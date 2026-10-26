import V185TrunkScan23Chunk0750

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4441363 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4]
def baseStart_4441363 : Nat := 118140960795 + 4441363 * 2 ^ 59
def prefixEnd_4441363 : Nat := 4983230072969 + 3 ^ 40 * 4441363 * 2
def baseEnd_4441363 : Nat := 2280553980094811880537049

theorem tailTrace_4441363 : CollatzResearch.WordTrace tailWord_4441363 prefixEnd_4441363 2280553980094811880537049 := by
  unfold tailWord_4441363
  simp only [CollatzResearch.WordTrace]
  refine ⟨161989816608707850256296743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107993211072471900170864495 161989816608707850256296743)
  ·
    refine ⟨242984724913061775384445115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161989816608707850256296743 242984724913061775384445115)
    ·
      refine ⟨364477087369592663076667673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242984724913061775384445115 364477087369592663076667673)
      ·
        refine ⟨273357815527194497307500755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364477087369592663076667673 273357815527194497307500755)
        ·
          refine ⟨410036723290791745961251133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273357815527194497307500755 410036723290791745961251133)
          ·
            refine ⟨153763771234046904735469175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410036723290791745961251133 153763771234046904735469175)
            ·
              refine ⟨230645656851070357103203763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153763771234046904735469175 230645656851070357103203763)
              ·
                refine ⟨345968485276605535654805645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230645656851070357103203763 345968485276605535654805645)
                ·
                  refine ⟨129738181978727075870552117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345968485276605535654805645 129738181978727075870552117)
                  ·
                    refine ⟨12162954560505663362864261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 129738181978727075870552117 12162954560505663362864261)
                    ·
                      refine ⟨2280553980094811880537049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12162954560505663362864261 2280553980094811880537049)
                      ·
                        rfl

theorem cell23_4441363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_4441363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441363 prefixEnd_4441363 := by exact prefixLift 4441363
  have htrace : WordTrace (prefixWord ++ tailWord_4441363) baseStart_4441363 baseEnd_4441363 := by
    simpa [prefixWord, tailWord_4441363, baseEnd_4441363] using wordTrace_append hprefix tailTrace_4441363
  have hstable : (prefixWord ++ tailWord_4441363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441363).length < 2 ^ (prefixWord ++ tailWord_4441363).sum := by decide
  have hdescent : baseEnd_4441363 < baseStart_4441363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441380 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4441380 : Nat := 118140960795 + 4441380 * 2 ^ 59
def prefixEnd_4441380 : Nat := 4983230072969 + 3 ^ 40 * 4441380 * 2
def baseEnd_4441380 : Nat := 2280562709265938314024471

theorem tailTrace_4441380 : CollatzResearch.WordTrace tailWord_4441380 prefixEnd_4441380 2280562709265938314024471 := by
  unfold tailWord_4441380
  simp only [CollatzResearch.WordTrace]
  refine ⟨80995218324823131079832797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107993624433097508106443729 80995218324823131079832797)
  ·
    refine ⟨30373206871808674154937299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80995218324823131079832797 30373206871808674154937299)
    ·
      refine ⟨45559810307713011232405949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30373206871808674154937299 45559810307713011232405949)
      ·
        refine ⟨17084928865392379212152231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45559810307713011232405949 17084928865392379212152231)
        ·
          refine ⟨25627393298088568818228347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17084928865392379212152231 25627393298088568818228347)
          ·
            refine ⟨38441089947132853227342521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25627393298088568818228347 38441089947132853227342521)
            ·
              refine ⟨28830817460349639920506891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38441089947132853227342521 28830817460349639920506891)
              ·
                refine ⟨43246226190524459880760337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28830817460349639920506891 43246226190524459880760337)
                ·
                  refine ⟨32434669642893344910570253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43246226190524459880760337 32434669642893344910570253)
                  ·
                    refine ⟨12163001116085004341463845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32434669642893344910570253 12163001116085004341463845)
                    ·
                      refine ⟨2280562709265938314024471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12163001116085004341463845 2280562709265938314024471)
                      ·
                        rfl

theorem cell23_4441380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4441380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441380 prefixEnd_4441380 := by exact prefixLift 4441380
  have htrace : WordTrace (prefixWord ++ tailWord_4441380) baseStart_4441380 baseEnd_4441380 := by
    simpa [prefixWord, tailWord_4441380, baseEnd_4441380] using wordTrace_append hprefix tailTrace_4441380
  have hstable : (prefixWord ++ tailWord_4441380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441380).length < 2 ^ (prefixWord ++ tailWord_4441380).sum := by decide
  have hdescent : baseEnd_4441380 < baseStart_4441380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441423 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_4441423 : Nat := 118140960795 + 4441423 * 2 ^ 59
def prefixEnd_4441423 : Nat := 4983230072969 + 3 ^ 40 * 4441423 * 2
def baseEnd_4441423 : Nat := 2280584788934081645786773

theorem tailTrace_4441423 : CollatzResearch.WordTrace tailWord_4441423 prefixEnd_4441423 2280584788934081645786773 := by
  unfold tailWord_4441423
  simp only [CollatzResearch.WordTrace]
  refine ⟨161992004988490480503480923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107994669992326987002320615 161992004988490480503480923)
  ·
    refine ⟨242988007482735720755221385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161992004988490480503480923 242988007482735720755221385)
    ·
      refine ⟨182241005612051790566416039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242988007482735720755221385 182241005612051790566416039)
      ·
        refine ⟨273361508418077685849624059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182241005612051790566416039 273361508418077685849624059)
        ·
          refine ⟨410042262627116528774436089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273361508418077685849624059 410042262627116528774436089)
          ·
            refine ⟨307531696970337396580827067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410042262627116528774436089 307531696970337396580827067)
            ·
              refine ⟨461297545455506094871240601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307531696970337396580827067 461297545455506094871240601)
              ·
                refine ⟨345973159091629571153430451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461297545455506094871240601 345973159091629571153430451)
                ·
                  refine ⟨518959738637444356730145677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345973159091629571153430451 518959738637444356730145677)
                  ·
                    refine ⟨194609901989041633773804629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518959738637444356730145677 194609901989041633773804629)
                    ·
                      refine ⟨2280584788934081645786773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194609901989041633773804629 2280584788934081645786773)
                      ·
                        rfl

theorem cell23_4441423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_4441423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441423 prefixEnd_4441423 := by exact prefixLift 4441423
  have htrace : WordTrace (prefixWord ++ tailWord_4441423) baseStart_4441423 baseEnd_4441423 := by
    simpa [prefixWord, tailWord_4441423, baseEnd_4441423] using wordTrace_append hprefix tailTrace_4441423
  have hstable : (prefixWord ++ tailWord_4441423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441423).length < 2 ^ (prefixWord ++ tailWord_4441423).sum := by decide
  have hdescent : baseEnd_4441423 < baseStart_4441423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441431 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 2, 2, 2]
def baseStart_4441431 : Nat := 118140960795 + 4441431 * 2 ^ 59
def prefixEnd_4441431 : Nat := 4983230072969 + 3 ^ 40 * 4441431 * 2
def baseEnd_4441431 : Nat := 2280588896779317614486737

theorem tailTrace_4441431 : CollatzResearch.WordTrace tailWord_4441431 prefixEnd_4441431 2280588896779317614486737 := by
  unfold tailWord_4441431
  simp only [CollatzResearch.WordTrace]
  refine ⟨161992296772461497869772147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107994864514974331913181431 161992296772461497869772147)
  ·
    refine ⟨242988445158692246804658221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161992296772461497869772147 242988445158692246804658221)
    ·
      refine ⟨91120666934509592551746833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242988445158692246804658221 91120666934509592551746833)
      ·
        refine ⟨68340500200882194413810125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91120666934509592551746833 68340500200882194413810125)
        ·
          refine ⟨25627687575330822905178797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68340500200882194413810125 25627687575330822905178797)
          ·
            refine ⟨9610382840749058589442049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25627687575330822905178797 9610382840749058589442049)
            ·
              refine ⟨7207787130561793942081537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9610382840749058589442049 7207787130561793942081537)
              ·
                refine ⟨5405840347921345456561153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7207787130561793942081537 5405840347921345456561153)
                ·
                  refine ⟨4054380260941009092420865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5405840347921345456561153 4054380260941009092420865)
                  ·
                    refine ⟨3040785195705756819315649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054380260941009092420865 3040785195705756819315649)
                    ·
                      refine ⟨2280588896779317614486737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040785195705756819315649 2280588896779317614486737)
                      ·
                        rfl

theorem cell23_4441431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_4441431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441431 prefixEnd_4441431 := by exact prefixLift 4441431
  have htrace : WordTrace (prefixWord ++ tailWord_4441431) baseStart_4441431 baseEnd_4441431 := by
    simpa [prefixWord, tailWord_4441431, baseEnd_4441431] using wordTrace_append hprefix tailTrace_4441431
  have hstable : (prefixWord ++ tailWord_4441431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441431).length < 2 ^ (prefixWord ++ tailWord_4441431).sum := by decide
  have hdescent : baseEnd_4441431 < baseStart_4441431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441454 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_4441454 : Nat := 118140960795 + 4441454 * 2 ^ 59
def prefixEnd_4441454 : Nat := 4983230072969 + 3 ^ 40 * 4441454 * 2
def baseEnd_4441454 : Nat := 253400078537152336055459

theorem tailTrace_4441454 : CollatzResearch.WordTrace tailWord_4441454 prefixEnd_4441454 253400078537152336055459 := by
  unfold tailWord_4441454
  simp only [CollatzResearch.WordTrace]
  refine ⟨20249141956422271599732427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107995423767585448531906277 20249141956422271599732427)
  ·
    refine ⟨30373712934633407399598641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20249141956422271599732427 30373712934633407399598641)
    ·
      refine ⟨22780284700975055549698981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30373712934633407399598641 22780284700975055549698981)
      ·
        refine ⟨4271303381432822915568559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22780284700975055549698981 4271303381432822915568559)
        ·
          refine ⟨6406955072149234373352839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271303381432822915568559 6406955072149234373352839)
          ·
            refine ⟨9610432608223851560029259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406955072149234373352839 9610432608223851560029259)
            ·
              refine ⟨14415648912335777340043889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9610432608223851560029259 14415648912335777340043889)
              ·
                refine ⟨10811736684251833005032917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14415648912335777340043889 10811736684251833005032917)
                ·
                  refine ⟨253400078537152336055459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10811736684251833005032917 253400078537152336055459)
                  ·
                    rfl

theorem cell23_4441454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_4441454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441454 prefixEnd_4441454 := by exact prefixLift 4441454
  have htrace : WordTrace (prefixWord ++ tailWord_4441454) baseStart_4441454 baseEnd_4441454 := by
    simpa [prefixWord, tailWord_4441454, baseEnd_4441454] using wordTrace_append hprefix tailTrace_4441454
  have hstable : (prefixWord ++ tailWord_4441454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441454).length < 2 ^ (prefixWord ++ tailWord_4441454).sum := by decide
  have hdescent : baseEnd_4441454 < baseStart_4441454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441497 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 3, 4]
def baseStart_4441497 : Nat := 118140960795 + 4441497 * 2 ^ 59
def prefixEnd_4441497 : Nat := 4983230072969 + 3 ^ 40 * 4441497 * 2
def baseEnd_4441497 : Nat := 760207595500838118753811

theorem tailTrace_4441497 : CollatzResearch.WordTrace tailWord_4441497 prefixEnd_4441497 760207595500838118753811 := by
  unfold tailWord_4441497
  simp only [CollatzResearch.WordTrace]
  refine ⟨161994703990222391141674745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107996469326814927427783163 161994703990222391141674745)
  ·
    refine ⟨121496027992666793356256059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161994703990222391141674745 121496027992666793356256059)
    ·
      refine ⟨182244041989000190034384089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121496027992666793356256059 182244041989000190034384089)
      ·
        refine ⟨136683031491750142525788067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182244041989000190034384089 136683031491750142525788067)
        ·
          refine ⟨205024547237625213788682101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136683031491750142525788067 205024547237625213788682101)
          ·
            refine ⟨19221051303527363792688947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 205024547237625213788682101 19221051303527363792688947)
            ·
              refine ⟨28831576955291045689033421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19221051303527363792688947 28831576955291045689033421)
              ·
                refine ⟨10811841358234142133387533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28831576955291045689033421 10811841358234142133387533)
                ·
                  refine ⟨4054440509337803300020325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10811841358234142133387533 4054440509337803300020325)
                  ·
                    refine ⟨760207595500838118753811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054440509337803300020325 760207595500838118753811)
                    ·
                      rfl

theorem cell23_4441497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_4441497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441497 prefixEnd_4441497 := by exact prefixLift 4441497
  have htrace : WordTrace (prefixWord ++ tailWord_4441497) baseStart_4441497 baseEnd_4441497 := by
    simpa [prefixWord, tailWord_4441497, baseEnd_4441497] using wordTrace_append hprefix tailTrace_4441497
  have hstable : (prefixWord ++ tailWord_4441497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441497).length < 2 ^ (prefixWord ++ tailWord_4441497).sum := by decide
  have hdescent : baseEnd_4441497 < baseStart_4441497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441548 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_4441548 : Nat := 118140960795 + 4441548 * 2 ^ 59
def prefixEnd_4441548 : Nat := 4983230072969 + 3 ^ 40 * 4441548 * 2
def baseEnd_4441548 : Nat := 760216324671964552241233

theorem tailTrace_4441548 : CollatzResearch.WordTrace tailWord_4441548 prefixEnd_4441548 760216324671964552241233 := by
  unfold tailWord_4441548
  simp only [CollatzResearch.WordTrace]
  refine ⟨80998282056518813425890649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107997709408691751234520865 80998282056518813425890649)
  ·
    refine ⟨60748711542389110069417987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80998282056518813425890649 60748711542389110069417987)
    ·
      refine ⟨91123067313583665104126981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60748711542389110069417987 91123067313583665104126981)
      ·
        refine ⟨17085575121296937207023809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91123067313583665104126981 17085575121296937207023809)
        ·
          refine ⟨12814181340972702905267857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17085575121296937207023809 12814181340972702905267857)
          ·
            refine ⟨9610636005729527178950893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12814181340972702905267857 9610636005729527178950893)
            ·
              refine ⟨3603988502148572692106585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9610636005729527178950893 3603988502148572692106585)
              ·
                refine ⟨2702991376611429519079939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603988502148572692106585 2702991376611429519079939)
                ·
                  refine ⟨4054487064917144278619909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702991376611429519079939 4054487064917144278619909)
                  ·
                    refine ⟨760216324671964552241233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054487064917144278619909 760216324671964552241233)
                    ·
                      rfl

theorem cell23_4441548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_4441548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441548 prefixEnd_4441548 := by exact prefixLift 4441548
  have htrace : WordTrace (prefixWord ++ tailWord_4441548) baseStart_4441548 baseEnd_4441548 := by
    simpa [prefixWord, tailWord_4441548, baseEnd_4441548] using wordTrace_append hprefix tailTrace_4441548
  have hstable : (prefixWord ++ tailWord_4441548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441548).length < 2 ^ (prefixWord ++ tailWord_4441548).sum := by decide
  have hdescent : baseEnd_4441548 < baseStart_4441548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441557 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_4441557 : Nat := 118140960795 + 4441557 * 2 ^ 59
def prefixEnd_4441557 : Nat := 4983230072969 + 3 ^ 40 * 4441557 * 2
def baseEnd_4441557 : Nat := 760217865113928040503719

theorem tailTrace_4441557 : CollatzResearch.WordTrace tailWord_4441557 prefixEnd_4441557 760217865113928040503719 := by
  unfold tailWord_4441557
  simp only [CollatzResearch.WordTrace]
  refine ⟨161996892370005021388858925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107997928246670014259239283 161996892370005021388858925)
  ·
    refine ⟨60748834638751883020822097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161996892370005021388858925 60748834638751883020822097)
    ·
      refine ⟨45561625979063912265616573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60748834638751883020822097 45561625979063912265616573)
      ·
        refine ⟨17085609742148967099606215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45561625979063912265616573 17085609742148967099606215)
        ·
          refine ⟨25628414613223450649409323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17085609742148967099606215 25628414613223450649409323)
          ·
            refine ⟨38442621919835175974113985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25628414613223450649409323 38442621919835175974113985)
            ·
              refine ⟨28831966439876381980585489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38442621919835175974113985 28831966439876381980585489)
              ·
                refine ⟨21623974829907286485439117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28831966439876381980585489 21623974829907286485439117)
                ·
                  refine ⟨8108990561215232432039669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21623974829907286485439117 8108990561215232432039669)
                  ·
                    refine ⟨760217865113928040503719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8108990561215232432039669 760217865113928040503719)
                    ·
                      rfl

theorem cell23_4441557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_4441557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441557 prefixEnd_4441557 := by exact prefixLift 4441557
  have htrace : WordTrace (prefixWord ++ tailWord_4441557) baseStart_4441557 baseEnd_4441557 := by
    simpa [prefixWord, tailWord_4441557, baseEnd_4441557] using wordTrace_append hprefix tailTrace_4441557
  have hstable : (prefixWord ++ tailWord_4441557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441557).length < 2 ^ (prefixWord ++ tailWord_4441557).sum := by decide
  have hdescent : baseEnd_4441557 < baseStart_4441557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441587 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 4, 4]
def baseStart_4441587 : Nat := 118140960795 + 4441587 * 2 ^ 59
def prefixEnd_4441587 : Nat := 4983230072969 + 3 ^ 40 * 4441587 * 2
def baseEnd_4441587 : Nat := 760222999920473001378673

theorem tailTrace_4441587 : CollatzResearch.WordTrace tailWord_4441587 prefixEnd_4441587 760222999920473001378673 := by
  unfold tailWord_4441587
  simp only [CollatzResearch.WordTrace]
  refine ⟨161997986559896336512451015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107998657706597557674967343 161997986559896336512451015)
  ·
    refine ⟨242996979839844504768676523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161997986559896336512451015 242996979839844504768676523)
    ·
      refine ⟨364495469759766757153014785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242996979839844504768676523 364495469759766757153014785)
      ·
        refine ⟨273371602319825067864761089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364495469759766757153014785 273371602319825067864761089)
        ·
          refine ⟨205028701739868800898570817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273371602319825067864761089 205028701739868800898570817)
          ·
            refine ⟨153771526304901600673928113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205028701739868800898570817 153771526304901600673928113)
            ·
              refine ⟨115328644728676200505446085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153771526304901600673928113 115328644728676200505446085)
              ·
                refine ⟨21624120886626787594771141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115328644728676200505446085 21624120886626787594771141)
                ·
                  refine ⟨4054522666242522674019589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21624120886626787594771141 4054522666242522674019589)
                  ·
                    refine ⟨760222999920473001378673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054522666242522674019589 760222999920473001378673)
                    ·
                      rfl

theorem cell23_4441587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4].length) (baseStart_4441587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441587 prefixEnd_4441587 := by exact prefixLift 4441587
  have htrace : WordTrace (prefixWord ++ tailWord_4441587) baseStart_4441587 baseEnd_4441587 := by
    simpa [prefixWord, tailWord_4441587, baseEnd_4441587] using wordTrace_append hprefix tailTrace_4441587
  have hstable : (prefixWord ++ tailWord_4441587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441587).length < 2 ^ (prefixWord ++ tailWord_4441587).sum := by decide
  have hdescent : baseEnd_4441587 < baseStart_4441587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441704 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4441704 : Nat := 118140960795 + 4441704 * 2 ^ 59
def prefixEnd_4441704 : Nat := 4983230072969 + 3 ^ 40 * 4441704 * 2
def baseEnd_4441704 : Nat := 2280729076997995046372981

theorem tailTrace_4441704 : CollatzResearch.WordTrace tailWord_4441704 prefixEnd_4441704 2280729076997995046372981 := by
  unfold tailWord_4441704
  simp only [CollatzResearch.WordTrace]
  refine ⟨81001126950236232747230083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108001502600314976996306777 81001126950236232747230083)
  ·
    refine ⟨121501690425354349120845125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81001126950236232747230083 121501690425354349120845125)
    ·
      refine ⟨22781566954753940460158461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121501690425354349120845125 22781566954753940460158461)
      ·
        refine ⟨8543087608032727672559423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22781566954753940460158461 8543087608032727672559423)
        ·
          refine ⟨12814631412049091508839135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8543087608032727672559423 12814631412049091508839135)
          ·
            refine ⟨19221947118073637263258703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12814631412049091508839135 19221947118073637263258703)
            ·
              refine ⟨28832920677110455894888055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19221947118073637263258703 28832920677110455894888055)
              ·
                refine ⟨43249381015665683842332083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28832920677110455894888055 43249381015665683842332083)
                ·
                  refine ⟨64874071523498525763498125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43249381015665683842332083 64874071523498525763498125)
                  ·
                    refine ⟨24327776821311947161311797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64874071523498525763498125 24327776821311947161311797)
                    ·
                      refine ⟨2280729076997995046372981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24327776821311947161311797 2280729076997995046372981)
                      ·
                        rfl

theorem cell23_4441704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4441704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441704 prefixEnd_4441704 := by exact prefixLift 4441704
  have htrace : WordTrace (prefixWord ++ tailWord_4441704) baseStart_4441704 baseEnd_4441704 := by
    simpa [prefixWord, tailWord_4441704, baseEnd_4441704] using wordTrace_append hprefix tailTrace_4441704
  have hstable : (prefixWord ++ tailWord_4441704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441704).length < 2 ^ (prefixWord ++ tailWord_4441704).sum := by decide
  have hdescent : baseEnd_4441704 < baseStart_4441704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441735 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_4441735 : Nat := 118140960795 + 4441735 * 2 ^ 59
def prefixEnd_4441735 : Nat := 4983230072969 + 3 ^ 40 * 4441735 * 2
def baseEnd_4441735 : Nat := 2280744994898284425085339

theorem tailTrace_4441735 : CollatzResearch.WordTrace tailWord_4441735 prefixEnd_4441735 2280744994898284425085339 := by
  unfold tailWord_4441735
  simp only [CollatzResearch.WordTrace]
  refine ⟨162003384563360157788838659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108002256375573438525892439 162003384563360157788838659)
  ·
    refine ⟨243005076845040236683257989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162003384563360157788838659 243005076845040236683257989)
    ·
      refine ⟨45563451908445044378110873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243005076845040236683257989 45563451908445044378110873)
      ·
        refine ⟨34172588931333783283583155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45563451908445044378110873 34172588931333783283583155)
        ·
          refine ⟨51258883397000674925374733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34172588931333783283583155 51258883397000674925374733)
          ·
            refine ⟨19222081273875253097015525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51258883397000674925374733 19222081273875253097015525)
            ·
              refine ⟨3604140238851609955690411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19222081273875253097015525 3604140238851609955690411)
              ·
                refine ⟨5406210358277414933535617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604140238851609955690411 5406210358277414933535617)
                ·
                  refine ⟨4054657768708061200151713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5406210358277414933535617 4054657768708061200151713)
                  ·
                    refine ⟨3040993326531045900113785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054657768708061200151713 3040993326531045900113785)
                    ·
                      refine ⟨2280744994898284425085339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040993326531045900113785 2280744994898284425085339)
                      ·
                        rfl

theorem cell23_4441735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_4441735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441735 prefixEnd_4441735 := by exact prefixLift 4441735
  have htrace : WordTrace (prefixWord ++ tailWord_4441735) baseStart_4441735 baseEnd_4441735 := by
    simpa [prefixWord, tailWord_4441735, baseEnd_4441735] using wordTrace_append hprefix tailTrace_4441735
  have hstable : (prefixWord ++ tailWord_4441735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441735).length < 2 ^ (prefixWord ++ tailWord_4441735).sum := by decide
  have hdescent : baseEnd_4441735 < baseStart_4441735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441737 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_4441737 : Nat := 118140960795 + 4441737 * 2 ^ 59
def prefixEnd_4441737 : Nat := 4983230072969 + 3 ^ 40 * 4441737 * 2
def baseEnd_4441737 : Nat := 760248673953197805753443

theorem tailTrace_4441737 : CollatzResearch.WordTrace tailWord_4441737 prefixEnd_4441737 760248673953197805753443 := by
  unfold tailWord_4441737
  simp only [CollatzResearch.WordTrace]
  refine ⟨162003457509352912130411465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108002305006235274753607643 162003457509352912130411465)
  ·
    refine ⟨121502593132014684097808599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162003457509352912130411465 121502593132014684097808599)
    ·
      refine ⟨182253889698022026146712899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121502593132014684097808599 182253889698022026146712899)
      ·
        refine ⟨273380834547033039220069349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182253889698022026146712899 273380834547033039220069349)
        ·
          refine ⟨51258906477568694853763003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273380834547033039220069349 51258906477568694853763003)
          ·
            refine ⟨76888359716353042280644505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51258906477568694853763003 76888359716353042280644505)
            ·
              refine ⟨57666269787264781710483379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76888359716353042280644505 57666269787264781710483379)
              ·
                refine ⟨86499404680897172565725069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57666269787264781710483379 86499404680897172565725069)
                ·
                  refine ⟨32437276755336439712146901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86499404680897172565725069 32437276755336439712146901)
                  ·
                    refine ⟨760248673953197805753443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32437276755336439712146901 760248673953197805753443)
                    ·
                      rfl

theorem cell23_4441737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_4441737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441737 prefixEnd_4441737 := by exact prefixLift 4441737
  have htrace : WordTrace (prefixWord ++ tailWord_4441737) baseStart_4441737 baseEnd_4441737 := by
    simpa [prefixWord, tailWord_4441737, baseEnd_4441737] using wordTrace_append hprefix tailTrace_4441737
  have hstable : (prefixWord ++ tailWord_4441737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441737).length < 2 ^ (prefixWord ++ tailWord_4441737).sum := by decide
  have hdescent : baseEnd_4441737 < baseStart_4441737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441747 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_4441747 : Nat := 118140960795 + 4441747 * 2 ^ 59
def prefixEnd_4441747 : Nat := 4983230072969 + 3 ^ 40 * 4441747 * 2
def baseEnd_4441747 : Nat := 2280751156666138378135283

theorem tailTrace_4441747 : CollatzResearch.WordTrace tailWord_4441747 prefixEnd_4441747 2280751156666138378135283 := by
  unfold tailWord_4441747
  simp only [CollatzResearch.WordTrace]
  refine ⟨162003822239316683838275495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108002548159544455892183663 162003822239316683838275495)
  ·
    refine ⟨243005733358975025757413243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162003822239316683838275495 243005733358975025757413243)
    ·
      refine ⟨364508600038462538636119865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243005733358975025757413243 364508600038462538636119865)
      ·
        refine ⟨273381450028846903977089899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364508600038462538636119865 273381450028846903977089899)
        ·
          refine ⟨410072175043270355965634849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273381450028846903977089899 410072175043270355965634849)
          ·
            refine ⟨307554131282452766974226137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410072175043270355965634849 307554131282452766974226137)
            ·
              refine ⟨230665598461839575230669603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307554131282452766974226137 230665598461839575230669603)
              ·
                refine ⟨345998397692759362846004405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230665598461839575230669603 345998397692759362846004405)
                ·
                  refine ⟨32437349783696190266812913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345998397692759362846004405 32437349783696190266812913)
                  ·
                    refine ⟨24328012337772142700109685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32437349783696190266812913 24328012337772142700109685)
                    ·
                      refine ⟨2280751156666138378135283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24328012337772142700109685 2280751156666138378135283)
                      ·
                        rfl

theorem cell23_4441747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_4441747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441747 prefixEnd_4441747 := by exact prefixLift 4441747
  have htrace : WordTrace (prefixWord ++ tailWord_4441747) baseStart_4441747 baseEnd_4441747 := by
    simpa [prefixWord, tailWord_4441747, baseEnd_4441747] using wordTrace_append hprefix tailTrace_4441747
  have hstable : (prefixWord ++ tailWord_4441747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441747).length < 2 ^ (prefixWord ++ tailWord_4441747).sum := by decide
  have hdescent : baseEnd_4441747 < baseStart_4441747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441764 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_4441764 : Nat := 118140960795 + 4441764 * 2 ^ 59
def prefixEnd_4441764 : Nat := 4983230072969 + 3 ^ 40 * 4441764 * 2
def baseEnd_4441764 : Nat := 2280759885837264811622705

theorem tailTrace_4441764 : CollatzResearch.WordTrace tailWord_4441764 prefixEnd_4441764 2280759885837264811622705 := by
  unfold tailWord_4441764
  simp only [CollatzResearch.WordTrace]
  refine ⟨81002221140127547870822173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108002961520170063827762897 81002221140127547870822173)
  ·
    refine ⟨30375832927547830451558315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81002221140127547870822173 30375832927547830451558315)
    ·
      refine ⟨45563749391321745677337473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30375832927547830451558315 45563749391321745677337473)
      ·
        refine ⟨34172812043491309258003105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45563749391321745677337473 34172812043491309258003105)
        ·
          refine ⟨25629609032618481943502329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34172812043491309258003105 25629609032618481943502329)
          ·
            refine ⟨19222206774463861457626747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25629609032618481943502329 19222206774463861457626747)
            ·
              refine ⟨28833310161695792186440121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19222206774463861457626747 28833310161695792186440121)
              ·
                refine ⟨21624982621271844139830091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28833310161695792186440121 21624982621271844139830091)
                ·
                  refine ⟨32437473931907766209745137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21624982621271844139830091 32437473931907766209745137)
                  ·
                    refine ⟨24328105448930824657308853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32437473931907766209745137 24328105448930824657308853)
                    ·
                      refine ⟨2280759885837264811622705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24328105448930824657308853 2280759885837264811622705)
                      ·
                        rfl

theorem cell23_4441764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_4441764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441764 prefixEnd_4441764 := by exact prefixLift 4441764
  have htrace : WordTrace (prefixWord ++ tailWord_4441764) baseStart_4441764 baseEnd_4441764 := by
    simpa [prefixWord, tailWord_4441764, baseEnd_4441764] using wordTrace_append hprefix tailTrace_4441764
  have hstable : (prefixWord ++ tailWord_4441764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441764).length < 2 ^ (prefixWord ++ tailWord_4441764).sum := by decide
  have hdescent : baseEnd_4441764 < baseStart_4441764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441784 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 7, 4]
def baseStart_4441784 : Nat := 118140960795 + 4441784 * 2 ^ 59
def prefixEnd_4441784 : Nat := 4983230072969 + 3 ^ 40 * 4441784 * 2
def baseEnd_4441784 : Nat := 760256718483451577790871

theorem tailTrace_4441784 : CollatzResearch.WordTrace tailWord_4441784 prefixEnd_4441784 760256718483451577790871 := by
  unfold tailWord_4441784
  simp only [CollatzResearch.WordTrace]
  refine ⟨81002585870091319578686203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108003447826788426104914937 81002585870091319578686203)
  ·
    refine ⟨121503878805136979368029305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81002585870091319578686203 121503878805136979368029305)
    ·
      refine ⟨91127909103852734526021979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121503878805136979368029305 91127909103852734526021979)
      ·
        refine ⟨136691863655779101789032969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91127909103852734526021979 136691863655779101789032969)
        ·
          refine ⟨102518897741834326341774727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136691863655779101789032969 102518897741834326341774727)
          ·
            refine ⟨153778346612751489512662091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102518897741834326341774727 153778346612751489512662091)
            ·
              refine ⟨230667519919127234268993137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153778346612751489512662091 230667519919127234268993137)
              ·
                refine ⟨173000639939345425701744853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230667519919127234268993137 173000639939345425701744853)
                ·
                  refine ⟨4054702498578408414884645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 173000639939345425701744853 4054702498578408414884645)
                  ·
                    refine ⟨760256718483451577790871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054702498578408414884645 760256718483451577790871)
                    ·
                      rfl

theorem cell23_4441784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_4441784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441784 prefixEnd_4441784 := by exact prefixLift 4441784
  have htrace : WordTrace (prefixWord ++ tailWord_4441784) baseStart_4441784 baseEnd_4441784 := by
    simpa [prefixWord, tailWord_4441784, baseEnd_4441784] using wordTrace_append hprefix tailTrace_4441784
  have hstable : (prefixWord ++ tailWord_4441784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441784).length < 2 ^ (prefixWord ++ tailWord_4441784).sum := by decide
  have hdescent : baseEnd_4441784 < baseStart_4441784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441791 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 2, 4, 2]
def baseStart_4441791 : Nat := 118140960795 + 4441791 * 2 ^ 59
def prefixEnd_4441791 : Nat := 4983230072969 + 3 ^ 40 * 4441791 * 2
def baseEnd_4441791 : Nat := 2280773749814936205985081

theorem tailTrace_4441791 : CollatzResearch.WordTrace tailWord_4441791 prefixEnd_4441791 2280773749814936205985081 := by
  unfold tailWord_4441791
  simp only [CollatzResearch.WordTrace]
  refine ⟨162005427051157279352877227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108003618034104852901918151 162005427051157279352877227)
  ·
    refine ⟨243008140576735919029315841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162005427051157279352877227 243008140576735919029315841)
    ·
      refine ⟨182256105432551939271986881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243008140576735919029315841 182256105432551939271986881)
      ·
        refine ⟨136692079074413954453990161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182256105432551939271986881 136692079074413954453990161)
        ·
          refine ⟨102519059305810465840492621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136692079074413954453990161 102519059305810465840492621)
          ·
            refine ⟨38444647239678924690184733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102519059305810465840492621 38444647239678924690184733)
            ·
              refine ⟨14416742714879596758819275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38444647239678924690184733 14416742714879596758819275)
              ·
                refine ⟨21625114072319395138228913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14416742714879596758819275 21625114072319395138228913)
                ·
                  refine ⟨16218835554239546353671685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21625114072319395138228913 16218835554239546353671685)
                  ·
                    refine ⟨3041031666419914941313441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16218835554239546353671685 3041031666419914941313441)
                    ·
                      refine ⟨2280773749814936205985081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041031666419914941313441 2280773749814936205985081)
                      ·
                        rfl

theorem cell23_4441791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_4441791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441791 prefixEnd_4441791 := by exact prefixLift 4441791
  have htrace : WordTrace (prefixWord ++ tailWord_4441791) baseStart_4441791 baseEnd_4441791 := by
    simpa [prefixWord, tailWord_4441791, baseEnd_4441791] using wordTrace_append hprefix tailTrace_4441791
  have hstable : (prefixWord ++ tailWord_4441791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441791).length < 2 ^ (prefixWord ++ tailWord_4441791).sum := by decide
  have hdescent : baseEnd_4441791 < baseStart_4441791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441805 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4441805 : Nat := 118140960795 + 4441805 * 2 ^ 59
def prefixEnd_4441805 : Nat := 4983230072969 + 3 ^ 40 * 4441805 * 2
def baseEnd_4441805 : Nat := 760260312848033050403339

theorem tailTrace_4441805 : CollatzResearch.WordTrace tailWord_4441805 prefixEnd_4441805 760260312848033050403339 := by
  unfold tailWord_4441805
  simp only [CollatzResearch.WordTrace]
  refine ⟨162005937673106559743886869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108003958448737706495924579 162005937673106559743886869)
  ·
    refine ⟨7594028328426869987994697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 162005937673106559743886869 7594028328426869987994697)
    ·
      refine ⟨5695521246320152490996023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7594028328426869987994697 5695521246320152490996023)
      ·
        refine ⟨8543281869480228736494035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5695521246320152490996023 8543281869480228736494035)
        ·
          refine ⟨12814922804220343104741053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8543281869480228736494035 12814922804220343104741053)
          ·
            refine ⟨4805596051582628664277895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12814922804220343104741053 4805596051582628664277895)
            ·
              refine ⟨7208394077373942996416843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805596051582628664277895 7208394077373942996416843)
              ·
                refine ⟨10812591116060914494625265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7208394077373942996416843 10812591116060914494625265)
                ·
                  refine ⟨8109443337045685870968949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10812591116060914494625265 8109443337045685870968949)
                  ·
                    refine ⟨760260312848033050403339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8109443337045685870968949 760260312848033050403339)
                    ·
                      rfl

theorem cell23_4441805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4441805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441805 prefixEnd_4441805 := by exact prefixLift 4441805
  have htrace : WordTrace (prefixWord ++ tailWord_4441805) baseStart_4441805 baseEnd_4441805 := by
    simpa [prefixWord, tailWord_4441805, baseEnd_4441805] using wordTrace_append hprefix tailTrace_4441805
  have hstable : (prefixWord ++ tailWord_4441805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441805).length < 2 ^ (prefixWord ++ tailWord_4441805).sum := by decide
  have hdescent : baseEnd_4441805 < baseStart_4441805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441818 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_4441818 : Nat := 118140960795 + 4441818 * 2 ^ 59
def prefixEnd_4441818 : Nat := 4983230072969 + 3 ^ 40 * 4441818 * 2
def baseEnd_4441818 : Nat := 760262537930869200115819

theorem tailTrace_4441818 : CollatzResearch.WordTrace tailWord_4441818 prefixEnd_4441818 760262537930869200115819 := by
  unfold tailWord_4441818
  simp only [CollatzResearch.WordTrace]
  refine ⟨40501602955514865741027527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108004274548039641976073405 40501602955514865741027527)
  ·
    refine ⟨60752404433272298611541291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40501602955514865741027527 60752404433272298611541291)
    ·
      refine ⟨91128606649908447917311937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60752404433272298611541291 91128606649908447917311937)
      ·
        refine ⟨68346454987431335937983953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91128606649908447917311937 68346454987431335937983953)
        ·
          refine ⟨51259841240573501953487965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68346454987431335937983953 51259841240573501953487965)
          ·
            refine ⟨19222440465215063232557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51259841240573501953487965 19222440465215063232557987)
            ·
              refine ⟨28833660697822594848836981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19222440465215063232557987 28833660697822594848836981)
              ·
                refine ⟨2703155690420868267078467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28833660697822594848836981 2703155690420868267078467)
                ·
                  refine ⟨4054733535631302400617701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703155690420868267078467 4054733535631302400617701)
                  ·
                    refine ⟨760262537930869200115819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054733535631302400617701 760262537930869200115819)
                    ·
                      rfl

theorem cell23_4441818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_4441818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441818 prefixEnd_4441818 := by exact prefixLift 4441818
  have htrace : WordTrace (prefixWord ++ tailWord_4441818) baseStart_4441818 baseEnd_4441818 := by
    simpa [prefixWord, tailWord_4441818, baseEnd_4441818] using wordTrace_append hprefix tailTrace_4441818
  have hstable : (prefixWord ++ tailWord_4441818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441818).length < 2 ^ (prefixWord ++ tailWord_4441818).sum := by decide
  have hdescent : baseEnd_4441818 < baseStart_4441818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441834 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_4441834 : Nat := 118140960795 + 4441834 * 2 ^ 59
def prefixEnd_4441834 : Nat := 4983230072969 + 3 ^ 40 * 4441834 * 2
def baseEnd_4441834 : Nat := 2280795829483079537747383

theorem tailTrace_4441834 : CollatzResearch.WordTrace tailWord_4441834 prefixEnd_4441834 2280795829483079537747383 := by
  unfold tailWord_4441834
  simp only [CollatzResearch.WordTrace]
  refine ⟨40501748847500374424173139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108004663593334331797795037 40501748847500374424173139)
  ·
    refine ⟨60752623271250561636259709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40501748847500374424173139 60752623271250561636259709)
    ·
      refine ⟨22782233726718960613597391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60752623271250561636259709 22782233726718960613597391)
      ·
        refine ⟨34173350590078440920396087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22782233726718960613597391 34173350590078440920396087)
        ·
          refine ⟨51260025885117661380594131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34173350590078440920396087 51260025885117661380594131)
          ·
            refine ⟨76890038827676492070891197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51260025885117661380594131 76890038827676492070891197)
            ·
              refine ⟨28833764560378684526584199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76890038827676492070891197 28833764560378684526584199)
              ·
                refine ⟨43250646840568026789876299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28833764560378684526584199 43250646840568026789876299)
                ·
                  refine ⟨64875970260852040184814449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43250646840568026789876299 64875970260852040184814449)
                  ·
                    refine ⟨48656977695639030138610837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64875970260852040184814449 48656977695639030138610837)
                    ·
                      refine ⟨2280795829483079537747383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48656977695639030138610837 2280795829483079537747383)
                      ·
                        rfl

theorem cell23_4441834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_4441834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441834 prefixEnd_4441834 := by exact prefixLift 4441834
  have htrace : WordTrace (prefixWord ++ tailWord_4441834) baseStart_4441834 baseEnd_4441834 := by
    simpa [prefixWord, tailWord_4441834, baseEnd_4441834] using wordTrace_append hprefix tailTrace_4441834
  have hstable : (prefixWord ++ tailWord_4441834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441834).length < 2 ^ (prefixWord ++ tailWord_4441834).sum := by decide
  have hdescent : baseEnd_4441834 < baseStart_4441834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441851 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 6, 3, 2]
def baseStart_4441851 : Nat := 118140960795 + 4441851 * 2 ^ 59
def prefixEnd_4441851 : Nat := 4983230072969 + 3 ^ 40 * 4441851 * 2
def baseEnd_4441851 : Nat := 2280804558654205971234805

theorem tailTrace_4441851 : CollatzResearch.WordTrace tailWord_4441851 prefixEnd_4441851 2280804558654205971234805 := by
  unfold tailWord_4441851
  simp only [CollatzResearch.WordTrace]
  refine ⟨162007615430939909600061407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108005076953959939733374271 162007615430939909600061407)
  ·
    refine ⟨243011423146409864400092111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162007615430939909600061407 243011423146409864400092111)
    ·
      refine ⟨364517134719614796600138167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243011423146409864400092111 364517134719614796600138167)
      ·
        refine ⟨546775702079422194900207251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364517134719614796600138167 546775702079422194900207251)
        ·
          refine ⟨820163553119133292350310877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546775702079422194900207251 820163553119133292350310877)
          ·
            refine ⟨307561332419674984631366579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 820163553119133292350310877 307561332419674984631366579)
            ·
              refine ⟨461341998629512476947049869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307561332419674984631366579 461341998629512476947049869)
              ·
                refine ⟨173003249486067178855143701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461341998629512476947049869 173003249486067178855143701)
                ·
                  refine ⟨8109527319659399008834861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 173003249486067178855143701 8109527319659399008834861)
                  ·
                    refine ⟨3041072744872274628313073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8109527319659399008834861 3041072744872274628313073)
                    ·
                      refine ⟨2280804558654205971234805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041072744872274628313073 2280804558654205971234805)
                      ·
                        rfl

theorem cell23_4441851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3, 2].length) (baseStart_4441851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441851 prefixEnd_4441851 := by exact prefixLift 4441851
  have htrace : WordTrace (prefixWord ++ tailWord_4441851) baseStart_4441851 baseEnd_4441851 := by
    simpa [prefixWord, tailWord_4441851, baseEnd_4441851] using wordTrace_append hprefix tailTrace_4441851
  have hstable : (prefixWord ++ tailWord_4441851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441851).length < 2 ^ (prefixWord ++ tailWord_4441851).sum := by decide
  have hdescent : baseEnd_4441851 < baseStart_4441851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441886 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4441886 : Nat := 118140960795 + 4441886 * 2 ^ 59
def prefixEnd_4441886 : Nat := 4983230072969 + 3 ^ 40 * 4441886 * 2
def baseEnd_4441886 : Nat := 760274176825704444765715

theorem tailTrace_4441886 : CollatzResearch.WordTrace tailWord_4441886 prefixEnd_4441886 760274176825704444765715 := by
  unfold tailWord_4441886
  simp only [CollatzResearch.WordTrace]
  refine ⟨20251111498226638822198189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108005927990542073718390341 20251111498226638822198189)
  ·
    refine ⟨7594166811834989558324321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20251111498226638822198189 7594166811834989558324321)
    ·
      refine ⟨5695625108876242168743241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7594166811834989558324321 5695625108876242168743241)
      ·
        refine ⟨4271718831657181626557431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5695625108876242168743241 4271718831657181626557431)
        ·
          refine ⟨6407578247485772439836147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271718831657181626557431 6407578247485772439836147)
          ·
            refine ⟨9611367371228658659754221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6407578247485772439836147 9611367371228658659754221)
            ·
              refine ⟨3604262764210746997407833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9611367371228658659754221 3604262764210746997407833)
              ·
                refine ⟨2703197073158060248055875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3604262764210746997407833 2703197073158060248055875)
                ·
                  refine ⟨4054795609737090372083813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703197073158060248055875 4054795609737090372083813)
                  ·
                    refine ⟨760274176825704444765715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054795609737090372083813 760274176825704444765715)
                    ·
                      rfl

theorem cell23_4441886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4441886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441886 prefixEnd_4441886 := by exact prefixLift 4441886
  have htrace : WordTrace (prefixWord ++ tailWord_4441886) baseStart_4441886 baseEnd_4441886 := by
    simpa [prefixWord, tailWord_4441886, baseEnd_4441886] using wordTrace_append hprefix tailTrace_4441886
  have hstable : (prefixWord ++ tailWord_4441886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441886).length < 2 ^ (prefixWord ++ tailWord_4441886).sum := by decide
  have hdescent : baseEnd_4441886 < baseStart_4441886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441891 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 4, 4]
def baseStart_4441891 : Nat := 118140960795 + 4441891 * 2 ^ 59
def prefixEnd_4441891 : Nat := 4983230072969 + 3 ^ 40 * 4441891 * 2
def baseEnd_4441891 : Nat := 760275032626795271578207

theorem tailTrace_4441891 : CollatzResearch.WordTrace tailWord_4441891 prefixEnd_4441891 760275032626795271578207 := by
  unfold tailWord_4441891
  simp only [CollatzResearch.WordTrace]
  refine ⟨162009074350794996431517527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108006049567196664287678351 162009074350794996431517527)
  ·
    refine ⟨243013611526192494647276291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162009074350794996431517527 243013611526192494647276291)
    ·
      refine ⟨364520417289288741970914437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243013611526192494647276291 364520417289288741970914437)
      ·
        refine ⟨68347578241741639119546457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 364520417289288741970914437 68347578241741639119546457)
        ·
          refine ⟨51260683681306229339659843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68347578241741639119546457 51260683681306229339659843)
          ·
            refine ⟨76891025521959344009489765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51260683681306229339659843 76891025521959344009489765)
            ·
              refine ⟨14417067285367377001779331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76891025521959344009489765 14417067285367377001779331)
              ·
                refine ⟨21625600928051065502668997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14417067285367377001779331 21625600928051065502668997)
                ·
                  refine ⟨4054800174009574781750437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21625600928051065502668997 4054800174009574781750437)
                  ·
                    refine ⟨760275032626795271578207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054800174009574781750437 760275032626795271578207)
                    ·
                      rfl

theorem cell23_4441891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 4].length) (baseStart_4441891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441891 prefixEnd_4441891 := by exact prefixLift 4441891
  have htrace : WordTrace (prefixWord ++ tailWord_4441891) baseStart_4441891 baseEnd_4441891 := by
    simpa [prefixWord, tailWord_4441891, baseEnd_4441891] using wordTrace_append hprefix tailTrace_4441891
  have hstable : (prefixWord ++ tailWord_4441891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441891).length < 2 ^ (prefixWord ++ tailWord_4441891).sum := by decide
  have hdescent : baseEnd_4441891 < baseStart_4441891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441944 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4441944 : Nat := 118140960795 + 4441944 * 2 ^ 59
def prefixEnd_4441944 : Nat := 4983230072969 + 3 ^ 40 * 4441944 * 2
def baseEnd_4441944 : Nat := 2280852312355074107371877

theorem tailTrace_4441944 : CollatzResearch.WordTrace tailWord_4441944 prefixEnd_4441944 2280852312355074107371877 := by
  unfold tailWord_4441944
  simp only [CollatzResearch.WordTrace]
  refine ⟨81005503709801493241598443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108007338279735324322131257 81005503709801493241598443)
  ·
    refine ⟨121508255564702239862397665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81005503709801493241598443 121508255564702239862397665)
    ·
      refine ⟨91131191673526679896798249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121508255564702239862397665 91131191673526679896798249)
      ·
        refine ⟨68348393755145009922598687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91131191673526679896798249 68348393755145009922598687)
        ·
          refine ⟨102522590632717514883898031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68348393755145009922598687 102522590632717514883898031)
          ·
            refine ⟨153783885949076272325847047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102522590632717514883898031 153783885949076272325847047)
            ·
              refine ⟨230675828923614408488770571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153783885949076272325847047 230675828923614408488770571)
              ·
                refine ⟨346013743385421612733155857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230675828923614408488770571 346013743385421612733155857)
                ·
                  refine ⟨259510307539066209549866893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346013743385421612733155857 259510307539066209549866893)
                  ·
                    refine ⟨97316365327149828581200085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259510307539066209549866893 97316365327149828581200085)
                    ·
                      refine ⟨2280852312355074107371877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97316365327149828581200085 2280852312355074107371877)
                      ·
                        rfl

theorem cell23_4441944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4441944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441944 prefixEnd_4441944 := by exact prefixLift 4441944
  have htrace : WordTrace (prefixWord ++ tailWord_4441944) baseStart_4441944 baseEnd_4441944 := by
    simpa [prefixWord, tailWord_4441944, baseEnd_4441944] using wordTrace_append hprefix tailTrace_4441944
  have hstable : (prefixWord ++ tailWord_4441944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441944).length < 2 ^ (prefixWord ++ tailWord_4441944).sum := by decide
  have hdescent : baseEnd_4441944 < baseStart_4441944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441965 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4441965 : Nat := 118140960795 + 4441965 * 2 ^ 59
def prefixEnd_4441965 : Nat := 4983230072969 + 3 ^ 40 * 4441965 * 2
def baseEnd_4441965 : Nat := 2280863095448818525209281

theorem tailTrace_4441965 : CollatzResearch.WordTrace tailWord_4441965 prefixEnd_4441965 2280863095448818525209281 := by
  unfold tailWord_4441965
  simp only [CollatzResearch.WordTrace]
  refine ⟨162011773352526907069711349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108007848901684604713140899 162011773352526907069711349)
  ·
    refine ⟨15188603751799397537785439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162011773352526907069711349 15188603751799397537785439)
    ·
      refine ⟨22782905627699096306678159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15188603751799397537785439 22782905627699096306678159)
      ·
        refine ⟨34174358441548644460017239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22782905627699096306678159 34174358441548644460017239)
        ·
          refine ⟨51261537662322966690025859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34174358441548644460017239 51261537662322966690025859)
          ·
            refine ⟨76892306493484450035038789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51261537662322966690025859 76892306493484450035038789)
            ·
              refine ⟨14417307467528334381569773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76892306493484450035038789 14417307467528334381569773)
              ·
                refine ⟨5406490300323125393088665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14417307467528334381569773 5406490300323125393088665)
                ·
                  refine ⟨4054867725242344044816499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5406490300323125393088665 4054867725242344044816499)
                  ·
                    refine ⟨6082301587863516067224749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4054867725242344044816499 6082301587863516067224749)
                    ·
                      refine ⟨2280863095448818525209281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6082301587863516067224749 2280863095448818525209281)
                      ·
                        rfl

theorem cell23_4441965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4441965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441965 prefixEnd_4441965 := by exact prefixLift 4441965
  have htrace : WordTrace (prefixWord ++ tailWord_4441965) baseStart_4441965 baseEnd_4441965 := by
    simpa [prefixWord, tailWord_4441965, baseEnd_4441965] using wordTrace_append hprefix tailTrace_4441965
  have hstable : (prefixWord ++ tailWord_4441965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441965).length < 2 ^ (prefixWord ++ tailWord_4441965).sum := by decide
  have hdescent : baseEnd_4441965 < baseStart_4441965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441992 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_4441992 : Nat := 118140960795 + 4441992 * 2 ^ 59
def prefixEnd_4441992 : Nat := 4983230072969 + 3 ^ 40 * 4441992 * 2
def baseEnd_4441992 : Nat := 2280876959426489919571657

theorem tailTrace_4441992 : CollatzResearch.WordTrace tailWord_4441992 prefixEnd_4441992 2280876959426489919571657 := by
  unfold tailWord_4441992
  simp only [CollatzResearch.WordTrace]
  refine ⟨81006379061714545340472115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108008505415619393787296153 81006379061714545340472115)
  ·
    refine ⟨121509568592571818010708173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81006379061714545340472115 121509568592571818010708173)
    ·
      refine ⟨45566088222214431754015565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121509568592571818010708173 45566088222214431754015565)
      ·
        refine ⟨17087283083330411907755837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45566088222214431754015565 17087283083330411907755837)
        ·
          refine ⟨6407731156248904465408439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17087283083330411907755837 6407731156248904465408439)
          ·
            refine ⟨9611596734373356698112659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6407731156248904465408439 9611596734373356698112659)
            ·
              refine ⟨14417395101560035047168989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9611596734373356698112659 14417395101560035047168989)
              ·
                refine ⟨5406523163085013142688371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14417395101560035047168989 5406523163085013142688371)
                ·
                  refine ⟨8109784744627519714032557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5406523163085013142688371 8109784744627519714032557)
                  ·
                    refine ⟨3041169279235319892762209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8109784744627519714032557 3041169279235319892762209)
                    ·
                      refine ⟨2280876959426489919571657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041169279235319892762209 2280876959426489919571657)
                      ·
                        rfl

theorem cell23_4441992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_4441992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441992 prefixEnd_4441992 := by exact prefixLift 4441992
  have htrace : WordTrace (prefixWord ++ tailWord_4441992) baseStart_4441992 baseEnd_4441992 := by
    simpa [prefixWord, tailWord_4441992, baseEnd_4441992] using wordTrace_append hprefix tailTrace_4441992
  have hstable : (prefixWord ++ tailWord_4441992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441992).length < 2 ^ (prefixWord ++ tailWord_4441992).sum := by decide
  have hdescent : baseEnd_4441992 < baseStart_4441992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442001 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_4442001 : Nat := 118140960795 + 4442001 * 2 ^ 59
def prefixEnd_4442001 : Nat := 4983230072969 + 3 ^ 40 * 4442001 * 2
def baseEnd_4442001 : Nat := 2280881580752380384359115

theorem tailTrace_4442001 : CollatzResearch.WordTrace tailWord_4442001 prefixEnd_4442001 2280881580752380384359115 := by
  unfold tailWord_4442001
  simp only [CollatzResearch.WordTrace]
  refine ⟨162013086380396485218021857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108008724253597656812014571 162013086380396485218021857)
  ·
    refine ⟨121509814785297363913516393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162013086380396485218021857 121509814785297363913516393)
    ·
      refine ⟨91132361088973022935137295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121509814785297363913516393 91132361088973022935137295)
      ·
        refine ⟨136698541633459534402705943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91132361088973022935137295 136698541633459534402705943)
        ·
          refine ⟨205047812450189301604058915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136698541633459534402705943 205047812450189301604058915)
          ·
            refine ⟨307571718675283952406088373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205047812450189301604058915 307571718675283952406088373)
            ·
              refine ⟨28834848625807870538070785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 307571718675283952406088373 28834848625807870538070785)
              ·
                refine ⟨21626136469355902903553089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28834848625807870538070785 21626136469355902903553089)
                ·
                  refine ⟨16219602352016927177664817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21626136469355902903553089 16219602352016927177664817)
                  ·
                    refine ⟨12164701764012695383248613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16219602352016927177664817 12164701764012695383248613)
                    ·
                      refine ⟨2280881580752380384359115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12164701764012695383248613 2280881580752380384359115)
                      ·
                        rfl

theorem cell23_4442001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_4442001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442001 prefixEnd_4442001 := by exact prefixLift 4442001
  have htrace : WordTrace (prefixWord ++ tailWord_4442001) baseStart_4442001 baseEnd_4442001 := by
    simpa [prefixWord, tailWord_4442001, baseEnd_4442001] using wordTrace_append hprefix tailTrace_4442001
  have hstable : (prefixWord ++ tailWord_4442001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442001).length < 2 ^ (prefixWord ++ tailWord_4442001).sum := by decide
  have hdescent : baseEnd_4442001 < baseStart_4442001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442005 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_4442005 : Nat := 118140960795 + 4442005 * 2 ^ 59
def prefixEnd_4442005 : Nat := 4983230072969 + 3 ^ 40 * 4442005 * 2
def baseEnd_4442005 : Nat := 2280883634674998368709097

theorem tailTrace_4442005 : CollatzResearch.WordTrace tailWord_4442005 prefixEnd_4442005 2280883634674998368709097 := by
  unfold tailWord_4442005
  simp only [CollatzResearch.WordTrace]
  refine ⟨162013232272381993901167469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108008821514921329267444979 162013232272381993901167469)
  ·
    refine ⟨60754962102143247712937801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162013232272381993901167469 60754962102143247712937801)
    ·
      refine ⟨45566221576607435784703351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60754962102143247712937801 45566221576607435784703351)
      ·
        refine ⟨68349332364911153677055027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45566221576607435784703351 68349332364911153677055027)
        ·
          refine ⟨102523998547366730515582541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68349332364911153677055027 102523998547366730515582541)
          ·
            refine ⟨38446499455262523943343453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102523998547366730515582541 38446499455262523943343453)
            ·
              refine ⟨14417437295723446478753795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38446499455262523943343453 14417437295723446478753795)
              ·
                refine ⟨21626155943585169718130693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14417437295723446478753795 21626155943585169718130693)
                ·
                  refine ⟨4054904239422219322149505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21626155943585169718130693 4054904239422219322149505)
                  ·
                    refine ⟨3041178179566664491612129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054904239422219322149505 3041178179566664491612129)
                    ·
                      refine ⟨2280883634674998368709097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041178179566664491612129 2280883634674998368709097)
                      ·
                        rfl

theorem cell23_4442005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_4442005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442005 prefixEnd_4442005 := by exact prefixLift 4442005
  have htrace : WordTrace (prefixWord ++ tailWord_4442005) baseStart_4442005 baseEnd_4442005 := by
    simpa [prefixWord, tailWord_4442005, baseEnd_4442005] using wordTrace_append hprefix tailTrace_4442005
  have hstable : (prefixWord ++ tailWord_4442005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442005).length < 2 ^ (prefixWord ++ tailWord_4442005).sum := by decide
  have hdescent : baseEnd_4442005 < baseStart_4442005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442041 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_4442041 : Nat := 118140960795 + 4442041 * 2 ^ 59
def prefixEnd_4442041 : Nat := 4983230072969 + 3 ^ 40 * 4442041 * 2
def baseEnd_4442041 : Nat := 760300706659520075952977

theorem tailTrace_4442041 : CollatzResearch.WordTrace tailWord_4442041 prefixEnd_4442041 760300706659520075952977 := by
  unfold tailWord_4442041
  simp only [CollatzResearch.WordTrace]
  refine ⟨162014545300251572049477977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108009696866834381366318651 162014545300251572049477977)
  ·
    refine ⟨121510908975188679037108483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162014545300251572049477977 121510908975188679037108483)
    ·
      refine ⟨182266363462783018555662725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121510908975188679037108483 182266363462783018555662725)
      ·
        refine ⟨34174943149271815979186761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182266363462783018555662725 34174943149271815979186761)
        ·
          refine ⟨25631207361953861984390071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34174943149271815979186761 25631207361953861984390071)
          ·
            refine ⟨38446811042930792976585107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25631207361953861984390071 38446811042930792976585107)
            ·
              refine ⟨57670216564396189464877661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38446811042930792976585107 57670216564396189464877661)
              ·
                refine ⟨21626331211648571049329123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57670216564396189464877661 21626331211648571049329123)
                ·
                  refine ⟨32439496817472856573993685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21626331211648571049329123 32439496817472856573993685)
                  ·
                    refine ⟨760300706659520075952977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32439496817472856573993685 760300706659520075952977)
                    ·
                      rfl

theorem cell23_4442041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_4442041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442041 prefixEnd_4442041 := by exact prefixLift 4442041
  have htrace : WordTrace (prefixWord ++ tailWord_4442041) baseStart_4442041 baseEnd_4442041 := by
    simpa [prefixWord, tailWord_4442041, baseEnd_4442041] using wordTrace_append hprefix tailTrace_4442041
  have hstable : (prefixWord ++ tailWord_4442041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442041).length < 2 ^ (prefixWord ++ tailWord_4442041).sum := by decide
  have hdescent : baseEnd_4442041 < baseStart_4442041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442045 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 5]
def baseStart_4442045 : Nat := 118140960795 + 4442045 * 2 ^ 59
def prefixEnd_4442045 : Nat := 4983230072969 + 3 ^ 40 * 4442045 * 2
def baseEnd_4442045 : Nat := 253433797100130912467657

theorem tailTrace_4442045 : CollatzResearch.WordTrace tailWord_4442045 prefixEnd_4442045 253433797100130912467657 := by
  unfold tailWord_4442045
  simp only [CollatzResearch.WordTrace]
  refine ⟨162014691192237080732623589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108009794128158053821749059 162014691192237080732623589)
  ·
    refine ⟨30377754598544452637366923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162014691192237080732623589 30377754598544452637366923)
    ·
      refine ⟨45566631897816678956050385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30377754598544452637366923 45566631897816678956050385)
      ·
        refine ⟨34174973923362509217037789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45566631897816678956050385 34174973923362509217037789)
        ·
          refine ⟨12815615221260940956389171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34174973923362509217037789 12815615221260940956389171)
          ·
            refine ⟨19223422831891411434583757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12815615221260940956389171 19223422831891411434583757)
            ·
              refine ⟨7208783561959279287968909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19223422831891411434583757 7208783561959279287968909)
              ·
                refine ⟨2703293835734729732988341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7208783561959279287968909 2703293835734729732988341)
                ·
                  refine ⟨253433797100130912467657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2703293835734729732988341 253433797100130912467657)
                  ·
                    rfl

theorem cell23_4442045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_4442045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442045 prefixEnd_4442045 := by exact prefixLift 4442045
  have htrace : WordTrace (prefixWord ++ tailWord_4442045) baseStart_4442045 baseEnd_4442045 := by
    simpa [prefixWord, tailWord_4442045, baseEnd_4442045] using wordTrace_append hprefix tailTrace_4442045
  have hstable : (prefixWord ++ tailWord_4442045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442045).length < 2 ^ (prefixWord ++ tailWord_4442045).sum := by decide
  have hdescent : baseEnd_4442045 < baseStart_4442045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442068 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4442068 : Nat := 118140960795 + 4442068 * 2 ^ 59
def prefixEnd_4442068 : Nat := 4983230072969 + 3 ^ 40 * 4442068 * 2
def baseEnd_4442068 : Nat := 2280915983956231622221307

theorem tailTrace_4442068 : CollatzResearch.WordTrace tailWord_4442068 prefixEnd_4442068 2280915983956231622221307 := by
  unfold tailWord_4442068
  simp only [CollatzResearch.WordTrace]
  refine ⟨81007765035576877830355429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108010353380769170440473905 81007765035576877830355429)
  ·
    refine ⟨15188955944170664593191643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81007765035576877830355429 15188955944170664593191643)
    ·
      refine ⟨22783433916255996889787465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15188955944170664593191643 22783433916255996889787465)
      ·
        refine ⟨17087575437191997667340599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22783433916255996889787465 17087575437191997667340599)
        ·
          refine ⟨25631363155787996501010899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17087575437191997667340599 25631363155787996501010899)
          ·
            refine ⟨38447044733681994751516349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25631363155787996501010899 38447044733681994751516349)
            ·
              refine ⟨14417641775130748031818631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38447044733681994751516349 14417641775130748031818631)
              ·
                refine ⟨21626462662696122047727947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14417641775130748031818631 21626462662696122047727947)
                ·
                  refine ⟨32439693994044183071591921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21626462662696122047727947 32439693994044183071591921)
                  ·
                    refine ⟨24329770495533137303693941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32439693994044183071591921 24329770495533137303693941)
                    ·
                      refine ⟨2280915983956231622221307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24329770495533137303693941 2280915983956231622221307)
                      ·
                        rfl

theorem cell23_4442068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4442068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442068 prefixEnd_4442068 := by exact prefixLift 4442068
  have htrace : WordTrace (prefixWord ++ tailWord_4442068) baseStart_4442068 baseEnd_4442068 := by
    simpa [prefixWord, tailWord_4442068, baseEnd_4442068] using wordTrace_append hprefix tailTrace_4442068
  have hstable : (prefixWord ++ tailWord_4442068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442068).length < 2 ^ (prefixWord ++ tailWord_4442068).sum := by decide
  have hdescent : baseEnd_4442068 < baseStart_4442068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442088 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 5, 4]
def baseStart_4442088 : Nat := 118140960795 + 4442088 * 2 ^ 59
def prefixEnd_4442088 : Nat := 4983230072969 + 3 ^ 40 * 4442088 * 2
def baseEnd_4442088 : Nat := 760308751189773847990405

theorem tailTrace_4442088 : CollatzResearch.WordTrace tailWord_4442088 prefixEnd_4442088 760308751189773847990405 := by
  unfold tailWord_4442088
  simp only [CollatzResearch.WordTrace]
  refine ⟨81008129765540649538219459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108010839687387532717625945 81008129765540649538219459)
  ·
    refine ⟨121512194648310974307329189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81008129765540649538219459 121512194648310974307329189)
    ·
      refine ⟨22783536496558307682624223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121512194648310974307329189 22783536496558307682624223)
      ·
        refine ⟨34175304744837461523936335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22783536496558307682624223 34175304744837461523936335)
        ·
          refine ⟨51262957117256192285904503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34175304744837461523936335 51262957117256192285904503)
          ·
            refine ⟨76894435675884288428856755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51262957117256192285904503 76894435675884288428856755)
            ·
              refine ⟨115341653513826432643285133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76894435675884288428856755 115341653513826432643285133)
              ·
                refine ⟨43253120067684912241231925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115341653513826432643285133 43253120067684912241231925)
                ·
                  refine ⟨4054980006345460522615493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43253120067684912241231925 4054980006345460522615493)
                  ·
                    refine ⟨760308751189773847990405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054980006345460522615493 760308751189773847990405)
                    ·
                      rfl

theorem cell23_4442088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_4442088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442088 prefixEnd_4442088 := by exact prefixLift 4442088
  have htrace : WordTrace (prefixWord ++ tailWord_4442088) baseStart_4442088 baseEnd_4442088 := by
    simpa [prefixWord, tailWord_4442088, baseEnd_4442088] using wordTrace_append hprefix tailTrace_4442088
  have hstable : (prefixWord ++ tailWord_4442088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442088).length < 2 ^ (prefixWord ++ tailWord_4442088).sum := by decide
  have hdescent : baseEnd_4442088 < baseStart_4442088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442091 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4]
def baseStart_4442091 : Nat := 118140960795 + 4442091 * 2 ^ 59
def prefixEnd_4442091 : Nat := 4983230072969 + 3 ^ 40 * 4442091 * 2
def baseEnd_4442091 : Nat := 2280927794011285032233701

theorem tailTrace_4442091 : CollatzResearch.WordTrace tailWord_4442091 prefixEnd_4442091 2280927794011285032233701 := by
  unfold tailWord_4442091
  simp only [CollatzResearch.WordTrace]
  refine ⟨162016368950070430588798127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108010912633380287059198751 162016368950070430588798127)
  ·
    refine ⟨243024553425105645883197191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162016368950070430588798127 243024553425105645883197191)
    ·
      refine ⟨364536830137658468824795787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243024553425105645883197191 364536830137658468824795787)
      ·
        refine ⟨546805245206487703237193681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364536830137658468824795787 546805245206487703237193681)
        ·
          refine ⟨410103933904865777427895261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546805245206487703237193681 410103933904865777427895261)
          ·
            refine ⟨153788975214324666535460723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410103933904865777427895261 153788975214324666535460723)
            ·
              refine ⟨230683462821486999803191085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153788975214324666535460723 230683462821486999803191085)
              ·
                refine ⟨86506298558057624926196657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230683462821486999803191085 86506298558057624926196657)
                ·
                  refine ⟨64879723918543218694647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86506298558057624926196657 64879723918543218694647493)
                  ·
                    refine ⟨12164948234726853505246405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64879723918543218694647493 12164948234726853505246405)
                    ·
                      refine ⟨2280927794011285032233701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12164948234726853505246405 2280927794011285032233701)
                      ·
                        rfl

theorem cell23_4442091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_4442091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442091 prefixEnd_4442091 := by exact prefixLift 4442091
  have htrace : WordTrace (prefixWord ++ tailWord_4442091) baseStart_4442091 baseEnd_4442091 := by
    simpa [prefixWord, tailWord_4442091, baseEnd_4442091] using wordTrace_append hprefix tailTrace_4442091
  have hstable : (prefixWord ++ tailWord_4442091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442091).length < 2 ^ (prefixWord ++ tailWord_4442091).sum := by decide
  have hdescent : baseEnd_4442091 < baseStart_4442091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442155 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 2, 3, 2]
def baseStart_4442155 : Nat := 118140960795 + 4442155 * 2 ^ 59
def prefixEnd_4442155 : Nat := 4983230072969 + 3 ^ 40 * 4442155 * 2
def baseEnd_4442155 : Nat := 2280960656773172781833407

theorem tailTrace_4442155 : CollatzResearch.WordTrace tailWord_4442155 prefixEnd_4442155 2280960656773172781833407 := by
  unfold tailWord_4442155
  simp only [CollatzResearch.WordTrace]
  refine ⟨162018703221838569519127919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108012468814559046346085279 162018703221838569519127919)
  ·
    refine ⟨243028054832757854278691879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162018703221838569519127919 243028054832757854278691879)
    ·
      refine ⟨364542082249136781418037819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243028054832757854278691879 364542082249136781418037819)
      ·
        refine ⟨546813123373705172127056729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364542082249136781418037819 546813123373705172127056729)
        ·
          refine ⟨410109842530278879095292547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546813123373705172127056729 410109842530278879095292547)
          ·
            refine ⟨615164763795418318642938821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410109842530278879095292547 615164763795418318642938821)
            ·
              refine ⟨115343393211640934745551029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 615164763795418318642938821 115343393211640934745551029)
              ·
                refine ⟨10813443113591337632395409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115343393211640934745551029 10813443113591337632395409)
                ·
                  refine ⟨8110082335193503224296557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10813443113591337632395409 8110082335193503224296557)
                  ·
                    refine ⟨3041280875697563709111209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8110082335193503224296557 3041280875697563709111209)
                    ·
                      refine ⟨2280960656773172781833407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041280875697563709111209 2280960656773172781833407)
                      ·
                        rfl

theorem cell23_4442155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3, 2].length) (baseStart_4442155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442155 prefixEnd_4442155 := by exact prefixLift 4442155
  have htrace : WordTrace (prefixWord ++ tailWord_4442155) baseStart_4442155 baseEnd_4442155 := by
    simpa [prefixWord, tailWord_4442155, baseEnd_4442155] using wordTrace_append hprefix tailTrace_4442155
  have hstable : (prefixWord ++ tailWord_4442155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442155).length < 2 ^ (prefixWord ++ tailWord_4442155).sum := by decide
  have hdescent : baseEnd_4442155 < baseStart_4442155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442188 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4442188 : Nat := 118140960795 + 4442188 * 2 ^ 59
def prefixEnd_4442188 : Nat := 4983230072969 + 3 ^ 40 * 4442188 * 2
def baseEnd_4442188 : Nat := 2280977601634771152720755

theorem tailTrace_4442188 : CollatzResearch.WordTrace tailWord_4442188 prefixEnd_4442188 2280977601634771152720755 := by
  unfold tailWord_4442188
  simp only [CollatzResearch.WordTrace]
  refine ⟨81009953415359508077539609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108013271220479344103386145 81009953415359508077539609)
  ·
    refine ⟨60757465061519631058154707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81009953415359508077539609 60757465061519631058154707)
    ·
      refine ⟨91136197592279446587232061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60757465061519631058154707 91136197592279446587232061)
      ·
        refine ⟨34176074097104792470212023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91136197592279446587232061 34176074097104792470212023)
        ·
          refine ⟨51264111145657188705318035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34176074097104792470212023 51264111145657188705318035)
          ·
            refine ⟨76896166718485783057977053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51264111145657188705318035 76896166718485783057977053)
            ·
              refine ⟨28836062519432168646741395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76896166718485783057977053 28836062519432168646741395)
              ·
                refine ⟨43254093779148252970112093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28836062519432168646741395 43254093779148252970112093)
                ·
                  refine ⟨16220285167180594863792035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43254093779148252970112093 16220285167180594863792035)
                  ·
                    refine ⟨24330427750770892295688053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16220285167180594863792035 24330427750770892295688053)
                    ·
                      refine ⟨2280977601634771152720755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24330427750770892295688053 2280977601634771152720755)
                      ·
                        rfl

theorem cell23_4442188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4442188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442188 prefixEnd_4442188 := by exact prefixLift 4442188
  have htrace : WordTrace (prefixWord ++ tailWord_4442188) baseStart_4442188 baseEnd_4442188 := by
    simpa [prefixWord, tailWord_4442188, baseEnd_4442188] using wordTrace_append hprefix tailTrace_4442188
  have hstable : (prefixWord ++ tailWord_4442188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442188).length < 2 ^ (prefixWord ++ tailWord_4442188).sum := by decide
  have hdescent : baseEnd_4442188 < baseStart_4442188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442202 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2]
def baseStart_4442202 : Nat := 118140960795 + 4442202 * 2 ^ 59
def prefixEnd_4442202 : Nat := 4983230072969 + 3 ^ 40 * 4442202 * 2
def baseEnd_4442202 : Nat := 2280984790363934097945691

theorem tailTrace_4442202 : CollatzResearch.WordTrace tailWord_4442202 prefixEnd_4442202 2280984790363934097945691 := by
  unfold tailWord_4442202
  simp only [CollatzResearch.WordTrace]
  refine ⟨40505104363167074136522215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108013611635112197697392573 40505104363167074136522215)
  ·
    refine ⟨60757656544750611204783323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40505104363167074136522215 60757656544750611204783323)
    ·
      refine ⟨91136484817125916807174985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60757656544750611204783323 91136484817125916807174985)
      ·
        refine ⟨68352363612844437605381239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91136484817125916807174985 68352363612844437605381239)
        ·
          refine ⟨102528545419266656408071859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68352363612844437605381239 102528545419266656408071859)
          ·
            refine ⟨153792818128899984612107789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102528545419266656408071859 153792818128899984612107789)
            ·
              refine ⟨57672306798337494229540421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153792818128899984612107789 57672306798337494229540421)
              ·
                refine ⟨10813557524688280168038829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57672306798337494229540421 10813557524688280168038829)
                ·
                  refine ⟨4055084071758105063014561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10813557524688280168038829 4055084071758105063014561)
                  ·
                    refine ⟨3041313053818578797260921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4055084071758105063014561 3041313053818578797260921)
                    ·
                      refine ⟨2280984790363934097945691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041313053818578797260921 2280984790363934097945691)
                      ·
                        rfl

theorem cell23_4442202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_4442202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442202 prefixEnd_4442202 := by exact prefixLift 4442202
  have htrace : WordTrace (prefixWord ++ tailWord_4442202) baseStart_4442202 baseEnd_4442202 := by
    simpa [prefixWord, tailWord_4442202, baseEnd_4442202] using wordTrace_append hprefix tailTrace_4442202
  have hstable : (prefixWord ++ tailWord_4442202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442202).length < 2 ^ (prefixWord ++ tailWord_4442202).sum := by decide
  have hdescent : baseEnd_4442202 < baseStart_4442202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442208 : List Nat := [2, 1, 1, 3, 2, 4, 1, 9]
def baseStart_4442208 : Nat := 118140960795 + 4442208 * 2 ^ 59
def prefixEnd_4442208 : Nat := 4983230072969 + 3 ^ 40 * 4442208 * 2
def baseEnd_4442208 : Nat := 84481032268439299054469

theorem tailTrace_4442208 : CollatzResearch.WordTrace tailWord_4442208 prefixEnd_4442208 84481032268439299054469 := by
  unfold tailWord_4442208
  simp only [CollatzResearch.WordTrace]
  refine ⟨81010318145323279785403639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108013757527097706380538185 81010318145323279785403639)
  ·
    refine ⟨121515477217984919678105459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81010318145323279785403639 121515477217984919678105459)
    ·
      refine ⟨182273215826977379517158189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121515477217984919678105459 182273215826977379517158189)
      ·
        refine ⟨68352455935116517318934321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182273215826977379517158189 68352455935116517318934321)
        ·
          refine ⟨51264341951337387989200741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68352455935116517318934321 51264341951337387989200741)
          ·
            refine ⟨9612064115875760247975139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51264341951337387989200741 9612064115875760247975139)
            ·
              refine ⟨14418096173813640371962709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612064115875760247975139 14418096173813640371962709)
              ·
                refine ⟨84481032268439299054469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14418096173813640371962709 84481032268439299054469)
                ·
                  rfl

theorem cell23_4442208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 9].length) (baseStart_4442208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442208 prefixEnd_4442208 := by exact prefixLift 4442208
  have htrace : WordTrace (prefixWord ++ tailWord_4442208) baseStart_4442208 baseEnd_4442208 := by
    simpa [prefixWord, tailWord_4442208, baseEnd_4442208] using wordTrace_append hprefix tailTrace_4442208
  have hstable : (prefixWord ++ tailWord_4442208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442208).length < 2 ^ (prefixWord ++ tailWord_4442208).sum := by decide
  have hdescent : baseEnd_4442208 < baseStart_4442208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442222 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4442222 : Nat := 118140960795 + 4442222 * 2 ^ 59
def prefixEnd_4442222 : Nat := 4983230072969 + 3 ^ 40 * 4442222 * 2
def baseEnd_4442222 : Nat := 2280995059977024019695599

theorem tailTrace_4442222 : CollatzResearch.WordTrace tailWord_4442222 prefixEnd_4442222 2280995059977024019695599 := by
  unfold tailWord_4442222
  simp only [CollatzResearch.WordTrace]
  refine ⟨20252643364074479995227115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108014097941730559974544613 20252643364074479995227115)
  ·
    refine ⟨30378965046111719992840673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20252643364074479995227115 30378965046111719992840673)
    ·
      refine ⟨22784223784583789994630505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30378965046111719992840673 22784223784583789994630505)
      ·
        refine ⟨17088167838437842495972879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22784223784583789994630505 17088167838437842495972879)
        ·
          refine ⟨25632251757656763743959319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17088167838437842495972879 25632251757656763743959319)
          ·
            refine ⟨38448377636485145615938979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25632251757656763743959319 38448377636485145615938979)
            ·
              refine ⟨57672566454727718423908469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38448377636485145615938979 57672566454727718423908469)
              ·
                refine ⟨5406803105130723602241419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57672566454727718423908469 5406803105130723602241419)
                ·
                  refine ⟨8110204657696085403362129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5406803105130723602241419 8110204657696085403362129)
                  ·
                    refine ⟨6082653493272064052521597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8110204657696085403362129 6082653493272064052521597)
                    ·
                      refine ⟨2280995059977024019695599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6082653493272064052521597 2280995059977024019695599)
                      ·
                        rfl

theorem cell23_4442222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4442222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442222 prefixEnd_4442222 := by exact prefixLift 4442222
  have htrace : WordTrace (prefixWord ++ tailWord_4442222) baseStart_4442222 baseEnd_4442222 := by
    simpa [prefixWord, tailWord_4442222, baseEnd_4442222] using wordTrace_append hprefix tailTrace_4442222
  have hstable : (prefixWord ++ tailWord_4442222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442222).length < 2 ^ (prefixWord ++ tailWord_4442222).sum := by decide
  have hdescent : baseEnd_4442222 < baseStart_4442222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442295 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_4442295 : Nat := 118140960795 + 4442295 * 2 ^ 59
def prefixEnd_4442295 : Nat := 4983230072969 + 3 ^ 40 * 4442295 * 2
def baseEnd_4442295 : Nat := 2281032544064802234082763

theorem tailTrace_4442295 : CollatzResearch.WordTrace tailWord_4442295 prefixEnd_4442295 2281032544064802234082763 := by
  unfold tailWord_4442295
  simp only [CollatzResearch.WordTrace]
  refine ⟨162023809441331373429224339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108015872960887582286149559 162023809441331373429224339)
  ·
    refine ⟨243035714161997060143836509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162023809441331373429224339 243035714161997060143836509)
    ·
      refine ⟨91138392810748897553938691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243035714161997060143836509 91138392810748897553938691)
      ·
        refine ⟨136707589216123346330908037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91138392810748897553938691 136707589216123346330908037)
        ·
          refine ⟨25632672978023127437045257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136707589216123346330908037 25632672978023127437045257)
          ·
            refine ⟨19224504733517345577783943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25632672978023127437045257 19224504733517345577783943)
            ·
              refine ⟨28836757100276018366675915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19224504733517345577783943 28836757100276018366675915)
              ·
                refine ⟨43255135650414027550013873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28836757100276018366675915 43255135650414027550013873)
                ·
                  refine ⟨32441351737810520662510405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43255135650414027550013873 32441351737810520662510405)
                  ·
                    refine ⟨6082753450839472624220701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32441351737810520662510405 6082753450839472624220701)
                    ·
                      refine ⟨2281032544064802234082763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6082753450839472624220701 2281032544064802234082763)
                      ·
                        rfl

theorem cell23_4442295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_4442295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442295 prefixEnd_4442295 := by exact prefixLift 4442295
  have htrace : WordTrace (prefixWord ++ tailWord_4442295) baseStart_4442295 baseEnd_4442295 := by
    simpa [prefixWord, tailWord_4442295, baseEnd_4442295] using wordTrace_append hprefix tailTrace_4442295
  have hstable : (prefixWord ++ tailWord_4442295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442295).length < 2 ^ (prefixWord ++ tailWord_4442295).sum := by decide
  have hdescent : baseEnd_4442295 < baseStart_4442295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442302 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4442302 : Nat := 118140960795 + 4442302 * 2 ^ 59
def prefixEnd_4442302 : Nat := 4983230072969 + 3 ^ 40 * 4442302 * 2
def baseEnd_4442302 : Nat := 760345379476461235565077

theorem tailTrace_4442302 : CollatzResearch.WordTrace tailWord_4442302 prefixEnd_4442302 760345379476461235565077 := by
  unfold tailWord_4442302
  simp only [CollatzResearch.WordTrace]
  refine ⟨20253008094038251703091145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108016043168204009083152773 20253008094038251703091145)
  ·
    refine ⟨15189756070528688777318359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20253008094038251703091145 15189756070528688777318359)
    ·
      refine ⟨22784634105793033165977539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15189756070528688777318359 22784634105793033165977539)
      ·
        refine ⟨34176951158689549748966309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22784634105793033165977539 34176951158689549748966309)
        ·
          refine ⟨6408178342254290577931183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34176951158689549748966309 6408178342254290577931183)
          ·
            refine ⟨9612267513381435866896775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408178342254290577931183 9612267513381435866896775)
            ·
              refine ⟨14418401270072153800345163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612267513381435866896775 14418401270072153800345163)
              ·
                refine ⟨21627601905108230700517745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14418401270072153800345163 21627601905108230700517745)
                ·
                  refine ⟨16220701428831173025388309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21627601905108230700517745 16220701428831173025388309)
                  ·
                    refine ⟨760345379476461235565077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16220701428831173025388309 760345379476461235565077)
                    ·
                      rfl

theorem cell23_4442302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4442302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442302 prefixEnd_4442302 := by exact prefixLift 4442302
  have htrace : WordTrace (prefixWord ++ tailWord_4442302) baseStart_4442302 baseEnd_4442302 := by
    simpa [prefixWord, tailWord_4442302, baseEnd_4442302] using wordTrace_append hprefix tailTrace_4442302
  have hstable : (prefixWord ++ tailWord_4442302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442302).length < 2 ^ (prefixWord ++ tailWord_4442302).sum := by decide
  have hdescent : baseEnd_4442302 < baseStart_4442302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442309 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 2, 2, 2]
def baseStart_4442309 : Nat := 118140960795 + 4442309 * 2 ^ 59
def prefixEnd_4442309 : Nat := 4983230072969 + 3 ^ 40 * 4442309 * 2
def baseEnd_4442309 : Nat := 2281039732793965179307699

theorem tailTrace_4442309 : CollatzResearch.WordTrace tailWord_4442309 prefixEnd_4442309 2281039732793965179307699 := by
  unfold tailWord_4442309
  simp only [CollatzResearch.WordTrace]
  refine ⟨162024320063280653820233981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108016213375520435880155987 162024320063280653820233981)
  ·
    refine ⟨60759120023730245182587743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162024320063280653820233981 60759120023730245182587743)
    ·
      refine ⟨91138680035595367773881615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60759120023730245182587743 91138680035595367773881615)
      ·
        refine ⟨136708020053393051660822423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91138680035595367773881615 136708020053393051660822423)
        ·
          refine ⟨205062030080089577491233635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136708020053393051660822423 205062030080089577491233635)
          ·
            refine ⟨307593045120134366236850453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205062030080089577491233635 307593045120134366236850453)
            ·
              refine ⟨14418423990006298417352365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 307593045120134366236850453 14418423990006298417352365)
              ·
                refine ⟨5406908996252361906507137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14418423990006298417352365 5406908996252361906507137)
                ·
                  refine ⟨4055181747189271429880353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5406908996252361906507137 4055181747189271429880353)
                  ·
                    refine ⟨3041386310391953572410265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4055181747189271429880353 3041386310391953572410265)
                    ·
                      refine ⟨2281039732793965179307699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041386310391953572410265 2281039732793965179307699)
                      ·
                        rfl

theorem cell23_4442309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_4442309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442309 prefixEnd_4442309 := by exact prefixLift 4442309
  have htrace : WordTrace (prefixWord ++ tailWord_4442309) baseStart_4442309 baseEnd_4442309 := by
    simpa [prefixWord, tailWord_4442309, baseEnd_4442309] using wordTrace_append hprefix tailTrace_4442309
  have hstable : (prefixWord ++ tailWord_4442309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442309).length < 2 ^ (prefixWord ++ tailWord_4442309).sum := by decide
  have hdescent : baseEnd_4442309 < baseStart_4442309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442326 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4442326 : Nat := 118140960795 + 4442326 * 2 ^ 59
def prefixEnd_4442326 : Nat := 4983230072969 + 3 ^ 40 * 4442326 * 2
def baseEnd_4442326 : Nat := 2281048461965091612795121

theorem tailTrace_4442326 : CollatzResearch.WordTrace tailWord_4442326 prefixEnd_4442326 2281048461965091612795121 := by
  unfold tailWord_4442326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10126558756513691607725177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108016626736146043815735221 10126558756513691607725177)
  ·
    refine ⟨7594919067385268705793883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10126558756513691607725177 7594919067385268705793883)
    ·
      refine ⟨11392378601077903058690825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7594919067385268705793883 11392378601077903058690825)
      ·
        refine ⟨8544283950808427294018119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11392378601077903058690825 8544283950808427294018119)
        ·
          refine ⟨12816425926212640941027179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544283950808427294018119 12816425926212640941027179)
          ·
            refine ⟨19224638889318961411540769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12816425926212640941027179 19224638889318961411540769)
            ·
              refine ⟨14418479166989221058655577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19224638889318961411540769 14418479166989221058655577)
              ·
                refine ⟨10813859375241915793991683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14418479166989221058655577 10813859375241915793991683)
                ·
                  refine ⟨16220789062862873690987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10813859375241915793991683 16220789062862873690987525)
                  ·
                    refine ⟨3041397949286788817060161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16220789062862873690987525 3041397949286788817060161)
                    ·
                      refine ⟨2281048461965091612795121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041397949286788817060161 2281048461965091612795121)
                      ·
                        rfl

theorem cell23_4442326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4442326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442326 prefixEnd_4442326 := by exact prefixLift 4442326
  have htrace : WordTrace (prefixWord ++ tailWord_4442326) baseStart_4442326 baseEnd_4442326 := by
    simpa [prefixWord, tailWord_4442326, baseEnd_4442326] using wordTrace_append hprefix tailTrace_4442326
  have hstable : (prefixWord ++ tailWord_4442326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442326).length < 2 ^ (prefixWord ++ tailWord_4442326).sum := by decide
  have hdescent : baseEnd_4442326 < baseStart_4442326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442343 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4442343 : Nat := 118140960795 + 4442343 * 2 ^ 59
def prefixEnd_4442343 : Nat := 4983230072969 + 3 ^ 40 * 4442343 * 2
def baseEnd_4442343 : Nat := 2281057191136218046282543

theorem tailTrace_4442343 : CollatzResearch.WordTrace tailWord_4442343 prefixEnd_4442343 2281057191136218046282543 := by
  unfold tailWord_4442343
  simp only [CollatzResearch.WordTrace]
  refine ⟨162025560145157477626971683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108017040096771651751314455 162025560145157477626971683)
  ·
    refine ⟨243038340217736216440457525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162025560145157477626971683 243038340217736216440457525)
    ·
      refine ⟨22784844395412770291292893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 243038340217736216440457525 22784844395412770291292893)
      ·
        refine ⟨8544316648279788859234835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22784844395412770291292893 8544316648279788859234835)
        ·
          refine ⟨12816474972419683288852253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544316648279788859234835 12816474972419683288852253)
          ·
            refine ⟨4806178114657381233319595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12816474972419683288852253 4806178114657381233319595)
            ·
              refine ⟨7209267171986071849979393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4806178114657381233319595 7209267171986071849979393)
              ·
                refine ⟨5406950378989553887484545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7209267171986071849979393 5406950378989553887484545)
                ·
                  refine ⟨4055212784242165415613409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5406950378989553887484545 4055212784242165415613409)
                  ·
                    refine ⟨3041409588181624061710057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4055212784242165415613409 3041409588181624061710057)
                    ·
                      refine ⟨2281057191136218046282543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041409588181624061710057 2281057191136218046282543)
                      ·
                        rfl

theorem cell23_4442343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4442343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442343 prefixEnd_4442343 := by exact prefixLift 4442343
  have htrace : WordTrace (prefixWord ++ tailWord_4442343) baseStart_4442343 baseEnd_4442343 := by
    simpa [prefixWord, tailWord_4442343, baseEnd_4442343] using wordTrace_append hprefix tailTrace_4442343
  have hstable : (prefixWord ++ tailWord_4442343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442343).length < 2 ^ (prefixWord ++ tailWord_4442343).sum := by decide
  have hdescent : baseEnd_4442343 < baseStart_4442343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442382 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4442382 : Nat := 118140960795 + 4442382 * 2 ^ 59
def prefixEnd_4442382 : Nat := 4983230072969 + 3 ^ 40 * 4442382 * 2
def baseEnd_4442382 : Nat := 2281077216881743393694863

theorem tailTrace_4442382 : CollatzResearch.WordTrace tailWord_4442382 prefixEnd_4442382 2281077216881743393694863 := by
  unfold tailWord_4442382
  simp only [CollatzResearch.WordTrace]
  refine ⟨20253372824002023410955175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108017988394677458191760933 20253372824002023410955175)
  ·
    refine ⟨30380059236003035116432763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20253372824002023410955175 30380059236003035116432763)
    ·
      refine ⟨45570088854004552674649145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30380059236003035116432763 45570088854004552674649145)
      ·
        refine ⟨34177566640503414505986859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45570088854004552674649145 34177566640503414505986859)
        ·
          refine ⟨51266349960755121758980289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34177566640503414505986859 51266349960755121758980289)
          ·
            refine ⟨38449762470566341319235217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51266349960755121758980289 38449762470566341319235217)
            ·
              refine ⟨28837321852924755989426413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38449762470566341319235217 28837321852924755989426413)
              ·
                refine ⟨10813995694846783496034905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28837321852924755989426413 10813995694846783496034905)
                ·
                  refine ⟨8110496771135087622026179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10813995694846783496034905 8110496771135087622026179)
                  ·
                    refine ⟨12165745156702631433039269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8110496771135087622026179 12165745156702631433039269)
                    ·
                      refine ⟨2281077216881743393694863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12165745156702631433039269 2281077216881743393694863)
                      ·
                        rfl

theorem cell23_4442382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4442382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442382 prefixEnd_4442382 := by exact prefixLift 4442382
  have htrace : WordTrace (prefixWord ++ tailWord_4442382) baseStart_4442382 baseEnd_4442382 := by
    simpa [prefixWord, tailWord_4442382, baseEnd_4442382] using wordTrace_append hprefix tailTrace_4442382
  have hstable : (prefixWord ++ tailWord_4442382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442382).length < 2 ^ (prefixWord ++ tailWord_4442382).sum := by decide
  have hdescent : baseEnd_4442382 < baseStart_4442382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442482 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_4442482 : Nat := 118140960795 + 4442482 * 2 ^ 59
def prefixEnd_4442482 : Nat := 4983230072969 + 3 ^ 40 * 4442482 * 2
def baseEnd_4442482 : Nat := 760376188315731000814801

theorem tailTrace_4442482 : CollatzResearch.WordTrace tailWord_4442482 prefixEnd_4442482 760376188315731000814801 := by
  unfold tailWord_4442482
  simp only [CollatzResearch.WordTrace]
  refine ⟨40507657472913476091570425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108020419927769269577521133 40507657472913476091570425)
  ·
    refine ⟨30380743104685107068677819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40507657472913476091570425 30380743104685107068677819)
    ·
      refine ⟨45571114657027660603016729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30380743104685107068677819 45571114657027660603016729)
      ·
        refine ⟨34178335992770745452262547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45571114657027660603016729 34178335992770745452262547)
        ·
          refine ⟨51267503989156118178393821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34178335992770745452262547 51267503989156118178393821)
          ·
            refine ⟨19225313995933544316897683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51267503989156118178393821 19225313995933544316897683)
            ·
              refine ⟨28837970993900316475346525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19225313995933544316897683 28837970993900316475346525)
              ·
                refine ⟨10814239122712618678254947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28837970993900316475346525 10814239122712618678254947)
                ·
                  refine ⟨16221358684068928017382421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10814239122712618678254947 16221358684068928017382421)
                  ·
                    refine ⟨760376188315731000814801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16221358684068928017382421 760376188315731000814801)
                    ·
                      rfl

theorem cell23_4442482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_4442482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442482 prefixEnd_4442482 := by exact prefixLift 4442482
  have htrace : WordTrace (prefixWord ++ tailWord_4442482) baseStart_4442482 baseEnd_4442482 := by
    simpa [prefixWord, tailWord_4442482, baseEnd_4442482] using wordTrace_append hprefix tailTrace_4442482
  have hstable : (prefixWord ++ tailWord_4442482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442482).length < 2 ^ (prefixWord ++ tailWord_4442482).sum := by decide
  have hdescent : baseEnd_4442482 < baseStart_4442482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442516 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4442516 : Nat := 118140960795 + 4442516 * 2 ^ 59
def prefixEnd_4442516 : Nat := 4983230072969 + 3 ^ 40 * 4442516 * 2
def baseEnd_4442516 : Nat := 760382007763148623139749

theorem tailTrace_4442516 : CollatzResearch.WordTrace tailWord_4442516 prefixEnd_4442516 760382007763148623139749 := by
  unfold tailWord_4442516
  simp only [CollatzResearch.WordTrace]
  refine ⟨81015934986765364086509701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108021246649020485448679601 81015934986765364086509701)
  ·
    refine ⟨15190487810018505766220569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81015934986765364086509701 15190487810018505766220569)
    ·
      refine ⟨11392865857513879324665427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15190487810018505766220569 11392865857513879324665427)
      ·
        refine ⟨17089298786270818986998141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11392865857513879324665427 17089298786270818986998141)
        ·
          refine ⟨6408487044851557120124303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17089298786270818986998141 6408487044851557120124303)
          ·
            refine ⟨9612730567277335680186455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408487044851557120124303 9612730567277335680186455)
            ·
              refine ⟨14419095850916003520279683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612730567277335680186455 14419095850916003520279683)
              ·
                refine ⟨21628643776374005280419525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14419095850916003520279683 21628643776374005280419525)
                ·
                  refine ⟨4055370708070125990078661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21628643776374005280419525 4055370708070125990078661)
                  ·
                    refine ⟨760382007763148623139749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055370708070125990078661 760382007763148623139749)
                    ·
                      rfl

theorem cell23_4442516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4442516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442516 prefixEnd_4442516 := by exact prefixLift 4442516
  have htrace : WordTrace (prefixWord ++ tailWord_4442516) baseStart_4442516 baseEnd_4442516 := by
    simpa [prefixWord, tailWord_4442516, baseEnd_4442516] using wordTrace_append hprefix tailTrace_4442516
  have hstable : (prefixWord ++ tailWord_4442516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442516).length < 2 ^ (prefixWord ++ tailWord_4442516).sum := by decide
  have hdescent : baseEnd_4442516 < baseStart_4442516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442526 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4442526 : Nat := 118140960795 + 4442526 * 2 ^ 59
def prefixEnd_4442526 : Nat := 4983230072969 + 3 ^ 40 * 4442526 * 2
def baseEnd_4442526 : Nat := 2281151158095990830294201

theorem tailTrace_4442526 : CollatzResearch.WordTrace tailWord_4442526 prefixEnd_4442526 2281151158095990830294201 := by
  unfold tailWord_4442526
  simp only [CollatzResearch.WordTrace]
  refine ⟨20254029337936812485110429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108021489802329666587255621 20254029337936812485110429)
  ·
    refine ⟨7595261001726304681916411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20254029337936812485110429 7595261001726304681916411)
    ·
      refine ⟨11392891502589457022874617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7595261001726304681916411 11392891502589457022874617)
      ·
        refine ⟨8544668626942092767155963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11392891502589457022874617 8544668626942092767155963)
        ·
          refine ⟨12817002940413139150733945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544668626942092767155963 12817002940413139150733945)
          ·
            refine ⟨9612752205309854363050459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12817002940413139150733945 9612752205309854363050459)
            ·
              refine ⟨14419128307964781544575689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612752205309854363050459 14419128307964781544575689)
              ·
                refine ⟨10814346230973586158431767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14419128307964781544575689 10814346230973586158431767)
                ·
                  refine ⟨16221519346460379237647651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10814346230973586158431767 16221519346460379237647651)
                  ·
                    refine ⟨24332279019690568856471477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16221519346460379237647651 24332279019690568856471477)
                    ·
                      refine ⟨2281151158095990830294201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24332279019690568856471477 2281151158095990830294201)
                      ·
                        rfl

theorem cell23_4442526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4442526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442526 prefixEnd_4442526 := by exact prefixLift 4442526
  have htrace : WordTrace (prefixWord ++ tailWord_4442526) baseStart_4442526 baseEnd_4442526 := by
    simpa [prefixWord, tailWord_4442526, baseEnd_4442526] using wordTrace_append hprefix tailTrace_4442526
  have hstable : (prefixWord ++ tailWord_4442526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442526).length < 2 ^ (prefixWord ++ tailWord_4442526).sum := by decide
  have hdescent : baseEnd_4442526 < baseStart_4442526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442536 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4442536 : Nat := 118140960795 + 4442536 * 2 ^ 59
def prefixEnd_4442536 : Nat := 4983230072969 + 3 ^ 40 * 4442536 * 2
def baseEnd_4442536 : Nat := 2281156292902535791169155

theorem tailTrace_4442536 : CollatzResearch.WordTrace tailWord_4442536 prefixEnd_4442536 2281156292902535791169155 := by
  unfold tailWord_4442536
  simp only [CollatzResearch.WordTrace]
  refine ⟨81016299716729135794373731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108021732955638847725831641 81016299716729135794373731)
  ·
    refine ⟨121524449575093703691560597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81016299716729135794373731 121524449575093703691560597)
    ·
      refine ⟨5696458573832517360541903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121524449575093703691560597 5696458573832517360541903)
      ·
        refine ⟨8544687860748776040812855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696458573832517360541903 8544687860748776040812855)
        ·
          refine ⟨12817031791123164061219283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544687860748776040812855 12817031791123164061219283)
          ·
            refine ⟨19225547686684746091828925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12817031791123164061219283 19225547686684746091828925)
            ·
              refine ⟨7209580382506779784435847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19225547686684746091828925 7209580382506779784435847)
              ·
                refine ⟨10814370573760169676653771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209580382506779784435847 10814370573760169676653771)
                ·
                  refine ⟨16221555860640254514980657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10814370573760169676653771 16221555860640254514980657)
                  ·
                    refine ⟨12166166895480190886235493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16221555860640254514980657 12166166895480190886235493)
                    ·
                      refine ⟨2281156292902535791169155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12166166895480190886235493 2281156292902535791169155)
                      ·
                        rfl

theorem cell23_4442536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4442536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442536 prefixEnd_4442536 := by exact prefixLift 4442536
  have htrace : WordTrace (prefixWord ++ tailWord_4442536) baseStart_4442536 baseEnd_4442536 := by
    simpa [prefixWord, tailWord_4442536, baseEnd_4442536] using wordTrace_append hprefix tailTrace_4442536
  have hstable : (prefixWord ++ tailWord_4442536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442536).length < 2 ^ (prefixWord ++ tailWord_4442536).sum := by decide
  have hdescent : baseEnd_4442536 < baseStart_4442536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442556 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4442556 : Nat := 118140960795 + 4442556 * 2 ^ 59
def prefixEnd_4442556 : Nat := 4983230072969 + 3 ^ 40 * 4442556 * 2
def baseEnd_4442556 : Nat := 2281166562515625712919063

theorem tailTrace_4442556 : CollatzResearch.WordTrace tailWord_4442556 prefixEnd_4442556 2281166562515625712919063 := by
  unfold tailWord_4442556
  simp only [CollatzResearch.WordTrace]
  refine ⟨81016664446692907502237761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108022219262257210002983681 81016664446692907502237761)
  ·
    refine ⟨60762498335019680626678321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81016664446692907502237761 60762498335019680626678321)
    ·
      refine ⟨45571873751264760470008741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60762498335019680626678321 45571873751264760470008741)
      ·
        refine ⟨8544726328362142588126639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45571873751264760470008741 8544726328362142588126639)
        ·
          refine ⟨12817089492543213882189959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544726328362142588126639 12817089492543213882189959)
          ·
            refine ⟨19225634238814820823284939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12817089492543213882189959 19225634238814820823284939)
            ·
              refine ⟨28838451358222231234927409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19225634238814820823284939 28838451358222231234927409)
              ·
                refine ⟨21628838518666673426195557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28838451358222231234927409 21628838518666673426195557)
                ·
                  refine ⟨4055407222250001267411667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21628838518666673426195557 4055407222250001267411667)
                  ·
                    refine ⟨6083110833375001901117501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4055407222250001267411667 6083110833375001901117501)
                    ·
                      refine ⟨2281166562515625712919063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6083110833375001901117501 2281166562515625712919063)
                      ·
                        rfl

theorem cell23_4442556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4442556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442556 prefixEnd_4442556 := by exact prefixLift 4442556
  have htrace : WordTrace (prefixWord ++ tailWord_4442556) baseStart_4442556 baseEnd_4442556 := by
    simpa [prefixWord, tailWord_4442556, baseEnd_4442556] using wordTrace_append hprefix tailTrace_4442556
  have hstable : (prefixWord ++ tailWord_4442556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442556).length < 2 ^ (prefixWord ++ tailWord_4442556).sum := by decide
  have hdescent : baseEnd_4442556 < baseStart_4442556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442592 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_4442592 : Nat := 118140960795 + 4442592 * 2 ^ 59
def prefixEnd_4442592 : Nat := 4983230072969 + 3 ^ 40 * 4442592 * 2
def baseEnd_4442592 : Nat := 2281185047819187572068897

theorem tailTrace_4442592 : CollatzResearch.WordTrace tailWord_4442592 prefixEnd_4442592 2281185047819187572068897 := by
  unfold tailWord_4442592
  simp only [CollatzResearch.WordTrace]
  refine ⟨81017320960627696576393015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108023094614170262101857353 81017320960627696576393015)
  ·
    refine ⟨121525981440941544864589523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81017320960627696576393015 121525981440941544864589523)
    ·
      refine ⟨182288972161412317296884285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121525981440941544864589523 182288972161412317296884285)
      ·
        refine ⟨68358364560529618986331607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182288972161412317296884285 68358364560529618986331607)
        ·
          refine ⟨102537546840794428479497411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68358364560529618986331607 102537546840794428479497411)
          ·
            refine ⟨153806320261191642719246117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102537546840794428479497411 153806320261191642719246117)
            ·
              refine ⟨28838685048973433009858647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153806320261191642719246117 28838685048973433009858647)
              ·
                refine ⟨43258027573460149514787971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28838685048973433009858647 43258027573460149514787971)
                ·
                  refine ⟨64887041360190224272181957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43258027573460149514787971 64887041360190224272181957)
                  ·
                    refine ⟨12166320255035667051034117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64887041360190224272181957 12166320255035667051034117)
                    ·
                      refine ⟨2281185047819187572068897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12166320255035667051034117 2281185047819187572068897)
                      ·
                        rfl

theorem cell23_4442592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_4442592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442592 prefixEnd_4442592 := by exact prefixLift 4442592
  have htrace : WordTrace (prefixWord ++ tailWord_4442592) baseStart_4442592 baseEnd_4442592 := by
    simpa [prefixWord, tailWord_4442592, baseEnd_4442592] using wordTrace_append hprefix tailTrace_4442592
  have hstable : (prefixWord ++ tailWord_4442592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442592).length < 2 ^ (prefixWord ++ tailWord_4442592).sum := by decide
  have hdescent : baseEnd_4442592 < baseStart_4442592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442632 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_4442632 : Nat := 118140960795 + 4442632 * 2 ^ 59
def prefixEnd_4442632 : Nat := 4983230072969 + 3 ^ 40 * 4442632 * 2
def baseEnd_4442632 : Nat := 760401862348455805189571

theorem tailTrace_4442632 : CollatzResearch.WordTrace tailWord_4442632 prefixEnd_4442632 760401862348455805189571 := by
  unfold tailWord_4442632
  simp only [CollatzResearch.WordTrace]
  refine ⟨81018050420555239992121075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108024067227406986656161433 81018050420555239992121075)
  ·
    refine ⟨121527075630832859988181613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81018050420555239992121075 121527075630832859988181613)
    ·
      refine ⟨45572653361562322495568105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121527075630832859988181613 45572653361562322495568105)
      ·
        refine ⟨34179490021171741871676079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45572653361562322495568105 34179490021171741871676079)
        ·
          refine ⟨51269235031757612807514119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34179490021171741871676079 51269235031757612807514119)
          ·
            refine ⟨76903852547636419211271179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51269235031757612807514119 76903852547636419211271179)
            ·
              refine ⟨115355778821454628816906769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76903852547636419211271179 115355778821454628816906769)
              ·
                refine ⟨86516834116090971612680077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115355778821454628816906769 86516834116090971612680077)
                ·
                  refine ⟨32443812793534114354755029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86516834116090971612680077 32443812793534114354755029)
                  ·
                    refine ⟨760401862348455805189571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32443812793534114354755029 760401862348455805189571)
                    ·
                      rfl

theorem cell23_4442632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_4442632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442632 prefixEnd_4442632 := by exact prefixLift 4442632
  have htrace : WordTrace (prefixWord ++ tailWord_4442632) baseStart_4442632 baseEnd_4442632 := by
    simpa [prefixWord, tailWord_4442632, baseEnd_4442632] using wordTrace_append hprefix tailTrace_4442632
  have hstable : (prefixWord ++ tailWord_4442632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442632).length < 2 ^ (prefixWord ++ tailWord_4442632).sum := by decide
  have hdescent : baseEnd_4442632 < baseStart_4442632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442636 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 5]
def baseStart_4442636 : Nat := 118140960795 + 4442636 * 2 ^ 59
def prefixEnd_4442636 : Nat := 4983230072969 + 3 ^ 40 * 4442636 * 2
def baseEnd_4442636 : Nat := 253467515663109488879855

theorem tailTrace_4442636 : CollatzResearch.WordTrace tailWord_4442636 prefixEnd_4442636 253467515663109488879855 := by
  unfold tailWord_4442636
  simp only [CollatzResearch.WordTrace]
  refine ⟨81018123366547994333693881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108024164488730659111591841 81018123366547994333693881)
  ·
    refine ⟨60763592524910995750270411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81018123366547994333693881 60763592524910995750270411)
    ·
      refine ⟨91145388787366493625405617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60763592524910995750270411 91145388787366493625405617)
      ·
        refine ⟨68359041590524870219054213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91145388787366493625405617 68359041590524870219054213)
        ·
          refine ⟨12817320298223413166072665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68359041590524870219054213 12817320298223413166072665)
          ·
            refine ⟨9612990223667559874554499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12817320298223413166072665 9612990223667559874554499)
            ·
              refine ⟨14419485335501339811831749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612990223667559874554499 14419485335501339811831749)
              ·
                refine ⟨2703653500406501214718453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14419485335501339811831749 2703653500406501214718453)
                ·
                  refine ⟨253467515663109488879855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2703653500406501214718453 253467515663109488879855)
                  ·
                    rfl

theorem cell23_4442636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_4442636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442636 prefixEnd_4442636 := by exact prefixLift 4442636
  have htrace : WordTrace (prefixWord ++ tailWord_4442636) baseStart_4442636 baseEnd_4442636 := by
    simpa [prefixWord, tailWord_4442636, baseEnd_4442636] using wordTrace_append hprefix tailTrace_4442636
  have hstable : (prefixWord ++ tailWord_4442636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442636).length < 2 ^ (prefixWord ++ tailWord_4442636).sum := by decide
  have hdescent : baseEnd_4442636 < baseStart_4442636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442639 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 2, 5, 2]
def baseStart_4442639 : Nat := 118140960795 + 4442639 * 2 ^ 59
def prefixEnd_4442639 : Nat := 4983230072969 + 3 ^ 40 * 4442639 * 2
def baseEnd_4442639 : Nat := 2281209181409948888181181

theorem tailTrace_4442639 : CollatzResearch.WordTrace tailWord_4442639 prefixEnd_4442639 2281209181409948888181181 := by
  unfold tailWord_4442639
  simp only [CollatzResearch.WordTrace]
  refine ⟨162036356152085120179746971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108024237434723413453164647 162036356152085120179746971)
  ·
    refine ⟨243054534228127680269620457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162036356152085120179746971 243054534228127680269620457)
    ·
      refine ⟨182290900671095760202215343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243054534228127680269620457 182290900671095760202215343)
      ·
        refine ⟨273436351006643640303323015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182290900671095760202215343 273436351006643640303323015)
        ·
          refine ⟨410154526509965460454984523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273436351006643640303323015 410154526509965460454984523)
          ·
            refine ⟨615231789764948190682476785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410154526509965460454984523 615231789764948190682476785)
            ·
              refine ⟨461423842323711143011857589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615231789764948190682476785 461423842323711143011857589)
              ·
                refine ⟨43258485217847919657361649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461423842323711143011857589 43258485217847919657361649)
                ·
                  refine ⟨32443863913385939743021237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43258485217847919657361649 32443863913385939743021237)
                  ·
                    refine ⟨3041612241879931850908241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32443863913385939743021237 3041612241879931850908241)
                    ·
                      refine ⟨2281209181409948888181181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041612241879931850908241 2281209181409948888181181)
                      ·
                        rfl

theorem cell23_4442639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5, 2].length) (baseStart_4442639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442639 prefixEnd_4442639 := by exact prefixLift 4442639
  have htrace : WordTrace (prefixWord ++ tailWord_4442639) baseStart_4442639 baseEnd_4442639 := by
    simpa [prefixWord, tailWord_4442639, baseEnd_4442639] using wordTrace_append hprefix tailTrace_4442639
  have hstable : (prefixWord ++ tailWord_4442639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442639).length < 2 ^ (prefixWord ++ tailWord_4442639).sum := by decide
  have hdescent : baseEnd_4442639 < baseStart_4442639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442666 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4442666 : Nat := 118140960795 + 4442666 * 2 ^ 59
def prefixEnd_4442666 : Nat := 4983230072969 + 3 ^ 40 * 4442666 * 2
def baseEnd_4442666 : Nat := 760407681795873427514519

theorem tailTrace_4442666 : CollatzResearch.WordTrace tailWord_4442666 prefixEnd_4442666 760407681795873427514519 := by
  unfold tailWord_4442666
  simp only [CollatzResearch.WordTrace]
  refine ⟨40509335230746825947744963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108024893948658202527319901 40509335230746825947744963)
  ·
    refine ⟨60764002846120238921617445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40509335230746825947744963 60764002846120238921617445)
    ·
      refine ⟨11393250533647544797803271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60764002846120238921617445 11393250533647544797803271)
      ·
        refine ⟨17089875800471317196704907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11393250533647544797803271 17089875800471317196704907)
        ·
          refine ⟨25634813700706975795057361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17089875800471317196704907 25634813700706975795057361)
          ·
            refine ⟨19226110275530231846293021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25634813700706975795057361 19226110275530231846293021)
            ·
              refine ⟨7209791353323836942359883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19226110275530231846293021 7209791353323836942359883)
              ·
                refine ⟨10814687029985755413539825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209791353323836942359883 10814687029985755413539825)
                ·
                  refine ⟨8111015272489316560154869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10814687029985755413539825 8111015272489316560154869)
                  ·
                    refine ⟨760407681795873427514519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8111015272489316560154869 760407681795873427514519)
                    ·
                      rfl

theorem cell23_4442666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4442666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442666 prefixEnd_4442666 := by exact prefixLift 4442666
  have htrace : WordTrace (prefixWord ++ tailWord_4442666) baseStart_4442666 baseEnd_4442666 := by
    simpa [prefixWord, tailWord_4442666, baseEnd_4442666] using wordTrace_append hprefix tailTrace_4442666
  have hstable : (prefixWord ++ tailWord_4442666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442666).length < 2 ^ (prefixWord ++ tailWord_4442666).sum := by decide
  have hdescent : baseEnd_4442666 < baseStart_4442666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442679 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 5, 4]
def baseStart_4442679 : Nat := 118140960795 + 4442679 * 2 ^ 59
def prefixEnd_4442679 : Nat := 4983230072969 + 3 ^ 40 * 4442679 * 2
def baseEnd_4442679 : Nat := 760409906878709577226999

theorem tailTrace_4442679 : CollatzResearch.WordTrace tailWord_4442679 prefixEnd_4442679 760409906878709577226999 := by
  unfold tailWord_4442679
  simp only [CollatzResearch.WordTrace]
  refine ⟨162037815071940207011203091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108025210047960138007468727 162037815071940207011203091)
  ·
    refine ⟨243056722607910310516804637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162037815071940207011203091 243056722607910310516804637)
    ·
      refine ⟨91146270977966366443801739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243056722607910310516804637 91146270977966366443801739)
      ·
        refine ⟨136719406466949549665702609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91146270977966366443801739 136719406466949549665702609)
        ·
          refine ⟨102539554850212162249276957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136719406466949549665702609 102539554850212162249276957)
          ·
            refine ⟨38452333068829560843478859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102539554850212162249276957 38452333068829560843478859)
            ·
              refine ⟨57678499603244341265218289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38452333068829560843478859 57678499603244341265218289)
              ·
                refine ⟨43258874702433255948913717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57678499603244341265218289 43258874702433255948913717)
                ·
                  refine ⟨4055519503353117745210661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43258874702433255948913717 4055519503353117745210661)
                  ·
                    refine ⟨760409906878709577226999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055519503353117745210661 760409906878709577226999)
                    ·
                      rfl

theorem cell23_4442679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_4442679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442679 prefixEnd_4442679 := by exact prefixLift 4442679
  have htrace : WordTrace (prefixWord ++ tailWord_4442679) baseStart_4442679 baseEnd_4442679 := by
    simpa [prefixWord, tailWord_4442679, baseEnd_4442679] using wordTrace_append hprefix tailTrace_4442679
  have hstable : (prefixWord ++ tailWord_4442679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442679).length < 2 ^ (prefixWord ++ tailWord_4442679).sum := by decide
  have hdescent : baseEnd_4442679 < baseStart_4442679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442709 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 6]
def baseStart_4442709 : Nat := 118140960795 + 4442709 * 2 ^ 59
def prefixEnd_4442709 : Nat := 4983230072969 + 3 ^ 40 * 4442709 * 2
def baseEnd_4442709 : Nat := 253471680561751512700651

theorem tailTrace_4442709 : CollatzResearch.WordTrace tailWord_4442709 prefixEnd_4442709 253471680561751512700651 := by
  unfold tailWord_4442709
  simp only [CollatzResearch.WordTrace]
  refine ⟨162038909261831522134795181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108025939507887681423196787 162038909261831522134795181)
  ·
    refine ⟨60764590973186820800548193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162038909261831522134795181 60764590973186820800548193)
    ·
      refine ⟨45573443229890115600411145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60764590973186820800548193 45573443229890115600411145)
      ·
        refine ⟨34180082422417586700308359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45573443229890115600411145 34180082422417586700308359)
        ·
          refine ⟨51270123633626380050462539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34180082422417586700308359 51270123633626380050462539)
          ·
            refine ⟨76905185450439570075693809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51270123633626380050462539 76905185450439570075693809)
            ·
              refine ⟨57678889087829677556770357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76905185450439570075693809 57678889087829677556770357)
              ·
                refine ⟨5407395851984032270947221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57678889087829677556770357 5407395851984032270947221)
                ·
                  refine ⟨253471680561751512700651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5407395851984032270947221 253471680561751512700651)
                  ·
                    rfl

theorem cell23_4442709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_4442709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442709 prefixEnd_4442709 := by exact prefixLift 4442709
  have htrace : WordTrace (prefixWord ++ tailWord_4442709) baseStart_4442709 baseEnd_4442709 := by
    simpa [prefixWord, tailWord_4442709, baseEnd_4442709] using wordTrace_append hprefix tailTrace_4442709
  have hstable : (prefixWord ++ tailWord_4442709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442709).length < 2 ^ (prefixWord ++ tailWord_4442709).sum := by decide
  have hdescent : baseEnd_4442709 < baseStart_4442709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442776 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4442776 : Nat := 118140960795 + 4442776 * 2 ^ 59
def prefixEnd_4442776 : Nat := 4983230072969 + 3 ^ 40 * 4442776 * 2
def baseEnd_4442776 : Nat := 2281279528259614852168051

theorem tailTrace_4442776 : CollatzResearch.WordTrace tailWord_4442776 prefixEnd_4442776 2281279528259614852168051 := by
  unfold tailWord_4442776
  simp only [CollatzResearch.WordTrace]
  refine ⟨81020676476294396288742091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108027568635059195051656121 81020676476294396288742091)
  ·
    refine ⟨121531014714441594433113137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81020676476294396288742091 121531014714441594433113137)
    ·
      refine ⟨91148261035831195824834853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121531014714441594433113137 91148261035831195824834853)
      ·
        refine ⟨17090298944218349217156535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91148261035831195824834853 17090298944218349217156535)
        ·
          refine ⟨25635448416327523825734803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17090298944218349217156535 25635448416327523825734803)
          ·
            refine ⟨38453172624491285738602205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25635448416327523825734803 38453172624491285738602205)
            ·
              refine ⟨14419939734184232151975827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38453172624491285738602205 14419939734184232151975827)
              ·
                refine ⟨21629909601276348227963741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14419939734184232151975827 21629909601276348227963741)
                ·
                  refine ⟨8111216100478630585486403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21629909601276348227963741 8111216100478630585486403)
                  ·
                    refine ⟨12166824150717945878229605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8111216100478630585486403 12166824150717945878229605)
                    ·
                      refine ⟨2281279528259614852168051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12166824150717945878229605 2281279528259614852168051)
                      ·
                        rfl

theorem cell23_4442776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4442776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442776 prefixEnd_4442776 := by exact prefixLift 4442776
  have htrace : WordTrace (prefixWord ++ tailWord_4442776) baseStart_4442776 baseEnd_4442776 := by
    simpa [prefixWord, tailWord_4442776, baseEnd_4442776] using wordTrace_append hprefix tailTrace_4442776
  have hstable : (prefixWord ++ tailWord_4442776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442776).length < 2 ^ (prefixWord ++ tailWord_4442776).sum := by decide
  have hdescent : baseEnd_4442776 < baseStart_4442776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442780 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4442780 : Nat := 118140960795 + 4442780 * 2 ^ 59
def prefixEnd_4442780 : Nat := 4983230072969 + 3 ^ 40 * 4442780 * 2
def baseEnd_4442780 : Nat := 2281281582182232836518033

theorem tailTrace_4442780 : CollatzResearch.WordTrace tailWord_4442780 prefixEnd_4442780 2281281582182232836518033 := by
  unfold tailWord_4442780
  simp only [CollatzResearch.WordTrace]
  refine ⟨81020749422287150630314897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108027665896382867507086529 81020749422287150630314897)
  ·
    refine ⟨60765562066715362972736173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81020749422287150630314897 60765562066715362972736173)
    ·
      refine ⟨22787085775018261114776065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60765562066715362972736173 22787085775018261114776065)
      ·
        refine ⟨17090314331263695836082049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22787085775018261114776065 17090314331263695836082049)
        ·
          refine ⟨12817735748447771877061537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17090314331263695836082049 12817735748447771877061537)
          ·
            refine ⟨9613301811335828907796153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12817735748447771877061537 9613301811335828907796153)
            ·
              refine ⟨7209976358501871680847115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9613301811335828907796153 7209976358501871680847115)
              ·
                refine ⟨10814964537752807521270673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209976358501871680847115 10814964537752807521270673)
                ·
                  refine ⟨8111223403314605640953005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10814964537752807521270673 8111223403314605640953005)
                  ·
                    refine ⟨3041708776242977115357377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8111223403314605640953005 3041708776242977115357377)
                    ·
                      refine ⟨2281281582182232836518033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041708776242977115357377 2281281582182232836518033)
                      ·
                        rfl

theorem cell23_4442780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4442780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442780 prefixEnd_4442780 := by exact prefixLift 4442780
  have htrace : WordTrace (prefixWord ++ tailWord_4442780) baseStart_4442780 baseEnd_4442780 := by
    simpa [prefixWord, tailWord_4442780, baseEnd_4442780] using wordTrace_append hprefix tailTrace_4442780
  have hstable : (prefixWord ++ tailWord_4442780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442780).length < 2 ^ (prefixWord ++ tailWord_4442780).sum := by decide
  have hdescent : baseEnd_4442780 < baseStart_4442780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442803 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 2, 4]
def baseStart_4442803 : Nat := 118140960795 + 4442803 * 2 ^ 59
def prefixEnd_4442803 : Nat := 4983230072969 + 3 ^ 40 * 4442803 * 2
def baseEnd_4442803 : Nat := 760431130745762082176809

theorem tailTrace_4442803 : CollatzResearch.WordTrace tailWord_4442803 prefixEnd_4442803 760431130745762082176809 := by
  unfold tailWord_4442803
  simp only [CollatzResearch.WordTrace]
  refine ⟨162042337723490976188717063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108028225148993984125811375 162042337723490976188717063)
  ·
    refine ⟨243063506585236464283075595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162042337723490976188717063 243063506585236464283075595)
    ·
      refine ⟨364595259877854696424613393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243063506585236464283075595 364595259877854696424613393)
      ·
        refine ⟨273446444908391022318460045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364595259877854696424613393 273446444908391022318460045)
        ·
          refine ⟨102542416840646633369422517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273446444908391022318460045 102542416840646633369422517)
          ·
            refine ⟨9613351578810621878383361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102542416840646633369422517 9613351578810621878383361)
            ·
              refine ⟨7210013684107966408787521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9613351578810621878383361 7210013684107966408787521)
              ·
                refine ⟨5407510263080974806590641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7210013684107966408787521 5407510263080974806590641)
                ·
                  refine ⟨4055632697310731104942981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5407510263080974806590641 4055632697310731104942981)
                  ·
                    refine ⟨760431130745762082176809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055632697310731104942981 760431130745762082176809)
                    ·
                      rfl

theorem cell23_4442803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 4].length) (baseStart_4442803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442803 prefixEnd_4442803 := by exact prefixLift 4442803
  have htrace : WordTrace (prefixWord ++ tailWord_4442803) baseStart_4442803 baseEnd_4442803 := by
    simpa [prefixWord, tailWord_4442803, baseEnd_4442803] using wordTrace_append hprefix tailTrace_4442803
  have hstable : (prefixWord ++ tailWord_4442803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442803).length < 2 ^ (prefixWord ++ tailWord_4442803).sum := by decide
  have hdescent : baseEnd_4442803 < baseStart_4442803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442816 : List Nat := [2, 1, 1, 2, 4, 4, 1, 8]
def baseStart_4442816 : Nat := 118140960795 + 4442816 * 2 ^ 59
def prefixEnd_4442816 : Nat := 4983230072969 + 3 ^ 40 * 4442816 * 2
def baseEnd_4442816 : Nat := 84492595092066470209921

theorem tailTrace_4442816 : CollatzResearch.WordTrace tailWord_4442816 prefixEnd_4442816 84492595092066470209921 := by
  unfold tailWord_4442816
  simp only [CollatzResearch.WordTrace]
  refine ⟨81021405936221939704470151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108028541248295919605960201 81021405936221939704470151)
  ·
    refine ⟨121532108904332909556705227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81021405936221939704470151 121532108904332909556705227)
    ·
      refine ⟨182298163356499364335057841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121532108904332909556705227 182298163356499364335057841)
      ·
        refine ⟨136723622517374523251293381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182298163356499364335057841 136723622517374523251293381)
        ·
          refine ⟨25635679222007723109617509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136723622517374523251293381 25635679222007723109617509)
          ·
            refine ⟨4806689854126448083053283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25635679222007723109617509 4806689854126448083053283)
            ·
              refine ⟨7210034781189672124579925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4806689854126448083053283 7210034781189672124579925)
              ·
                refine ⟨84492595092066470209921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7210034781189672124579925 84492595092066470209921)
                ·
                  rfl

theorem cell23_4442816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 8].length) (baseStart_4442816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442816 prefixEnd_4442816 := by exact prefixLift 4442816
  have htrace : WordTrace (prefixWord ++ tailWord_4442816) baseStart_4442816 baseEnd_4442816 := by
    simpa [prefixWord, tailWord_4442816, baseEnd_4442816] using wordTrace_append hprefix tailTrace_4442816
  have hstable : (prefixWord ++ tailWord_4442816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442816).length < 2 ^ (prefixWord ++ tailWord_4442816).sum := by decide
  have hdescent : baseEnd_4442816 < baseStart_4442816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442844 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4442844 : Nat := 118140960795 + 4442844 * 2 ^ 59
def prefixEnd_4442844 : Nat := 4983230072969 + 3 ^ 40 * 4442844 * 2
def baseEnd_4442844 : Nat := 2281314444944120586117739

theorem tailTrace_4442844 : CollatzResearch.WordTrace tailWord_4442844 prefixEnd_4442844 2281314444944120586117739 := by
  unfold tailWord_4442844
  simp only [CollatzResearch.WordTrace]
  refine ⟨81021916558171220095479793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108029222077561626793973057 81021916558171220095479793)
  ·
    refine ⟨60766437418628415071609845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81021916558171220095479793 60766437418628415071609845)
    ·
      refine ⟨5696853507996413912963423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60766437418628415071609845 5696853507996413912963423)
      ·
        refine ⟨8545280261994620869445135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696853507996413912963423 8545280261994620869445135)
        ·
          refine ⟨12817920392991931304167703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8545280261994620869445135 12817920392991931304167703)
          ·
            refine ⟨19226880589487896956251555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12817920392991931304167703 19226880589487896956251555)
            ·
              refine ⟨28840320884231845434377333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19226880589487896956251555 28840320884231845434377333)
              ·
                refine ⟨2703780082896735509472875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28840320884231845434377333 2703780082896735509472875)
                ·
                  refine ⟨4055670124345103264209313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703780082896735509472875 4055670124345103264209313)
                  ·
                    refine ⟨3041752593258827448156985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4055670124345103264209313 3041752593258827448156985)
                    ·
                      refine ⟨2281314444944120586117739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041752593258827448156985 2281314444944120586117739)
                      ·
                        rfl

theorem cell23_4442844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4442844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442844 prefixEnd_4442844 := by exact prefixLift 4442844
  have htrace : WordTrace (prefixWord ++ tailWord_4442844) baseStart_4442844 baseEnd_4442844 := by
    simpa [prefixWord, tailWord_4442844, baseEnd_4442844] using wordTrace_append hprefix tailTrace_4442844
  have hstable : (prefixWord ++ tailWord_4442844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442844).length < 2 ^ (prefixWord ++ tailWord_4442844).sum := by decide
  have hdescent : baseEnd_4442844 < baseStart_4442844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442876 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_4442876 : Nat := 118140960795 + 4442876 * 2 ^ 59
def prefixEnd_4442876 : Nat := 4983230072969 + 3 ^ 40 * 4442876 * 2
def baseEnd_4442876 : Nat := 760443625441688153639197

theorem tailTrace_4442876 : CollatzResearch.WordTrace tailWord_4442876 prefixEnd_4442876 760443625441688153639197 := by
  unfold tailWord_4442876
  simp only [CollatzResearch.WordTrace]
  refine ⟨81022500126113254828062241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108030000168151006437416321 81022500126113254828062241)
  ·
    refine ⟨60766875094584941121046681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81022500126113254828062241 60766875094584941121046681)
    ·
      refine ⟨45575156320938705840785011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60766875094584941121046681 45575156320938705840785011)
      ·
        refine ⟨68362734481408058761177517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45575156320938705840785011 68362734481408058761177517)
        ·
          refine ⟨25636025430528022035441569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68362734481408058761177517 25636025430528022035441569)
          ·
            refine ⟨19227019072896016526581177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25636025430528022035441569 19227019072896016526581177)
            ·
              refine ⟨14420264304672012394935883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19227019072896016526581177 14420264304672012394935883)
              ·
                refine ⟨21630396457008018592403825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14420264304672012394935883 21630396457008018592403825)
                ·
                  refine ⟨16222797342756013944302869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21630396457008018592403825 16222797342756013944302869)
                  ·
                    refine ⟨760443625441688153639197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16222797342756013944302869 760443625441688153639197)
                    ·
                      rfl

theorem cell23_4442876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_4442876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442876 prefixEnd_4442876 := by exact prefixLift 4442876
  have htrace : WordTrace (prefixWord ++ tailWord_4442876) baseStart_4442876 baseEnd_4442876 := by
    simpa [prefixWord, tailWord_4442876, baseEnd_4442876] using wordTrace_append hprefix tailTrace_4442876
  have hstable : (prefixWord ++ tailWord_4442876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442876).length < 2 ^ (prefixWord ++ tailWord_4442876).sum := by decide
  have hdescent : baseEnd_4442876 < baseStart_4442876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442887 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4442887 : Nat := 118140960795 + 4442887 * 2 ^ 59
def prefixEnd_4442887 : Nat := 4983230072969 + 3 ^ 40 * 4442887 * 2
def baseEnd_4442887 : Nat := 2281336524612263917880041

theorem tailTrace_4442887 : CollatzResearch.WordTrace tailWord_4442887 prefixEnd_4442887 2281336524612263917880041 := by
  unfold tailWord_4442887
  simp only [CollatzResearch.WordTrace]
  refine ⟨162045401455186658534774915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108030267636791105689849943 162045401455186658534774915)
  ·
    refine ⟨243068102182779987802162373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162045401455186658534774915 243068102182779987802162373)
    ·
      refine ⟨45575269159271247712905445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243068102182779987802162373 45575269159271247712905445)
      ·
        refine ⟨8545362967363358946169771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45575269159271247712905445 8545362967363358946169771)
        ·
          refine ⟨12818044451045038419254657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8545362967363358946169771 12818044451045038419254657)
          ·
            refine ⟨9613533338283778814440993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12818044451045038419254657 9613533338283778814440993)
            ·
              refine ⟨7210150003712834110830745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9613533338283778814440993 7210150003712834110830745)
              ·
                refine ⟨5407612502784625583123059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7210150003712834110830745 5407612502784625583123059)
                ·
                  refine ⟨8111418754176938374684589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407612502784625583123059 8111418754176938374684589)
                  ·
                    refine ⟨3041782032816351890506721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8111418754176938374684589 3041782032816351890506721)
                    ·
                      refine ⟨2281336524612263917880041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041782032816351890506721 2281336524612263917880041)
                      ·
                        rfl

theorem cell23_4442887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4442887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442887 prefixEnd_4442887 := by exact prefixLift 4442887
  have htrace : WordTrace (prefixWord ++ tailWord_4442887) baseStart_4442887 baseEnd_4442887 := by
    simpa [prefixWord, tailWord_4442887, baseEnd_4442887] using wordTrace_append hprefix tailTrace_4442887
  have hstable : (prefixWord ++ tailWord_4442887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442887).length < 2 ^ (prefixWord ++ tailWord_4442887).sum := by decide
  have hdescent : baseEnd_4442887 < baseStart_4442887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442903 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_4442903 : Nat := 118140960795 + 4442903 * 2 ^ 59
def prefixEnd_4442903 : Nat := 4983230072969 + 3 ^ 40 * 4442903 * 2
def baseEnd_4442903 : Nat := 2281344740302735855279967

theorem tailTrace_4442903 : CollatzResearch.WordTrace tailWord_4442903 prefixEnd_4442903 2281344740302735855279967 := by
  unfold tailWord_4442903
  simp only [CollatzResearch.WordTrace]
  refine ⟨162045985023128693267357363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108030656682085795511571575 162045985023128693267357363)
  ·
    refine ⟨243068977534693039901036045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162045985023128693267357363 243068977534693039901036045)
    ·
      refine ⟨91150866575509889962888517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243068977534693039901036045 91150866575509889962888517)
      ·
        refine ⟨17090787482908104368041597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91150866575509889962888517 17090787482908104368041597)
        ·
          refine ⟨6409045306090539138015599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17090787482908104368041597 6409045306090539138015599)
          ·
            refine ⟨9613567959135808707023399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6409045306090539138015599 9613567959135808707023399)
            ·
              refine ⟨14420351938703713060535099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9613567959135808707023399 14420351938703713060535099)
              ·
                refine ⟨21630527908055569590802649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14420351938703713060535099 21630527908055569590802649)
                ·
                  refine ⟨16222895931041677193101987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21630527908055569590802649 16222895931041677193101987)
                  ·
                    refine ⟨24334343896562515789652981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16222895931041677193101987 24334343896562515789652981)
                    ·
                      refine ⟨2281344740302735855279967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24334343896562515789652981 2281344740302735855279967)
                      ·
                        rfl

theorem cell23_4442903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_4442903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442903 prefixEnd_4442903 := by exact prefixLift 4442903
  have htrace : WordTrace (prefixWord ++ tailWord_4442903) baseStart_4442903 baseEnd_4442903 := by
    simpa [prefixWord, tailWord_4442903, baseEnd_4442903] using wordTrace_append hprefix tailTrace_4442903
  have hstable : (prefixWord ++ tailWord_4442903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442903).length < 2 ^ (prefixWord ++ tailWord_4442903).sum := by decide
  have hdescent : baseEnd_4442903 < baseStart_4442903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442936 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_4442936 : Nat := 118140960795 + 4442936 * 2 ^ 59
def prefixEnd_4442936 : Nat := 4983230072969 + 3 ^ 40 * 4442936 * 2
def baseEnd_4442936 : Nat := 760453895054778075389105

theorem tailTrace_4442936 : CollatzResearch.WordTrace tailWord_4442936 prefixEnd_4442936 760453895054778075389105 := by
  unfold tailWord_4442936
  simp only [CollatzResearch.WordTrace]
  refine ⟨81023594316004569951654331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108031459088006093268872441 81023594316004569951654331)
  ·
    refine ⟨121535391474006854927481497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81023594316004569951654331 121535391474006854927481497)
    ·
      refine ⟨91151543605505141195611123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121535391474006854927481497 91151543605505141195611123)
      ·
        refine ⟨136727315408257711793416685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91151543605505141195611123 136727315408257711793416685)
        ·
          refine ⟨51272743278096641922531257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136727315408257711793416685 51272743278096641922531257)
          ·
            refine ⟨38454557458572481441898443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51272743278096641922531257 38454557458572481441898443)
            ·
              refine ⟨57681836187858722162847665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38454557458572481441898443 57681836187858722162847665)
              ·
                refine ⟨43261377140894041622135749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57681836187858722162847665 43261377140894041622135749)
                ·
                  refine ⟨8111508213917632804150453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43261377140894041622135749 8111508213917632804150453)
                  ·
                    refine ⟨760453895054778075389105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8111508213917632804150453 760453895054778075389105)
                    ·
                      rfl

theorem cell23_4442936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_4442936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442936 prefixEnd_4442936 := by exact prefixLift 4442936
  have htrace : WordTrace (prefixWord ++ tailWord_4442936) baseStart_4442936 baseEnd_4442936 := by
    simpa [prefixWord, tailWord_4442936, baseEnd_4442936] using wordTrace_append hprefix tailTrace_4442936
  have hstable : (prefixWord ++ tailWord_4442936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442936).length < 2 ^ (prefixWord ++ tailWord_4442936).sum := by decide
  have hdescent : baseEnd_4442936 < baseStart_4442936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442953 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 2, 5]
def baseStart_4442953 : Nat := 118140960795 + 4442953 * 2 ^ 59
def prefixEnd_4442953 : Nat := 4983230072969 + 3 ^ 40 * 4442953 * 2
def baseEnd_4442953 : Nat := 760456804778486886551579

theorem tailTrace_4442953 : CollatzResearch.WordTrace tailWord_4442953 prefixEnd_4442953 760456804778486886551579 := by
  unfold tailWord_4442953
  simp only [CollatzResearch.WordTrace]
  refine ⟨162047808672947551806677513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108031872448631701204451675 162047808672947551806677513)
  ·
    refine ⟨121535856504710663855008135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162047808672947551806677513 121535856504710663855008135)
    ·
      refine ⟨182303784757065995782512203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121535856504710663855008135 182303784757065995782512203)
      ·
        refine ⟨273455677135598993673768305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182303784757065995782512203 273455677135598993673768305)
        ·
          refine ⟨205091757851699245255326229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273455677135598993673768305 205091757851699245255326229)
          ·
            refine ⟨9613676149298402121343417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205091757851699245255326229 9613676149298402121343417)
            ·
              refine ⟨7210257111973801591007563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9613676149298402121343417 7210257111973801591007563)
              ·
                refine ⟨10815385667960702386511345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7210257111973801591007563 10815385667960702386511345)
                ·
                  refine ⟨8111539250970526789883509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10815385667960702386511345 8111539250970526789883509)
                  ·
                    refine ⟨760456804778486886551579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8111539250970526789883509 760456804778486886551579)
                    ·
                      rfl

theorem cell23_4442953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_4442953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442953 prefixEnd_4442953 := by exact prefixLift 4442953
  have htrace : WordTrace (prefixWord ++ tailWord_4442953) baseStart_4442953 baseEnd_4442953 := by
    simpa [prefixWord, tailWord_4442953, baseEnd_4442953] using wordTrace_append hprefix tailTrace_4442953
  have hstable : (prefixWord ++ tailWord_4442953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442953).length < 2 ^ (prefixWord ++ tailWord_4442953).sum := by decide
  have hdescent : baseEnd_4442953 < baseStart_4442953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4442976 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_4442976 : Nat := 118140960795 + 4442976 * 2 ^ 59
def prefixEnd_4442976 : Nat := 4983230072969 + 3 ^ 40 * 4442976 * 2
def baseEnd_4442976 : Nat := 2281382224390514069667131

theorem tailTrace_4442976 : CollatzResearch.WordTrace tailWord_4442976 prefixEnd_4442976 2281382224390514069667131 := by
  unfold tailWord_4442976
  simp only [CollatzResearch.WordTrace]
  refine ⟨81024323775932113367382391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108032431701242817823176521 81024323775932113367382391)
  ·
    refine ⟨121536485663898170051073587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81024323775932113367382391 121536485663898170051073587)
    ·
      refine ⟨182304728495847255076610381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121536485663898170051073587 182304728495847255076610381)
      ·
        refine ⟨68364273185942720653728893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182304728495847255076610381 68364273185942720653728893)
        ·
          refine ⟨25636602444728520245148335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68364273185942720653728893 25636602444728520245148335)
          ·
            refine ⟨38454903667092780367722503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25636602444728520245148335 38454903667092780367722503)
            ·
              refine ⟨57682355500639170551583755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38454903667092780367722503 57682355500639170551583755)
              ·
                refine ⟨86523533250958755827375633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57682355500639170551583755 86523533250958755827375633)
                ·
                  refine ⟨64892649938219066870531725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86523533250958755827375633 64892649938219066870531725)
                  ·
                    refine ⟨24334743726832150076449397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64892649938219066870531725 24334743726832150076449397)
                    ·
                      refine ⟨2281382224390514069667131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24334743726832150076449397 2281382224390514069667131)
                      ·
                        rfl

theorem cell23_4442976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_4442976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4442976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4442976 prefixEnd_4442976 := by exact prefixLift 4442976
  have htrace : WordTrace (prefixWord ++ tailWord_4442976) baseStart_4442976 baseEnd_4442976 := by
    simpa [prefixWord, tailWord_4442976, baseEnd_4442976] using wordTrace_append hprefix tailTrace_4442976
  have hstable : (prefixWord ++ tailWord_4442976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4442976).length < 2 ^ (prefixWord ++ tailWord_4442976).sum := by decide
  have hdescent : baseEnd_4442976 < baseStart_4442976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4442976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443017 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 1, 4]
def baseStart_4443017 : Nat := 118140960795 + 4443017 * 2 ^ 59
def prefixEnd_4443017 : Nat := 4983230072969 + 3 ^ 40 * 4443017 * 2
def baseEnd_4443017 : Nat := 760467759032449469751481

theorem tailTrace_4443017 : CollatzResearch.WordTrace tailWord_4443017 prefixEnd_4443017 760467759032449469751481 := by
  unfold tailWord_4443017
  simp only [CollatzResearch.WordTrace]
  refine ⟨162050142944715690737007305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108033428629810460491338203 162050142944715690737007305)
  ·
    refine ⟨121537607208536768052755479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162050142944715690737007305 121537607208536768052755479)
    ·
      refine ⟨182306410812805152079133219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121537607208536768052755479 182306410812805152079133219)
      ·
        refine ⟨273459616219207728118699829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182306410812805152079133219 273459616219207728118699829)
        ·
          refine ⟨25636839020550724511128109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 273459616219207728118699829 25636839020550724511128109)
          ·
            refine ⟨9613814632706521691673041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25636839020550724511128109 9613814632706521691673041)
            ·
              refine ⟨7210360974529891268754781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9613814632706521691673041 7210360974529891268754781)
              ·
                refine ⟨2703885365448709225783043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7210360974529891268754781 2703885365448709225783043)
                ·
                  refine ⟨4055828048173063838674565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703885365448709225783043 4055828048173063838674565)
                  ·
                    refine ⟨760467759032449469751481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055828048173063838674565 760467759032449469751481)
                    ·
                      rfl

theorem cell23_4443017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 4].length) (baseStart_4443017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443017 prefixEnd_4443017 := by exact prefixLift 4443017
  have htrace : WordTrace (prefixWord ++ tailWord_4443017) baseStart_4443017 baseEnd_4443017 := by
    simpa [prefixWord, tailWord_4443017, baseEnd_4443017] using wordTrace_append hprefix tailTrace_4443017
  have hstable : (prefixWord ++ tailWord_4443017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443017).length < 2 ^ (prefixWord ++ tailWord_4443017).sum := by decide
  have hdescent : baseEnd_4443017 < baseStart_4443017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443040 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 3, 1, 3]
def baseStart_4443040 : Nat := 118140960795 + 4443040 * 2 ^ 59
def prefixEnd_4443040 : Nat := 4983230072969 + 3 ^ 40 * 4443040 * 2
def baseEnd_4443040 : Nat := 2281415087152401819266837

theorem tailTrace_4443040 : CollatzResearch.WordTrace tailWord_4443040 prefixEnd_4443040 2281415087152401819266837 := by
  unfold tailWord_4443040
  simp only [CollatzResearch.WordTrace]
  refine ⟨81025490911816182832547287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108033987882421577110063049 81025490911816182832547287)
  ·
    refine ⟨121538236367724274248820931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81025490911816182832547287 121538236367724274248820931)
    ·
      refine ⟨182307354551586411373231397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121538236367724274248820931 182307354551586411373231397)
      ·
        refine ⟨34182628978422452132480887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182307354551586411373231397 34182628978422452132480887)
        ·
          refine ⟨51273943467633678198721331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34182628978422452132480887 51273943467633678198721331)
          ·
            refine ⟨76910915201450517298081997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51273943467633678198721331 76910915201450517298081997)
            ·
              refine ⟨28841593200543943986780749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76910915201450517298081997 28841593200543943986780749)
              ·
                refine ⟨10815597450203978995042781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28841593200543943986780749 10815597450203978995042781)
                ·
                  refine ⟨4055849043826492123141043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10815597450203978995042781 4055849043826492123141043)
                  ·
                    refine ⟨6083773565739738184711565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4055849043826492123141043 6083773565739738184711565)
                    ·
                      refine ⟨2281415087152401819266837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6083773565739738184711565 2281415087152401819266837)
                      ·
                        rfl

theorem cell23_4443040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_4443040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443040 prefixEnd_4443040 := by exact prefixLift 4443040
  have htrace : WordTrace (prefixWord ++ tailWord_4443040) baseStart_4443040 baseEnd_4443040 := by
    simpa [prefixWord, tailWord_4443040, baseEnd_4443040] using wordTrace_append hprefix tailTrace_4443040
  have hstable : (prefixWord ++ tailWord_4443040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443040).length < 2 ^ (prefixWord ++ tailWord_4443040).sum := by decide
  have hdescent : baseEnd_4443040 < baseStart_4443040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443047 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 6]
def baseStart_4443047 : Nat := 118140960795 + 4443047 * 2 ^ 59
def prefixEnd_4443047 : Nat := 4983230072969 + 3 ^ 40 * 4443047 * 2
def baseEnd_4443047 : Nat := 253490964612998143542145

theorem tailTrace_4443047 : CollatzResearch.WordTrace tailWord_4443047 prefixEnd_4443047 253490964612998143542145 := by
  unfold tailWord_4443047
  simp only [CollatzResearch.WordTrace]
  refine ⟨162051237134607005860599395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108034158089738003907066263 162051237134607005860599395)
  ·
    refine ⟨243076855701910508790899093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162051237134607005860599395 243076855701910508790899093)
    ·
      refine ⟨11394227611027055099573395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 243076855701910508790899093 11394227611027055099573395)
      ·
        refine ⟨17091341416540582649360093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11394227611027055099573395 17091341416540582649360093)
        ·
          refine ⟨6409253031202718493510035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17091341416540582649360093 6409253031202718493510035)
          ·
            refine ⟨9613879546804077740265053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6409253031202718493510035 9613879546804077740265053)
            ·
              refine ⟨3605204830051529152599395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9613879546804077740265053 3605204830051529152599395)
              ·
                refine ⟨5407807245077293728899093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605204830051529152599395 5407807245077293728899093)
                ·
                  refine ⟨253490964612998143542145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5407807245077293728899093 253490964612998143542145)
                  ·
                    rfl

theorem cell23_4443047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 6].length) (baseStart_4443047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443047 prefixEnd_4443047 := by exact prefixLift 4443047
  have htrace : WordTrace (prefixWord ++ tailWord_4443047) baseStart_4443047 baseEnd_4443047 := by
    simpa [prefixWord, tailWord_4443047, baseEnd_4443047] using wordTrace_append hprefix tailTrace_4443047
  have hstable : (prefixWord ++ tailWord_4443047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443047).length < 2 ^ (prefixWord ++ tailWord_4443047).sum := by decide
  have hdescent : baseEnd_4443047 < baseStart_4443047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443063 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_4443063 : Nat := 118140960795 + 4443063 * 2 ^ 59
def prefixEnd_4443063 : Nat := 4983230072969 + 3 ^ 40 * 4443063 * 2
def baseEnd_4443063 : Nat := 2281426897207455229279231

theorem tailTrace_4443063 : CollatzResearch.WordTrace tailWord_4443063 prefixEnd_4443063 2281426897207455229279231 := by
  unfold tailWord_4443063
  simp only [CollatzResearch.WordTrace]
  refine ⟨162051820702549040593181843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108034547135032693728787895 162051820702549040593181843)
  ·
    refine ⟨243077731053823560889772765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162051820702549040593181843 243077731053823560889772765)
    ·
      refine ⟨91154149145183835333664787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243077731053823560889772765 91154149145183835333664787)
      ·
        refine ⟨136731223717775753000497181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91154149145183835333664787 136731223717775753000497181)
        ·
          refine ⟨51274208894165907375186443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136731223717775753000497181 51274208894165907375186443)
          ·
            refine ⟨76911313341248861062779665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51274208894165907375186443 76911313341248861062779665)
            ·
              refine ⟨57683485005936645797084749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76911313341248861062779665 57683485005936645797084749)
              ·
                refine ⟨21631306877226242173906781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57683485005936645797084749 21631306877226242173906781)
                ·
                  refine ⟨8111740078959840815215043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21631306877226242173906781 8111740078959840815215043)
                  ·
                    refine ⟨12167610118439761222822565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8111740078959840815215043 12167610118439761222822565)
                    ·
                      refine ⟨2281426897207455229279231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12167610118439761222822565 2281426897207455229279231)
                      ·
                        rfl

theorem cell23_4443063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_4443063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443063 prefixEnd_4443063 := by exact prefixLift 4443063
  have htrace : WordTrace (prefixWord ++ tailWord_4443063) baseStart_4443063 baseEnd_4443063 := by
    simpa [prefixWord, tailWord_4443063, baseEnd_4443063] using wordTrace_append hprefix tailTrace_4443063
  have hstable : (prefixWord ++ tailWord_4443063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443063).length < 2 ^ (prefixWord ++ tailWord_4443063).sum := by decide
  have hdescent : baseEnd_4443063 < baseStart_4443063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443078 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4443078 : Nat := 118140960795 + 4443078 * 2 ^ 59
def prefixEnd_4443078 : Nat := 4983230072969 + 3 ^ 40 * 4443078 * 2
def baseEnd_4443078 : Nat := 2281434599417272670591663

theorem tailTrace_4443078 : CollatzResearch.WordTrace tailWord_4443078 prefixEnd_4443078 2281434599417272670591663 := by
  unfold tailWord_4443078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064136493671709317343059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108034911864996465436651925 5064136493671709317343059)
  ·
    refine ⟨7596204740507563976014589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5064136493671709317343059 7596204740507563976014589)
    ·
      refine ⟨2848576777690336491005471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7596204740507563976014589 2848576777690336491005471)
      ·
        refine ⟨4272865166535504736508207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848576777690336491005471 4272865166535504736508207)
        ·
          refine ⟨6409297749803257104762311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272865166535504736508207 6409297749803257104762311)
          ·
            refine ⟨9613946624704885657143467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6409297749803257104762311 9613946624704885657143467)
            ·
              refine ⟨14420919937057328485715201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9613946624704885657143467 14420919937057328485715201)
              ·
                refine ⟨10815689952792996364286401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14420919937057328485715201 10815689952792996364286401)
                ·
                  refine ⟨8111767464594747273214801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10815689952792996364286401 8111767464594747273214801)
                  ·
                    refine ⟨6083825598446060454911101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8111767464594747273214801 6083825598446060454911101)
                    ·
                      refine ⟨2281434599417272670591663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6083825598446060454911101 2281434599417272670591663)
                      ·
                        rfl

theorem cell23_4443078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4443078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443078 prefixEnd_4443078 := by exact prefixLift 4443078
  have htrace : WordTrace (prefixWord ++ tailWord_4443078) baseStart_4443078 baseEnd_4443078 := by
    simpa [prefixWord, tailWord_4443078, baseEnd_4443078] using wordTrace_append hprefix tailTrace_4443078
  have hstable : (prefixWord ++ tailWord_4443078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443078).length < 2 ^ (prefixWord ++ tailWord_4443078).sum := by decide
  have hdescent : baseEnd_4443078 < baseStart_4443078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443083 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5]
def baseStart_4443083 : Nat := 118140960795 + 4443083 * 2 ^ 59
def prefixEnd_4443083 : Nat := 4983230072969 + 3 ^ 40 * 4443083 * 2
def baseEnd_4443083 : Nat := 2281437166820545151029139

theorem tailTrace_4443083 : CollatzResearch.WordTrace tailWord_4443083 prefixEnd_4443083 2281437166820545151029139 := by
  unfold tailWord_4443083
  simp only [CollatzResearch.WordTrace]
  refine ⟨162052550162476584008909903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108035033441651056005939935 162052550162476584008909903)
  ·
    refine ⟨243078825243714876013364855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162052550162476584008909903 243078825243714876013364855)
    ·
      refine ⟨364618237865572314020047283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243078825243714876013364855 364618237865572314020047283)
      ·
        refine ⟨546927356798358471030070925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364618237865572314020047283 546927356798358471030070925)
        ·
          refine ⟨205097758799384426636276597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 546927356798358471030070925 205097758799384426636276597)
          ·
            refine ⟨19227914887442289997150931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 205097758799384426636276597 19227914887442289997150931)
            ·
              refine ⟨28841872331163434995726397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19227914887442289997150931 28841872331163434995726397)
              ·
                refine ⟨10815702124186288123397399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28841872331163434995726397 10815702124186288123397399)
                ·
                  refine ⟨16223553186279432185096099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10815702124186288123397399 16223553186279432185096099)
                  ·
                    refine ⟨24335329779419148277644149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16223553186279432185096099 24335329779419148277644149)
                    ·
                      refine ⟨2281437166820545151029139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24335329779419148277644149 2281437166820545151029139)
                      ·
                        rfl

theorem cell23_4443083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].length) (baseStart_4443083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443083 prefixEnd_4443083 := by exact prefixLift 4443083
  have htrace : WordTrace (prefixWord ++ tailWord_4443083) baseStart_4443083 baseEnd_4443083 := by
    simpa [prefixWord, tailWord_4443083, baseEnd_4443083] using wordTrace_append hprefix tailTrace_4443083
  have hstable : (prefixWord ++ tailWord_4443083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443083).length < 2 ^ (prefixWord ++ tailWord_4443083).sum := by decide
  have hdescent : baseEnd_4443083 < baseStart_4443083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443085 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4443085 : Nat := 118140960795 + 4443085 * 2 ^ 59
def prefixEnd_4443085 : Nat := 4983230072969 + 3 ^ 40 * 4443085 * 2
def baseEnd_4443085 : Nat := 760479397927284714401377

theorem tailTrace_4443085 : CollatzResearch.WordTrace tailWord_4443085 prefixEnd_4443085 760479397927284714401377 := by
  unfold tailWord_4443085
  simp only [CollatzResearch.WordTrace]
  refine ⟨162052623108469338350482709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108035082072312892233655139 162052623108469338350482709)
  ·
    refine ⟨7596216708209500235178877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 162052623108469338350482709 7596216708209500235178877)
    ·
      refine ⟨2848581265578562588192079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7596216708209500235178877 2848581265578562588192079)
      ·
        refine ⟨4272871898367843882288119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848581265578562588192079 4272871898367843882288119)
        ·
          refine ⟨6409307847551765823432179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272871898367843882288119 6409307847551765823432179)
          ·
            refine ⟨9613961771327648735148269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6409307847551765823432179 9613961771327648735148269)
            ·
              refine ⟨3605235664247868275680601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9613961771327648735148269 3605235664247868275680601)
              ·
                refine ⟨2703926748185901206760451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605235664247868275680601 2703926748185901206760451)
                ·
                  refine ⟨4055890122278851810140677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703926748185901206760451 4055890122278851810140677)
                  ·
                    refine ⟨760479397927284714401377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055890122278851810140677 760479397927284714401377)
                    ·
                      rfl

theorem cell23_4443085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4443085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443085 prefixEnd_4443085 := by exact prefixLift 4443085
  have htrace : WordTrace (prefixWord ++ tailWord_4443085) baseStart_4443085 baseEnd_4443085 := by
    simpa [prefixWord, tailWord_4443085, baseEnd_4443085] using wordTrace_append hprefix tailTrace_4443085
  have hstable : (prefixWord ++ tailWord_4443085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443085).length < 2 ^ (prefixWord ++ tailWord_4443085).sum := by decide
  have hdescent : baseEnd_4443085 < baseStart_4443085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443113 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_4443113 : Nat := 118140960795 + 4443113 * 2 ^ 59
def prefixEnd_4443113 : Nat := 4983230072969 + 3 ^ 40 * 4443113 * 2
def baseEnd_4443113 : Nat := 2281452571240180033654001

theorem tailTrace_4443113 : CollatzResearch.WordTrace tailWord_4443113 prefixEnd_4443113 2281452571240180033654001 := by
  unfold tailWord_4443113
  simp only [CollatzResearch.WordTrace]
  refine ⟨162053644352367899132501993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108035762901578599421667995 162053644352367899132501993)
  ·
    refine ⟨121540233264275924349376495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162053644352367899132501993 121540233264275924349376495)
    ·
      refine ⟨182310349896413886524064743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121540233264275924349376495 182310349896413886524064743)
      ·
        refine ⟨273465524844620829786097115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182310349896413886524064743 273465524844620829786097115)
        ·
          refine ⟨410198287266931244679145673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273465524844620829786097115 410198287266931244679145673)
          ·
            refine ⟨307648715450198433509359255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410198287266931244679145673 307648715450198433509359255)
            ·
              refine ⟨461473073175297650264038883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307648715450198433509359255 461473073175297650264038883)
              ·
                refine ⟨692209609762946475396058325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461473073175297650264038883 692209609762946475396058325)
                ·
                  refine ⟨16223662728819058017095117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 692209609762946475396058325 16223662728819058017095117)
                  ·
                    refine ⟨6083873523307146756410669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16223662728819058017095117 6083873523307146756410669)
                    ·
                      refine ⟨2281452571240180033654001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6083873523307146756410669 2281452571240180033654001)
                      ·
                        rfl

theorem cell23_4443113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_4443113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443113 prefixEnd_4443113 := by exact prefixLift 4443113
  have htrace : WordTrace (prefixWord ++ tailWord_4443113) baseStart_4443113 baseEnd_4443113 := by
    simpa [prefixWord, tailWord_4443113, baseEnd_4443113] using wordTrace_append hprefix tailTrace_4443113
  have hstable : (prefixWord ++ tailWord_4443113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443113).length < 2 ^ (prefixWord ++ tailWord_4443113).sum := by decide
  have hdescent : baseEnd_4443113 < baseStart_4443113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443130 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_4443130 : Nat := 118140960795 + 4443130 * 2 ^ 59
def prefixEnd_4443130 : Nat := 4983230072969 + 3 ^ 40 * 4443130 * 2
def baseEnd_4443130 : Nat := 2281461300411306467141423

theorem tailTrace_4443130 : CollatzResearch.WordTrace tailWord_4443130 prefixEnd_4443130 2281461300411306467141423 := by
  unfold tailWord_4443130
  simp only [CollatzResearch.WordTrace]
  refine ⟨40513566098326577758967711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108036176262204207357247229 40513566098326577758967711)
  ·
    refine ⟨60770349147489866638451567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40513566098326577758967711 60770349147489866638451567)
    ·
      refine ⟨91155523721234799957677351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60770349147489866638451567 91155523721234799957677351)
      ·
        refine ⟨136733285581852199936516027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91155523721234799957677351 136733285581852199936516027)
        ·
          refine ⟨205099928372778299904774041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136733285581852199936516027 205099928372778299904774041)
          ·
            refine ⟨153824946279583724928580531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205099928372778299904774041 153824946279583724928580531)
            ·
              refine ⟨230737419419375587392870797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153824946279583724928580531 230737419419375587392870797)
              ·
                refine ⟨86526532282265845272326549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230737419419375587392870797 86526532282265845272326549)
                ·
                  refine ⟨4055931200731211497140307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86526532282265845272326549 4055931200731211497140307)
                  ·
                    refine ⟨6083896801096817245710461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4055931200731211497140307 6083896801096817245710461)
                    ·
                      refine ⟨2281461300411306467141423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6083896801096817245710461 2281461300411306467141423)
                      ·
                        rfl

theorem cell23_4443130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_4443130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443130 prefixEnd_4443130 := by exact prefixLift 4443130
  have htrace : WordTrace (prefixWord ++ tailWord_4443130) baseStart_4443130 baseEnd_4443130 := by
    simpa [prefixWord, tailWord_4443130, baseEnd_4443130] using wordTrace_append hprefix tailTrace_4443130
  have hstable : (prefixWord ++ tailWord_4443130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443130).length < 2 ^ (prefixWord ++ tailWord_4443130).sum := by decide
  have hdescent : baseEnd_4443130 < baseStart_4443130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443134 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4443134 : Nat := 118140960795 + 4443134 * 2 ^ 59
def prefixEnd_4443134 : Nat := 4983230072969 + 3 ^ 40 * 4443134 * 2
def baseEnd_4443134 : Nat := 2281463354333924451491405

theorem tailTrace_4443134 : CollatzResearch.WordTrace tailWord_4443134 prefixEnd_4443134 2281463354333924451491405 := by
  unfold tailWord_4443134
  simp only [CollatzResearch.WordTrace]
  refine ⟨20256801285661477464877057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108036273523527879812677637 20256801285661477464877057)
  ·
    refine ⟨15192600964246108098657793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20256801285661477464877057 15192600964246108098657793)
    ·
      refine ⟨11394450723184581073993345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15192600964246108098657793 11394450723184581073993345)
      ·
        refine ⟨8545838042388435805495009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11394450723184581073993345 8545838042388435805495009)
        ·
          refine ⟨6409378531791326854121257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8545838042388435805495009 6409378531791326854121257)
          ·
            refine ⟨4807033898843495140590943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6409378531791326854121257 4807033898843495140590943)
            ·
              refine ⟨7210550848265242710886415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807033898843495140590943 7210550848265242710886415)
              ·
                refine ⟨10815826272397864066329623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7210550848265242710886415 10815826272397864066329623)
                ·
                  refine ⟨16223739408596796099494435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10815826272397864066329623 16223739408596796099494435)
                  ·
                    refine ⟨24335609112895194149241653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16223739408596796099494435 24335609112895194149241653)
                    ·
                      refine ⟨2281463354333924451491405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24335609112895194149241653 2281463354333924451491405)
                      ·
                        rfl

theorem cell23_4443134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4443134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443134 prefixEnd_4443134 := by exact prefixLift 4443134
  have htrace : WordTrace (prefixWord ++ tailWord_4443134) baseStart_4443134 baseEnd_4443134 := by
    simpa [prefixWord, tailWord_4443134, baseEnd_4443134] using wordTrace_append hprefix tailTrace_4443134
  have hstable : (prefixWord ++ tailWord_4443134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443134).length < 2 ^ (prefixWord ++ tailWord_4443134).sum := by decide
  have hdescent : baseEnd_4443134 < baseStart_4443134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443147 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 3]
def baseStart_4443147 : Nat := 118140960795 + 4443147 * 2 ^ 59
def prefixEnd_4443147 : Nat := 4983230072969 + 3 ^ 40 * 4443147 * 2
def baseEnd_4443147 : Nat := 2281470029582432900628845

theorem tailTrace_4443147 : CollatzResearch.WordTrace tailWord_4443147 prefixEnd_4443147 2281470029582432900628845 := by
  unfold tailWord_4443147
  simp only [CollatzResearch.WordTrace]
  refine ⟨162054884434244722939239695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108036589622829815292826463 162054884434244722939239695)
  ·
    refine ⟨243082326651367084408859543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162054884434244722939239695 243082326651367084408859543)
    ·
      refine ⟨364623489977050626613289315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243082326651367084408859543 364623489977050626613289315)
      ·
        refine ⟨546935234965575939919933973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364623489977050626613289315 546935234965575939919933973)
        ·
          refine ⟨25637589139011372183746905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 546935234965575939919933973 25637589139011372183746905)
          ·
            refine ⟨19228191854258529137810179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25637589139011372183746905 19228191854258529137810179)
            ·
              refine ⟨28842287781387793706715269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19228191854258529137810179 28842287781387793706715269)
              ·
                refine ⟨5407928959010211320009113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28842287781387793706715269 5407928959010211320009113)
                ·
                  refine ⟨4055946719257658490006835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5407928959010211320009113 4055946719257658490006835)
                  ·
                    refine ⟨6083920078886487735010253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4055946719257658490006835 6083920078886487735010253)
                    ·
                      refine ⟨2281470029582432900628845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6083920078886487735010253 2281470029582432900628845)
                      ·
                        rfl

theorem cell23_4443147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 3].length) (baseStart_4443147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443147 prefixEnd_4443147 := by exact prefixLift 4443147
  have htrace : WordTrace (prefixWord ++ tailWord_4443147) baseStart_4443147 baseEnd_4443147 := by
    simpa [prefixWord, tailWord_4443147, baseEnd_4443147] using wordTrace_append hprefix tailTrace_4443147
  have hstable : (prefixWord ++ tailWord_4443147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443147).length < 2 ^ (prefixWord ++ tailWord_4443147).sum := by decide
  have hdescent : baseEnd_4443147 < baseStart_4443147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443148 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 1, 2, 2]
def baseStart_4443148 : Nat := 118140960795 + 4443148 * 2 ^ 59
def prefixEnd_4443148 : Nat := 4983230072969 + 3 ^ 40 * 4443148 * 2
def baseEnd_4443148 : Nat := 2281470543063087396716341

theorem tailTrace_4443148 : CollatzResearch.WordTrace tailWord_4443148 prefixEnd_4443148 2281470543063087396716341 := by
  unfold tailWord_4443148
  simp only [CollatzResearch.WordTrace]
  refine ⟨81027460453620550055013049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108036613938160733406684065 81027460453620550055013049)
  ·
    refine ⟨60770595340215412541259787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81027460453620550055013049 60770595340215412541259787)
    ·
      refine ⟨91155893010323118811889681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60770595340215412541259787 91155893010323118811889681)
      ·
        refine ⟨68366919757742339108917261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91155893010323118811889681 68366919757742339108917261)
        ·
          refine ⟨25637594909153377165843973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68366919757742339108917261 25637594909153377165843973)
          ·
            refine ⟨4807049045466258218595745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25637594909153377165843973 4807049045466258218595745)
            ·
              refine ⟨3605286784099693663946809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807049045466258218595745 3605286784099693663946809)
              ·
                refine ⟨2703965088074770247960107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605286784099693663946809 2703965088074770247960107)
                ·
                  refine ⟨4055947632112155371940161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703965088074770247960107 4055947632112155371940161)
                  ·
                    refine ⟨3041960724084116528955121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4055947632112155371940161 3041960724084116528955121)
                    ·
                      refine ⟨2281470543063087396716341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041960724084116528955121 2281470543063087396716341)
                      ·
                        rfl

theorem cell23_4443148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_4443148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443148 prefixEnd_4443148 := by exact prefixLift 4443148
  have htrace : WordTrace (prefixWord ++ tailWord_4443148) baseStart_4443148 baseEnd_4443148 := by
    simpa [prefixWord, tailWord_4443148, baseEnd_4443148] using wordTrace_append hprefix tailTrace_4443148
  have hstable : (prefixWord ++ tailWord_4443148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443148).length < 2 ^ (prefixWord ++ tailWord_4443148).sum := by decide
  have hdescent : baseEnd_4443148 < baseStart_4443148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443157 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_4443157 : Nat := 118140960795 + 4443157 * 2 ^ 59
def prefixEnd_4443157 : Nat := 4983230072969 + 3 ^ 40 * 4443157 * 2
def baseEnd_4443157 : Nat := 2281475164388977861503799

theorem tailTrace_4443157 : CollatzResearch.WordTrace tailWord_4443157 prefixEnd_4443157 2281475164388977861503799 := by
  unfold tailWord_4443157
  simp only [CollatzResearch.WordTrace]
  refine ⟨162055249164208494647103725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108036832776138996431402483 162055249164208494647103725)
  ·
    refine ⟨60770718436578185492663897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162055249164208494647103725 60770718436578185492663897)
    ·
      refine ⟨45578038827433639119497923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60770718436578185492663897 45578038827433639119497923)
      ·
        refine ⟨68367058241150458679246885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45578038827433639119497923 68367058241150458679246885)
        ·
          refine ⟨12818823420215711002358791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68367058241150458679246885 12818823420215711002358791)
          ·
            refine ⟨19228235130323566503538187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12818823420215711002358791 19228235130323566503538187)
            ·
              refine ⟨28842352695485349755307281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19228235130323566503538187 28842352695485349755307281)
              ·
                refine ⟨21631764521614012316480461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28842352695485349755307281 21631764521614012316480461)
                ·
                  refine ⟨8111911695605254618680173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21631764521614012316480461 8111911695605254618680173)
                  ·
                    refine ⟨3041966885851970482005065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8111911695605254618680173 3041966885851970482005065)
                    ·
                      refine ⟨2281475164388977861503799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041966885851970482005065 2281475164388977861503799)
                      ·
                        rfl

theorem cell23_4443157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_4443157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443157 prefixEnd_4443157 := by exact prefixLift 4443157
  have htrace : WordTrace (prefixWord ++ tailWord_4443157) baseStart_4443157 baseEnd_4443157 := by
    simpa [prefixWord, tailWord_4443157, baseEnd_4443157] using wordTrace_append hprefix tailTrace_4443157
  have hstable : (prefixWord ++ tailWord_4443157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443157).length < 2 ^ (prefixWord ++ tailWord_4443157).sum := by decide
  have hdescent : baseEnd_4443157 < baseStart_4443157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443187 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 4, 2, 2]
def baseStart_4443187 : Nat := 118140960795 + 4443187 * 2 ^ 59
def prefixEnd_4443187 : Nat := 4983230072969 + 3 ^ 40 * 4443187 * 2
def baseEnd_4443187 : Nat := 2281490568808612744128661

theorem tailTrace_4443187 : CollatzResearch.WordTrace tailWord_4443187 prefixEnd_4443187 2281490568808612744128661 := by
  unfold tailWord_4443187
  simp only [CollatzResearch.WordTrace]
  refine ⟨162056343354099809770695815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108037562236066539847130543 162056343354099809770695815)
  ·
    refine ⟨243084515031149714656043723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162056343354099809770695815 243084515031149714656043723)
    ·
      refine ⟨364626772546724571984065585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243084515031149714656043723 364626772546724571984065585)
      ·
        refine ⟨273470079410043428988049189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364626772546724571984065585 273470079410043428988049189)
        ·
          refine ⟨51275639889383142935259223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273470079410043428988049189 51275639889383142935259223)
          ·
            refine ⟨76913459834074714402888835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51275639889383142935259223 76913459834074714402888835)
            ·
              refine ⟨115370189751112071604333253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76913459834074714402888835 115370189751112071604333253)
              ·
                refine ⟨21631910578333513425812485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115370189751112071604333253 21631910578333513425812485)
                ·
                  refine ⟨4055983233437533767339841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21631910578333513425812485 4055983233437533767339841)
                  ·
                    refine ⟨3041987425078150325504881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4055983233437533767339841 3041987425078150325504881)
                    ·
                      refine ⟨2281490568808612744128661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3041987425078150325504881 2281490568808612744128661)
                      ·
                        rfl

theorem cell23_4443187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 2, 2].length) (baseStart_4443187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443187 prefixEnd_4443187 := by exact prefixLift 4443187
  have htrace : WordTrace (prefixWord ++ tailWord_4443187) baseStart_4443187 baseEnd_4443187 := by
    simpa [prefixWord, tailWord_4443187, baseEnd_4443187] using wordTrace_append hprefix tailTrace_4443187
  have hstable : (prefixWord ++ tailWord_4443187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443187).length < 2 ^ (prefixWord ++ tailWord_4443187).sum := by decide
  have hdescent : baseEnd_4443187 < baseStart_4443187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443221 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_4443221 : Nat := 118140960795 + 4443221 * 2 ^ 59
def prefixEnd_4443221 : Nat := 4983230072969 + 3 ^ 40 * 4443221 * 2
def baseEnd_4443221 : Nat := 2281508027150865611103505

theorem tailTrace_4443221 : CollatzResearch.WordTrace tailWord_4443221 prefixEnd_4443221 2281508027150865611103505 := by
  unfold tailWord_4443221
  simp only [CollatzResearch.WordTrace]
  refine ⟨162057583435976633577433517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108038388957317755718289011 162057583435976633577433517)
  ·
    refine ⟨60771593788491237591537569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162057583435976633577433517 60771593788491237591537569)
    ·
      refine ⟨45578695341368428193653177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60771593788491237591537569 45578695341368428193653177)
      ·
        refine ⟨34184021506026321145239883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45578695341368428193653177 34184021506026321145239883)
        ·
          refine ⟨51276032259039481717859825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34184021506026321145239883 51276032259039481717859825)
          ·
            refine ⟨38457024194279611288394869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51276032259039481717859825 38457024194279611288394869)
            ·
              refine ⟨3605346018213713558287019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38457024194279611288394869 3605346018213713558287019)
              ·
                refine ⟨5408019027320570337430529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605346018213713558287019 5408019027320570337430529)
                ·
                  refine ⟨4056014270490427753072897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5408019027320570337430529 4056014270490427753072897)
                  ·
                    refine ⟨3042010702867820814804673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4056014270490427753072897 3042010702867820814804673)
                    ·
                      refine ⟨2281508027150865611103505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042010702867820814804673 2281508027150865611103505)
                      ·
                        rfl

theorem cell23_4443221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_4443221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443221 prefixEnd_4443221 := by exact prefixLift 4443221
  have htrace : WordTrace (prefixWord ++ tailWord_4443221) baseStart_4443221 baseEnd_4443221 := by
    simpa [prefixWord, tailWord_4443221, baseEnd_4443221] using wordTrace_append hprefix tailTrace_4443221
  have hstable : (prefixWord ++ tailWord_4443221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443221).length < 2 ^ (prefixWord ++ tailWord_4443221).sum := by decide
  have hdescent : baseEnd_4443221 < baseStart_4443221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443250 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4443250 : Nat := 118140960795 + 4443250 * 2 ^ 59
def prefixEnd_4443250 : Nat := 4983230072969 + 3 ^ 40 * 4443250 * 2
def baseEnd_4443250 : Nat := 2281522918089845997640871

theorem tailTrace_4443250 : CollatzResearch.WordTrace tailWord_4443250 prefixEnd_4443250 2281522918089845997640871 := by
  unfold tailWord_4443250
  simp only [CollatzResearch.WordTrace]
  refine ⟨40514660288217892882559801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108039094101914381020159469 40514660288217892882559801)
  ·
    refine ⟨30385995216163419661919851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40514660288217892882559801 30385995216163419661919851)
    ·
      refine ⟨45578992824245129492879777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30385995216163419661919851 45578992824245129492879777)
      ·
        refine ⟨34184244618183847119659833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45578992824245129492879777 34184244618183847119659833)
        ·
          refine ⟨25638183463637885339744875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34184244618183847119659833 25638183463637885339744875)
          ·
            refine ⟨38457275195456828009617313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25638183463637885339744875 38457275195456828009617313)
            ·
              refine ⟨28842956396592621007212985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38457275195456828009617313 28842956396592621007212985)
              ·
                refine ⟨21632217297444465755409739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28842956396592621007212985 21632217297444465755409739)
                ·
                  refine ⟨32448325946166698633114609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21632217297444465755409739 32448325946166698633114609)
                  ·
                    refine ⟨24336244459625023974835957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32448325946166698633114609 24336244459625023974835957)
                    ·
                      refine ⟨2281522918089845997640871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24336244459625023974835957 2281522918089845997640871)
                      ·
                        rfl

theorem cell23_4443250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4443250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443250 prefixEnd_4443250 := by exact prefixLift 4443250
  have htrace : WordTrace (prefixWord ++ tailWord_4443250) baseStart_4443250 baseEnd_4443250 := by
    simpa [prefixWord, tailWord_4443250, baseEnd_4443250] using wordTrace_append hprefix tailTrace_4443250
  have hstable : (prefixWord ++ tailWord_4443250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443250).length < 2 ^ (prefixWord ++ tailWord_4443250).sum := by decide
  have hdescent : baseEnd_4443250 < baseStart_4443250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443257 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 2, 5]
def baseStart_4443257 : Nat := 118140960795 + 4443257 * 2 ^ 59
def prefixEnd_4443257 : Nat := 4983230072969 + 3 ^ 40 * 4443257 * 2
def baseEnd_4443257 : Nat := 760508837484809156751113

theorem tailTrace_4443257 : CollatzResearch.WordTrace tailWord_4443257 prefixEnd_4443257 760508837484809156751113 := by
  unfold tailWord_4443257
  simp only [CollatzResearch.WordTrace]
  refine ⟨162058896463846211725744025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108039264309230807817162683 162058896463846211725744025)
  ·
    refine ⟨121544172347884658794308019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162058896463846211725744025 121544172347884658794308019)
    ·
      refine ⟨182316258521826988191462029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121544172347884658794308019 182316258521826988191462029)
      ·
        refine ⟨68368596945685120571798261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182316258521826988191462029 68368596945685120571798261)
        ·
          refine ⟨6409555963657980053606087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68368596945685120571798261 6409555963657980053606087)
          ·
            refine ⟨9614333945486970080409131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6409555963657980053606087 9614333945486970080409131)
            ·
              refine ⟨14421500918230455120613697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9614333945486970080409131 14421500918230455120613697)
              ·
                refine ⟨10816125688672841340460273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14421500918230455120613697 10816125688672841340460273)
                ·
                  refine ⟨8112094266504631005345205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10816125688672841340460273 8112094266504631005345205)
                  ·
                    refine ⟨760508837484809156751113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8112094266504631005345205 760508837484809156751113)
                    ·
                      rfl

theorem cell23_4443257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_4443257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443257 prefixEnd_4443257 := by exact prefixLift 4443257
  have htrace : WordTrace (prefixWord ++ tailWord_4443257) baseStart_4443257 baseEnd_4443257 := by
    simpa [prefixWord, tailWord_4443257, baseEnd_4443257] using wordTrace_append hprefix tailTrace_4443257
  have hstable : (prefixWord ++ tailWord_4443257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443257).length < 2 ^ (prefixWord ++ tailWord_4443257).sum := by decide
  have hdescent : baseEnd_4443257 < baseStart_4443257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443280 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_4443280 : Nat := 118140960795 + 4443280 * 2 ^ 59
def prefixEnd_4443280 : Nat := 4983230072969 + 3 ^ 40 * 4443280 * 2
def baseEnd_4443280 : Nat := 2281538322509480880265733

theorem tailTrace_4443280 : CollatzResearch.WordTrace tailWord_4443280 prefixEnd_4443280 2281538322509480880265733 := by
  unfold tailWord_4443280
  simp only [CollatzResearch.WordTrace]
  refine ⟨81029867671381443326915647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108039823561841924435887529 81029867671381443326915647)
  ·
    refine ⟨121544801507072164990373471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81029867671381443326915647 121544801507072164990373471)
    ·
      refine ⟨182317202260608247485560207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121544801507072164990373471 182317202260608247485560207)
      ·
        refine ⟨273475803390912371228340311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182317202260608247485560207 273475803390912371228340311)
        ·
          refine ⟨410213705086368556842510467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273475803390912371228340311 410213705086368556842510467)
          ·
            refine ⟨615320557629552835263765701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410213705086368556842510467 615320557629552835263765701)
            ·
              refine ⟨115372604555541156611956069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 615320557629552835263765701 115372604555541156611956069)
              ·
                refine ⟨21632363354163966864741763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115372604555541156611956069 21632363354163966864741763)
                ·
                  refine ⟨32448545031245950297112645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21632363354163966864741763 32448545031245950297112645)
                  ·
                    refine ⟨6084102193358615680708621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32448545031245950297112645 6084102193358615680708621)
                    ·
                      refine ⟨2281538322509480880265733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084102193358615680708621 2281538322509480880265733)
                      ·
                        rfl

theorem cell23_4443280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_4443280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443280 prefixEnd_4443280 := by exact prefixLift 4443280
  have htrace : WordTrace (prefixWord ++ tailWord_4443280) baseStart_4443280 baseEnd_4443280 := by
    simpa [prefixWord, tailWord_4443280, baseEnd_4443280] using wordTrace_append hprefix tailTrace_4443280
  have hstable : (prefixWord ++ tailWord_4443280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443280).length < 2 ^ (prefixWord ++ tailWord_4443280).sum := by decide
  have hdescent : baseEnd_4443280 < baseStart_4443280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443294 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4443294 : Nat := 118140960795 + 4443294 * 2 ^ 59
def prefixEnd_4443294 : Nat := 4983230072969 + 3 ^ 40 * 4443294 * 2
def baseEnd_4443294 : Nat := 2281545511238643825490669

theorem tailTrace_4443294 : CollatzResearch.WordTrace tailWord_4443294 prefixEnd_4443294 2281545511238643825490669 := by
  unfold tailWord_4443294
  simp only [CollatzResearch.WordTrace]
  refine ⟨20257530745589020880605117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108040163976474778029893957 20257530745589020880605117)
  ·
    refine ⟨7596574029595882830226919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20257530745589020880605117 7596574029595882830226919)
    ·
      refine ⟨11394861044393824245340379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7596574029595882830226919 11394861044393824245340379)
      ·
        refine ⟨17092291566590736368010569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11394861044393824245340379 17092291566590736368010569)
        ·
          refine ⟨12819218674943052276007927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17092291566590736368010569 12819218674943052276007927)
          ·
            refine ⟨19228828012414578414011891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12819218674943052276007927 19228828012414578414011891)
            ·
              refine ⟨28843242018621867621017837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19228828012414578414011891 28843242018621867621017837)
              ·
                refine ⟨10816215756983200357881689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28843242018621867621017837 10816215756983200357881689)
                ·
                  refine ⟨8112161817737400268411267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10816215756983200357881689 8112161817737400268411267)
                  ·
                    refine ⟨12168242726606100402616901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8112161817737400268411267 12168242726606100402616901)
                    ·
                      refine ⟨2281545511238643825490669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12168242726606100402616901 2281545511238643825490669)
                      ·
                        rfl

theorem cell23_4443294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4443294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443294 prefixEnd_4443294 := by exact prefixLift 4443294
  have htrace : WordTrace (prefixWord ++ tailWord_4443294) baseStart_4443294 baseEnd_4443294 := by
    simpa [prefixWord, tailWord_4443294, baseEnd_4443294] using wordTrace_append hprefix tailTrace_4443294
  have hstable : (prefixWord ++ tailWord_4443294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443294).length < 2 ^ (prefixWord ++ tailWord_4443294).sum := by decide
  have hdescent : baseEnd_4443294 < baseStart_4443294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443321 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 1, 4]
def baseStart_4443321 : Nat := 118140960795 + 4443321 * 2 ^ 59
def prefixEnd_4443321 : Nat := 4983230072969 + 3 ^ 40 * 4443321 * 2
def baseEnd_4443321 : Nat := 760519791738771739951015

theorem tailTrace_4443321 : CollatzResearch.WordTrace tailWord_4443321 prefixEnd_4443321 760519791738771739951015 := by
  unfold tailWord_4443321
  simp only [CollatzResearch.WordTrace]
  refine ⟨162061230735614350656073817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108040820490409567104049211 162061230735614350656073817)
  ·
    refine ⟨121545923051710762992055363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162061230735614350656073817 121545923051710762992055363)
    ·
      refine ⟨182318884577566144488083045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121545923051710762992055363 182318884577566144488083045)
      ·
        refine ⟨34184790858293652091515571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182318884577566144488083045 34184790858293652091515571)
        ·
          refine ⟨51277186287440478137273357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34184790858293652091515571 51277186287440478137273357)
          ·
            refine ⟨19228944857790179301477509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51277186287440478137273357 19228944857790179301477509)
            ·
              refine ⟨3605427160835658619027033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19228944857790179301477509 3605427160835658619027033)
              ·
                refine ⟨2704070370626743964270275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605427160835658619027033 2704070370626743964270275)
                ·
                  refine ⟨4056105555940115946405413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704070370626743964270275 4056105555940115946405413)
                  ·
                    refine ⟨760519791738771739951015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4056105555940115946405413 760519791738771739951015)
                    ·
                      rfl

theorem cell23_4443321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 4].length) (baseStart_4443321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443321 prefixEnd_4443321 := by exact prefixLift 4443321
  have htrace : WordTrace (prefixWord ++ tailWord_4443321) baseStart_4443321 baseEnd_4443321 := by
    simpa [prefixWord, tailWord_4443321, baseEnd_4443321] using wordTrace_append hprefix tailTrace_4443321
  have hstable : (prefixWord ++ tailWord_4443321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443321).length < 2 ^ (prefixWord ++ tailWord_4443321).sum := by decide
  have hdescent : baseEnd_4443321 < baseStart_4443321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443348 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4443348 : Nat := 118140960795 + 4443348 * 2 ^ 59
def prefixEnd_4443348 : Nat := 4983230072969 + 3 ^ 40 * 4443348 * 2
def baseEnd_4443348 : Nat := 2281573239193986614215421

theorem tailTrace_4443348 : CollatzResearch.WordTrace tailWord_4443348 prefixEnd_4443348 2281573239193986614215421 := by
  unfold tailWord_4443348
  simp only [CollatzResearch.WordTrace]
  refine ⟨81031107753258267133653349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108041477004344356178204465 81031107753258267133653349)
  ·
    refine ⟨15193332703735925087560003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81031107753258267133653349 15193332703735925087560003)
    ·
      refine ⟨22789999055603887631340005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15193332703735925087560003 22789999055603887631340005)
      ·
        refine ⟨4273124822925728930876251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22789999055603887631340005 4273124822925728930876251)
        ·
          refine ⟨6409687234388593396314377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273124822925728930876251 6409687234388593396314377)
          ·
            refine ⟨4807265425791445047235783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6409687234388593396314377 4807265425791445047235783)
            ·
              refine ⟨7210898138687167570853675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807265425791445047235783 7210898138687167570853675)
              ·
                refine ⟨10816347208030751356280513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7210898138687167570853675 10816347208030751356280513)
                ·
                  refine ⟨8112260406023063517210385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10816347208030751356280513 8112260406023063517210385)
                  ·
                    refine ⟨6084195304517297637907789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8112260406023063517210385 6084195304517297637907789)
                    ·
                      refine ⟨2281573239193986614215421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084195304517297637907789 2281573239193986614215421)
                      ·
                        rfl

theorem cell23_4443348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4443348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443348 prefixEnd_4443348 := by exact prefixLift 4443348
  have htrace : WordTrace (prefixWord ++ tailWord_4443348) baseStart_4443348 baseEnd_4443348 := by
    simpa [prefixWord, tailWord_4443348, baseEnd_4443348] using wordTrace_append hprefix tailTrace_4443348
  have hstable : (prefixWord ++ tailWord_4443348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443348).length < 2 ^ (prefixWord ++ tailWord_4443348).sum := by decide
  have hdescent : baseEnd_4443348 < baseStart_4443348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443361 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_4443361 : Nat := 118140960795 + 4443361 * 2 ^ 59
def prefixEnd_4443361 : Nat := 4983230072969 + 3 ^ 40 * 4443361 * 2
def baseEnd_4443361 : Nat := 2281579914442495063352861

theorem tailTrace_4443361 : CollatzResearch.WordTrace tailWord_4443361 prefixEnd_4443361 2281579914442495063352861 := by
  unfold tailWord_4443361
  simp only [CollatzResearch.WordTrace]
  refine ⟨162062689655469437487529937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108041793103646291658353291 162062689655469437487529937)
  ·
    refine ⟨121547017241602078115647453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162062689655469437487529937 121547017241602078115647453)
    ·
      refine ⟨45580131465600779293367795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121547017241602078115647453 45580131465600779293367795)
      ·
        refine ⟨68370197198401168940051693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45580131465600779293367795 68370197198401168940051693)
        ·
          refine ⟨25638823949400438352519385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68370197198401168940051693 25638823949400438352519385)
          ·
            refine ⟨19229117962050328764389539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25638823949400438352519385 19229117962050328764389539)
            ·
              refine ⟨28843676943075493146584309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19229117962050328764389539 28843676943075493146584309)
              ·
                refine ⟨2704094713413327482492279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28843676943075493146584309 2704094713413327482492279)
                ·
                  refine ⟨4056142070119991223738419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704094713413327482492279 4056142070119991223738419)
                  ·
                    refine ⟨6084213105179986835607629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4056142070119991223738419 6084213105179986835607629)
                    ·
                      refine ⟨2281579914442495063352861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084213105179986835607629 2281579914442495063352861)
                      ·
                        rfl

theorem cell23_4443361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_4443361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443361 prefixEnd_4443361 := by exact prefixLift 4443361
  have htrace : WordTrace (prefixWord ++ tailWord_4443361) baseStart_4443361 baseEnd_4443361 := by
    simpa [prefixWord, tailWord_4443361, baseEnd_4443361] using wordTrace_append hprefix tailTrace_4443361
  have hstable : (prefixWord ++ tailWord_4443361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443361).length < 2 ^ (prefixWord ++ tailWord_4443361).sum := by decide
  have hdescent : baseEnd_4443361 < baseStart_4443361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443364 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_4443364 : Nat := 118140960795 + 4443364 * 2 ^ 59
def prefixEnd_4443364 : Nat := 4983230072969 + 3 ^ 40 * 4443364 * 2
def baseEnd_4443364 : Nat := 760527151628152850538449

theorem tailTrace_4443364 : CollatzResearch.WordTrace tailWord_4443364 prefixEnd_4443364 760527151628152850538449 := by
  unfold tailWord_4443364
  simp only [CollatzResearch.WordTrace]
  refine ⟨81031399537229284499944573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108041866049639045999926097 81031399537229284499944573)
  ·
    refine ⟨30386774826460981687479215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81031399537229284499944573 30386774826460981687479215)
    ·
      refine ⟨45580162239691472531218823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30386774826460981687479215 45580162239691472531218823)
      ·
        refine ⟨68370243359537208796828235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45580162239691472531218823 68370243359537208796828235)
        ·
          refine ⟨102555365039305813195242353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68370243359537208796828235 102555365039305813195242353)
          ·
            refine ⟨76916523779479359896431765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102555365039305813195242353 76916523779479359896431765)
            ·
              refine ⟨3605462052163094995145239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76916523779479359896431765 3605462052163094995145239)
              ·
                refine ⟨5408193078244642492717859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605462052163094995145239 5408193078244642492717859)
                ·
                  refine ⟨8112289617366963739076789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408193078244642492717859 8112289617366963739076789)
                  ·
                    refine ⟨760527151628152850538449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8112289617366963739076789 760527151628152850538449)
                    ·
                      rfl

theorem cell23_4443364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_4443364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443364 prefixEnd_4443364 := by exact prefixLift 4443364
  have htrace : WordTrace (prefixWord ++ tailWord_4443364) baseStart_4443364 baseEnd_4443364 := by
    simpa [prefixWord, tailWord_4443364, baseEnd_4443364] using wordTrace_append hprefix tailTrace_4443364
  have hstable : (prefixWord ++ tailWord_4443364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443364).length < 2 ^ (prefixWord ++ tailWord_4443364).sum := by decide
  have hdescent : baseEnd_4443364 < baseStart_4443364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443404 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_4443404 : Nat := 118140960795 + 4443404 * 2 ^ 59
def prefixEnd_4443404 : Nat := 4983230072969 + 3 ^ 40 * 4443404 * 2
def baseEnd_4443404 : Nat := 2281601994110638395115163

theorem tailTrace_4443404 : CollatzResearch.WordTrace tailWord_4443404 prefixEnd_4443404 2281601994110638395115163 := by
  unfold tailWord_4443404
  simp only [CollatzResearch.WordTrace]
  refine ⟨81032128997156827915672633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108042838662875770554230177 81032128997156827915672633)
  ·
    refine ⟨60774096747867620936754475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81032128997156827915672633 60774096747867620936754475)
    ·
      refine ⟨91161145121801431405131713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60774096747867620936754475 91161145121801431405131713)
      ·
        refine ⟨68370858841351073553848785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91161145121801431405131713 68370858841351073553848785)
        ·
          refine ⟨51278144131013305165386589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68370858841351073553848785 51278144131013305165386589)
          ·
            refine ⟨19229304049129989437019971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51278144131013305165386589 19229304049129989437019971)
            ·
              refine ⟨28843956073694984155529957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19229304049129989437019971 28843956073694984155529957)
              ·
                refine ⟨5408241763817809529161867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28843956073694984155529957 5408241763817809529161867)
                ·
                  refine ⟨8112362645726714293742801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408241763817809529161867 8112362645726714293742801)
                  ·
                    refine ⟨6084271984295035720307101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8112362645726714293742801 6084271984295035720307101)
                    ·
                      refine ⟨2281601994110638395115163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084271984295035720307101 2281601994110638395115163)
                      ·
                        rfl

theorem cell23_4443404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_4443404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443404 prefixEnd_4443404 := by exact prefixLift 4443404
  have htrace : WordTrace (prefixWord ++ tailWord_4443404) baseStart_4443404 baseEnd_4443404 := by
    simpa [prefixWord, tailWord_4443404, baseEnd_4443404] using wordTrace_append hprefix tailTrace_4443404
  have hstable : (prefixWord ++ tailWord_4443404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443404).length < 2 ^ (prefixWord ++ tailWord_4443404).sum := by decide
  have hdescent : baseEnd_4443404 < baseStart_4443404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443421 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4443421 : Nat := 118140960795 + 4443421 * 2 ^ 59
def prefixEnd_4443421 : Nat := 4983230072969 + 3 ^ 40 * 4443421 * 2
def baseEnd_4443421 : Nat := 2281610723281764828602585

theorem tailTrace_4443421 : CollatzResearch.WordTrace tailWord_4443421 prefixEnd_4443421 2281610723281764828602585 := by
  unfold tailWord_4443421
  simp only [CollatzResearch.WordTrace]
  refine ⟨162064878035252067734714117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108043252023501378489809411 162064878035252067734714117)
  ·
    refine ⟨30387164631609762700258897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162064878035252067734714117 30387164631609762700258897)
    ·
      refine ⟨22790373473707322025194173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30387164631609762700258897 22790373473707322025194173)
      ·
        refine ⟨8546390052640245759447815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22790373473707322025194173 8546390052640245759447815)
        ·
          refine ⟨12819585078960368639171723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546390052640245759447815 12819585078960368639171723)
          ·
            refine ⟨19229377618440552958757585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12819585078960368639171723 19229377618440552958757585)
            ·
              refine ⟨14422033213830414719068189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19229377618440552958757585 14422033213830414719068189)
              ·
                refine ⟨5408262455186405519650571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14422033213830414719068189 5408262455186405519650571)
                ·
                  refine ⟨8112393682779608279475857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408262455186405519650571 8112393682779608279475857)
                  ·
                    refine ⟨6084295262084706209606893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8112393682779608279475857 6084295262084706209606893)
                    ·
                      refine ⟨2281610723281764828602585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084295262084706209606893 2281610723281764828602585)
                      ·
                        rfl

theorem cell23_4443421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4443421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443421 prefixEnd_4443421 := by exact prefixLift 4443421
  have htrace : WordTrace (prefixWord ++ tailWord_4443421) baseStart_4443421 baseEnd_4443421 := by
    simpa [prefixWord, tailWord_4443421, baseEnd_4443421] using wordTrace_append hprefix tailTrace_4443421
  have hstable : (prefixWord ++ tailWord_4443421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443421).length < 2 ^ (prefixWord ++ tailWord_4443421).sum := by decide
  have hdescent : baseEnd_4443421 < baseStart_4443421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443424 : List Nat := [2, 1, 1, 5, 4, 1, 9]
def baseStart_4443424 : Nat := 118140960795 + 4443424 * 2 ^ 59
def prefixEnd_4443424 : Nat := 4983230072969 + 3 ^ 40 * 4443424 * 2
def baseEnd_4443424 : Nat := 28168052638564547121791

theorem tailTrace_4443424 : CollatzResearch.WordTrace tailWord_4443424 prefixEnd_4443424 28168052638564547121791 := by
  unfold tailWord_4443424
  simp only [CollatzResearch.WordTrace]
  refine ⟨81032493727120599623536663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108043324969494132831382217 81032493727120599623536663)
  ·
    refine ⟨121548740590680899435304995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81032493727120599623536663 121548740590680899435304995)
    ·
      refine ⟨182323110886021349152957493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121548740590680899435304995 182323110886021349152957493)
      ·
        refine ⟨17092791645564501483089765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182323110886021349152957493 17092791645564501483089765)
        ·
          refine ⟨3204898433543344028079331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17092791645564501483089765 3204898433543344028079331)
          ·
            refine ⟨4807347650315016042118997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204898433543344028079331 4807347650315016042118997)
            ·
              refine ⟨28168052638564547121791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4807347650315016042118997 28168052638564547121791)
              ·
                rfl

theorem cell23_4443424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 9].length) (baseStart_4443424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443424 prefixEnd_4443424 := by exact prefixLift 4443424
  have htrace : WordTrace (prefixWord ++ tailWord_4443424) baseStart_4443424 baseEnd_4443424 := by
    simpa [prefixWord, tailWord_4443424, baseEnd_4443424] using wordTrace_append hprefix tailTrace_4443424
  have hstable : (prefixWord ++ tailWord_4443424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443424).length < 2 ^ (prefixWord ++ tailWord_4443424).sum := by decide
  have hdescent : baseEnd_4443424 < baseStart_4443424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443487 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_4443487 : Nat := 118140960795 + 4443487 * 2 ^ 59
def prefixEnd_4443487 : Nat := 4983230072969 + 3 ^ 40 * 4443487 * 2
def baseEnd_4443487 : Nat := 2281644613004961570377281

theorem tailTrace_4443487 : CollatzResearch.WordTrace tailWord_4443487 prefixEnd_4443487 2281644613004961570377281 := by
  unfold tailWord_4443487
  simp only [CollatzResearch.WordTrace]
  refine ⟨162067285253012961006616715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108044856835341974004411143 162067285253012961006616715)
  ·
    refine ⟨243100927879519441509925073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162067285253012961006616715 243100927879519441509925073)
    ·
      refine ⟨182325695909639581132443805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243100927879519441509925073 182325695909639581132443805)
      ·
        refine ⟨68372135966114842924666427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182325695909639581132443805 68372135966114842924666427)
        ·
          refine ⟨102558203949172264386999641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68372135966114842924666427 102558203949172264386999641)
          ·
            refine ⟨76918652961879198290249731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102558203949172264386999641 76918652961879198290249731)
            ·
              refine ⟨115377979442818797435374597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76918652961879198290249731 115377979442818797435374597)
              ·
                refine ⟨21633371145528524519132737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115377979442818797435374597 21633371145528524519132737)
                ·
                  refine ⟨16225028359146393389349553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21633371145528524519132737 16225028359146393389349553)
                  ·
                    refine ⟨12168771269359795042012165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16225028359146393389349553 12168771269359795042012165)
                    ·
                      refine ⟨2281644613004961570377281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12168771269359795042012165 2281644613004961570377281)
                      ·
                        rfl

theorem cell23_4443487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_4443487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443487 prefixEnd_4443487 := by exact prefixLift 4443487
  have htrace : WordTrace (prefixWord ++ tailWord_4443487) baseStart_4443487 baseEnd_4443487 := by
    simpa [prefixWord, tailWord_4443487, baseEnd_4443487] using wordTrace_append hprefix tailTrace_4443487
  have hstable : (prefixWord ++ tailWord_4443487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443487).length < 2 ^ (prefixWord ++ tailWord_4443487).sum := by decide
  have hdescent : baseEnd_4443487 < baseStart_4443487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443584 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_4443584 : Nat := 118140960795 + 4443584 * 2 ^ 59
def prefixEnd_4443584 : Nat := 4983230072969 + 3 ^ 40 * 4443584 * 2
def baseEnd_4443584 : Nat := 2281694420628447690864335

theorem tailTrace_4443584 : CollatzResearch.WordTrace tailWord_4443584 prefixEnd_4443584 2281694420628447690864335 := by
  unfold tailWord_4443584
  simp only [CollatzResearch.WordTrace]
  refine ⟨81035411566830773286448903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108047215422441031048598537 81035411566830773286448903)
  ·
    refine ⟨121553117350246159929673355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81035411566830773286448903 121553117350246159929673355)
    ·
      refine ⟨182329676025369239894510033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121553117350246159929673355 182329676025369239894510033)
      ·
        refine ⟨136747257019026929920882525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182329676025369239894510033 136747257019026929920882525)
        ·
          refine ⟨51280221382135098720330947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136747257019026929920882525 51280221382135098720330947)
          ·
            refine ⟨76920332073202648080496421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51280221382135098720330947 76920332073202648080496421)
            ·
              refine ⟨14422562263725496515093079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76920332073202648080496421 14422562263725496515093079)
              ·
                refine ⟨21633843395588244772639619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14422562263725496515093079 21633843395588244772639619)
                ·
                  refine ⟨32450765093382367158959429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21633843395588244772639619 32450765093382367158959429)
                  ·
                    refine ⟨6084518455009193842304893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32450765093382367158959429 6084518455009193842304893)
                    ·
                      refine ⟨2281694420628447690864335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084518455009193842304893 2281694420628447690864335)
                      ·
                        rfl

theorem cell23_4443584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_4443584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443584 prefixEnd_4443584 := by exact prefixLift 4443584
  have htrace : WordTrace (prefixWord ++ tailWord_4443584) baseStart_4443584 baseEnd_4443584 := by
    simpa [prefixWord, tailWord_4443584, baseEnd_4443584] using wordTrace_append hprefix tailTrace_4443584
  have hstable : (prefixWord ++ tailWord_4443584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443584).length < 2 ^ (prefixWord ++ tailWord_4443584).sum := by decide
  have hdescent : baseEnd_4443584 < baseStart_4443584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443587 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 8]
def baseStart_4443587 : Nat := 118140960795 + 4443587 * 2 ^ 59
def prefixEnd_4443587 : Nat := 4983230072969 + 3 ^ 40 * 4443587 * 2
def baseEnd_4443587 : Nat := 253521773452267908791869

theorem tailTrace_4443587 : CollatzResearch.WordTrace tailWord_4443587 prefixEnd_4443587 253521773452267908791869 := by
  unfold tailWord_4443587
  simp only [CollatzResearch.WordTrace]
  refine ⟨162070932552650678085257015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108047288368433785390171343 162070932552650678085257015)
  ·
    refine ⟨243106398828976017127885523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162070932552650678085257015 243106398828976017127885523)
    ·
      refine ⟨364659598243464025691828285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243106398828976017127885523 364659598243464025691828285)
      ·
        refine ⟨136747349341299009634435607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 364659598243464025691828285 136747349341299009634435607)
        ·
          refine ⟨205121024011948514451653411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136747349341299009634435607 205121024011948514451653411)
          ·
            refine ⟨307681536017922771677480117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205121024011948514451653411 307681536017922771677480117)
            ·
              refine ⟨28845144001680259844763761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 307681536017922771677480117 28845144001680259844763761)
              ·
                refine ⟨21633858001260194883572821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28845144001680259844763761 21633858001260194883572821)
                ·
                  refine ⟨253521773452267908791869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21633858001260194883572821 253521773452267908791869)
                  ·
                    rfl

theorem cell23_4443587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 8].length) (baseStart_4443587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443587 prefixEnd_4443587 := by exact prefixLift 4443587
  have htrace : WordTrace (prefixWord ++ tailWord_4443587) baseStart_4443587 baseEnd_4443587 := by
    simpa [prefixWord, tailWord_4443587, baseEnd_4443587] using wordTrace_append hprefix tailTrace_4443587
  have hstable : (prefixWord ++ tailWord_4443587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443587).length < 2 ^ (prefixWord ++ tailWord_4443587).sum := by decide
  have hdescent : baseEnd_4443587 < baseStart_4443587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443607 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_4443607 : Nat := 118140960795 + 4443607 * 2 ^ 59
def prefixEnd_4443607 : Nat := 4983230072969 + 3 ^ 40 * 4443607 * 2
def baseEnd_4443607 : Nat := 2281706230683501100876729

theorem tailTrace_4443607 : CollatzResearch.WordTrace tailWord_4443607 prefixEnd_4443607 2281706230683501100876729 := by
  unfold tailWord_4443607
  simp only [CollatzResearch.WordTrace]
  refine ⟨162071662012578221500985075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108047774675052147667323383 162071662012578221500985075)
  ·
    refine ⟨243107493018867332251477613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162071662012578221500985075 243107493018867332251477613)
    ·
      refine ⟨91165309882075249594304105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243107493018867332251477613 91165309882075249594304105)
      ·
        refine ⟨68373982411556437195728079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91165309882075249594304105 68373982411556437195728079)
        ·
          refine ⟨102560973617334655793592119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68373982411556437195728079 102560973617334655793592119)
          ·
            refine ⟨153841460426001983690388179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102560973617334655793592119 153841460426001983690388179)
            ·
              refine ⟨230762190639002975535582269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153841460426001983690388179 230762190639002975535582269)
              ·
                refine ⟨86535821489626115825843351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230762190639002975535582269 86535821489626115825843351)
                ·
                  refine ⟨129803732234439173738765027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86535821489626115825843351 129803732234439173738765027)
                  ·
                    refine ⟨194705598351658760608147541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129803732234439173738765027 194705598351658760608147541)
                    ·
                      refine ⟨2281706230683501100876729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194705598351658760608147541 2281706230683501100876729)
                      ·
                        rfl

theorem cell23_4443607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_4443607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443607 prefixEnd_4443607 := by exact prefixLift 4443607
  have htrace : WordTrace (prefixWord ++ tailWord_4443607) baseStart_4443607 baseEnd_4443607 := by
    simpa [prefixWord, tailWord_4443607, baseEnd_4443607] using wordTrace_append hprefix tailTrace_4443607
  have hstable : (prefixWord ++ tailWord_4443607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443607).length < 2 ^ (prefixWord ++ tailWord_4443607).sum := by decide
  have hdescent : baseEnd_4443607 < baseStart_4443607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443621 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 6]
def baseStart_4443621 : Nat := 118140960795 + 4443621 * 2 ^ 59
def prefixEnd_4443621 : Nat := 4983230072969 + 3 ^ 40 * 4443621 * 2
def baseEnd_4443621 : Nat := 253523713268073782900185

theorem tailTrace_4443621 : CollatzResearch.WordTrace tailWord_4443621 prefixEnd_4443621 253523713268073782900185 := by
  unfold tailWord_4443621
  simp only [CollatzResearch.WordTrace]
  refine ⟨162072172634527501891994717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108048115089685001261329811 162072172634527501891994717)
  ·
    refine ⟨60777064737947813209498019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162072172634527501891994717 60777064737947813209498019)
    ·
      refine ⟨91165597106921719814247029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60777064737947813209498019 91165597106921719814247029)
      ·
        refine ⟨8546774728773911232585659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91165597106921719814247029 8546774728773911232585659)
        ·
          refine ⟨12820162093160866848878489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546774728773911232585659 12820162093160866848878489)
          ·
            refine ⟨9615121569870650136658867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12820162093160866848878489 9615121569870650136658867)
            ·
              refine ⟨14422682354805975204988301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9615121569870650136658867 14422682354805975204988301)
              ·
                refine ⟨5408505883052240701870613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14422682354805975204988301 5408505883052240701870613)
                ·
                  refine ⟨253523713268073782900185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5408505883052240701870613 253523713268073782900185)
                  ·
                    rfl

theorem cell23_4443621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_4443621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443621 prefixEnd_4443621 := by exact prefixLift 4443621
  have htrace : WordTrace (prefixWord ++ tailWord_4443621) baseStart_4443621 baseEnd_4443621 := by
    simpa [prefixWord, tailWord_4443621, baseEnd_4443621] using wordTrace_append hprefix tailTrace_4443621
  have hstable : (prefixWord ++ tailWord_4443621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443621).length < 2 ^ (prefixWord ++ tailWord_4443621).sum := by decide
  have hdescent : baseEnd_4443621 < baseStart_4443621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443627 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_4443627 : Nat := 118140960795 + 4443627 * 2 ^ 59
def prefixEnd_4443627 : Nat := 4983230072969 + 3 ^ 40 * 4443627 * 2
def baseEnd_4443627 : Nat := 2281716500296591022626637

theorem tailTrace_4443627 : CollatzResearch.WordTrace tailWord_4443627 prefixEnd_4443627 2281716500296591022626637 := by
  unfold tailWord_4443627
  simp only [CollatzResearch.WordTrace]
  refine ⟨162072391472505764916713135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108048260981670509944475423 162072391472505764916713135)
  ·
    refine ⟨243108587208758647375069703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162072391472505764916713135 243108587208758647375069703)
    ·
      refine ⟨364662880813137971062604555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243108587208758647375069703 364662880813137971062604555)
      ·
        refine ⟨546994321219706956593906833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364662880813137971062604555 546994321219706956593906833)
        ·
          refine ⟨410245740914780217445430125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546994321219706956593906833 410245740914780217445430125)
          ·
            refine ⟨153842152843042581542036297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410245740914780217445430125 153842152843042581542036297)
            ·
              refine ⟨115381614632281936156527223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153842152843042581542036297 115381614632281936156527223)
              ·
                refine ⟨173072421948422904234790835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115381614632281936156527223 173072421948422904234790835)
                ·
                  refine ⟨259608632922634356352186253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173072421948422904234790835 259608632922634356352186253)
                  ·
                    refine ⟨97353237345987883632069845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259608632922634356352186253 97353237345987883632069845)
                    ·
                      refine ⟨2281716500296591022626637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97353237345987883632069845 2281716500296591022626637)
                      ·
                        rfl

theorem cell23_4443627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_4443627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443627 prefixEnd_4443627 := by exact prefixLift 4443627
  have htrace : WordTrace (prefixWord ++ tailWord_4443627) baseStart_4443627 baseEnd_4443627 := by
    simpa [prefixWord, tailWord_4443627, baseEnd_4443627] using wordTrace_append hprefix tailTrace_4443627
  have hstable : (prefixWord ++ tailWord_4443627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443627).length < 2 ^ (prefixWord ++ tailWord_4443627).sum := by decide
  have hdescent : baseEnd_4443627 < baseStart_4443627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443631 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 3]
def baseStart_4443631 : Nat := 118140960795 + 4443631 * 2 ^ 59
def prefixEnd_4443631 : Nat := 4983230072969 + 3 ^ 40 * 4443631 * 2
def baseEnd_4443631 : Nat := 2281718554219209006976619

theorem tailTrace_4443631 : CollatzResearch.WordTrace tailWord_4443631 prefixEnd_4443631 2281718554219209006976619 := by
  unfold tailWord_4443631
  simp only [CollatzResearch.WordTrace]
  refine ⟨162072537364491273599858747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108048358242994182399905831 162072537364491273599858747)
  ·
    refine ⟨243108806046736910399788121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162072537364491273599858747 243108806046736910399788121)
    ·
      refine ⟨182331604535052682799841091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243108806046736910399788121 182331604535052682799841091)
      ·
        refine ⟨273497406802579024199761637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182331604535052682799841091 273497406802579024199761637)
        ·
          refine ⟨51280763775483567037455307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273497406802579024199761637 51280763775483567037455307)
          ·
            refine ⟨76921145663225350556182961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51280763775483567037455307 76921145663225350556182961)
            ·
              refine ⟨57690859247419012917137221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76921145663225350556182961 57690859247419012917137221)
              ·
                refine ⟨10817036108891064921963229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57690859247419012917137221 10817036108891064921963229)
                ·
                  refine ⟨4056388540834149345736211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10817036108891064921963229 4056388540834149345736211)
                  ·
                    refine ⟨6084582811251224018604317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4056388540834149345736211 6084582811251224018604317)
                    ·
                      refine ⟨2281718554219209006976619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084582811251224018604317 2281718554219209006976619)
                      ·
                        rfl

theorem cell23_4443631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_4443631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443631 prefixEnd_4443631 := by exact prefixLift 4443631
  have htrace : WordTrace (prefixWord ++ tailWord_4443631) baseStart_4443631 baseEnd_4443631 := by
    simpa [prefixWord, tailWord_4443631, baseEnd_4443631] using wordTrace_append hprefix tailTrace_4443631
  have hstable : (prefixWord ++ tailWord_4443631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443631).length < 2 ^ (prefixWord ++ tailWord_4443631).sum := by decide
  have hdescent : baseEnd_4443631 < baseStart_4443631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443658 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_4443658 : Nat := 118140960795 + 4443658 * 2 ^ 59
def prefixEnd_4443658 : Nat := 4983230072969 + 3 ^ 40 * 4443658 * 2
def baseEnd_4443658 : Nat := 2281732418196880401338995

theorem tailTrace_4443658 : CollatzResearch.WordTrace tailWord_4443658 prefixEnd_4443658 2281732418196880401338995 := by
  unfold tailWord_4443658
  simp only [CollatzResearch.WordTrace]
  refine ⟨40518380533848364302772907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108049014756928971474061085 40518380533848364302772907)
  ·
    refine ⟨60777570800772546454159361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40518380533848364302772907 60777570800772546454159361)
    ·
      refine ⟨45583178100579409840619521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60777570800772546454159361 45583178100579409840619521)
      ·
        refine ⟨34187383575434557380464641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45583178100579409840619521 34187383575434557380464641)
        ·
          refine ⟨25640537681575918035348481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34187383575434557380464641 25640537681575918035348481)
          ·
            refine ⟨19230403261181938526511361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25640537681575918035348481 19230403261181938526511361)
            ·
              refine ⟨14422802445886453894883521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19230403261181938526511361 14422802445886453894883521)
              ·
                refine ⟨10817101834414840421162641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14422802445886453894883521 10817101834414840421162641)
                ·
                  refine ⟨8112826375811130315871981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10817101834414840421162641 8112826375811130315871981)
                  ·
                    refine ⟨3042309890929173868451993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8112826375811130315871981 3042309890929173868451993)
                    ·
                      refine ⟨2281732418196880401338995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042309890929173868451993 2281732418196880401338995)
                      ·
                        rfl

theorem cell23_4443658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_4443658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443658 prefixEnd_4443658 := by exact prefixLift 4443658
  have htrace : WordTrace (prefixWord ++ tailWord_4443658) baseStart_4443658 baseEnd_4443658 := by
    simpa [prefixWord, tailWord_4443658, baseEnd_4443658] using wordTrace_append hprefix tailTrace_4443658
  have hstable : (prefixWord ++ tailWord_4443658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443658).length < 2 ^ (prefixWord ++ tailWord_4443658).sum := by decide
  have hdescent : baseEnd_4443658 < baseStart_4443658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443674 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4443674 : Nat := 118140960795 + 4443674 * 2 ^ 59
def prefixEnd_4443674 : Nat := 4983230072969 + 3 ^ 40 * 4443674 * 2
def baseEnd_4443674 : Nat := 2281740633887352338738921

theorem tailTrace_4443674 : CollatzResearch.WordTrace tailWord_4443674 prefixEnd_4443674 2281740633887352338738921 := by
  unfold tailWord_4443674
  simp only [CollatzResearch.WordTrace]
  refine ⟨40518526425833872985918519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108049403802223661295782717 40518526425833872985918519)
  ·
    refine ⟨60777789638750809478877779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40518526425833872985918519 60777789638750809478877779)
    ·
      refine ⟨91166684458126214218316669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60777789638750809478877779 91166684458126214218316669)
      ·
        refine ⟨34187506671797330331868751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91166684458126214218316669 34187506671797330331868751)
        ·
          refine ⟨51281260007695995497803127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34187506671797330331868751 51281260007695995497803127)
          ·
            refine ⟨76921890011543993246704691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51281260007695995497803127 76921890011543993246704691)
            ·
              refine ⟨115382835017315989870057037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76921890011543993246704691 115382835017315989870057037)
              ·
                refine ⟨43268563131493496201271389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115382835017315989870057037 43268563131493496201271389)
                ·
                  refine ⟨16225711174310061075476771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43268563131493496201271389 16225711174310061075476771)
                  ·
                    refine ⟨24338566761465091613215157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16225711174310061075476771 24338566761465091613215157)
                    ·
                      refine ⟨2281740633887352338738921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24338566761465091613215157 2281740633887352338738921)
                      ·
                        rfl

theorem cell23_4443674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4443674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443674 prefixEnd_4443674 := by exact prefixLift 4443674
  have htrace : WordTrace (prefixWord ++ tailWord_4443674) baseStart_4443674 baseEnd_4443674 := by
    simpa [prefixWord, tailWord_4443674, baseEnd_4443674] using wordTrace_append hprefix tailTrace_4443674
  have hstable : (prefixWord ++ tailWord_4443674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443674).length < 2 ^ (prefixWord ++ tailWord_4443674).sum := by decide
  have hdescent : baseEnd_4443674 < baseStart_4443674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443681 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 1, 6]
def baseStart_4443681 : Nat := 118140960795 + 4443681 * 2 ^ 59
def prefixEnd_4443681 : Nat := 4983230072969 + 3 ^ 40 * 4443681 * 2
def baseEnd_4443681 : Nat := 760581409417311270450463

theorem tailTrace_4443681 : CollatzResearch.WordTrace tailWord_4443681 prefixEnd_4443681 760581409417311270450463 := by
  unfold tailWord_4443681
  simp only [CollatzResearch.WordTrace]
  refine ⟨162074361014310132139178897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108049574009540088092785931 162074361014310132139178897)
  ·
    refine ⟨121555770760732599104384173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162074361014310132139178897 121555770760732599104384173)
    ·
      refine ⟨45583414035274724664144065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121555770760732599104384173 45583414035274724664144065)
      ·
        refine ⟨34187560526456043498108049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45583414035274724664144065 34187560526456043498108049)
        ·
          refine ⟨25640670394842032623581037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34187560526456043498108049 25640670394842032623581037)
          ·
            refine ⟨9615251398065762233842889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25640670394842032623581037 9615251398065762233842889)
            ·
              refine ⟨7211438548549321675382167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9615251398065762233842889 7211438548549321675382167)
              ·
                refine ⟨10817157822823982513073251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7211438548549321675382167 10817157822823982513073251)
                ·
                  refine ⟨16225736734235973769609877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10817157822823982513073251 16225736734235973769609877)
                  ·
                    refine ⟨760581409417311270450463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16225736734235973769609877 760581409417311270450463)
                    ·
                      rfl

theorem cell23_4443681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_4443681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443681 prefixEnd_4443681 := by exact prefixLift 4443681
  have htrace : WordTrace (prefixWord ++ tailWord_4443681) baseStart_4443681 baseEnd_4443681 := by
    simpa [prefixWord, tailWord_4443681, baseEnd_4443681] using wordTrace_append hprefix tailTrace_4443681
  have hstable : (prefixWord ++ tailWord_4443681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443681).length < 2 ^ (prefixWord ++ tailWord_4443681).sum := by decide
  have hdescent : baseEnd_4443681 < baseStart_4443681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443701 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_4443701 : Nat := 118140960795 + 4443701 * 2 ^ 59
def prefixEnd_4443701 : Nat := 4983230072969 + 3 ^ 40 * 4443701 * 2
def baseEnd_4443701 : Nat := 2281754497865023733101297

theorem tailTrace_4443701 : CollatzResearch.WordTrace tailWord_4443701 prefixEnd_4443701 2281754497865023733101297 := by
  unfold tailWord_4443701
  simp only [CollatzResearch.WordTrace]
  refine ⟨162075090474237675554906957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108050060316158450369937971 162075090474237675554906957)
  ·
    refine ⟨60778158927839128333090109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162075090474237675554906957 60778158927839128333090109)
    ·
      refine ⟨22791809597939673124908791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60778158927839128333090109 22791809597939673124908791)
      ·
        refine ⟨34187714396909509687363187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22791809597939673124908791 34187714396909509687363187)
        ·
          refine ⟨51281571595364264531044781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34187714396909509687363187 51281571595364264531044781)
          ·
            refine ⟨19230589348261599199141793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51281571595364264531044781 19230589348261599199141793)
            ·
              refine ⟨14422942011196199399356345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19230589348261599199141793 14422942011196199399356345)
              ·
                refine ⟨10817206508397149549517259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14422942011196199399356345 10817206508397149549517259)
                ·
                  refine ⟨16225809762595724324275889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10817206508397149549517259 16225809762595724324275889)
                  ·
                    refine ⟨12169357321946793243206917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16225809762595724324275889 12169357321946793243206917)
                    ·
                      refine ⟨2281754497865023733101297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12169357321946793243206917 2281754497865023733101297)
                      ·
                        rfl

theorem cell23_4443701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_4443701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443701 prefixEnd_4443701 := by exact prefixLift 4443701
  have htrace : WordTrace (prefixWord ++ tailWord_4443701) baseStart_4443701 baseEnd_4443701 := by
    simpa [prefixWord, tailWord_4443701, baseEnd_4443701] using wordTrace_append hprefix tailTrace_4443701
  have hstable : (prefixWord ++ tailWord_4443701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443701).length < 2 ^ (prefixWord ++ tailWord_4443701).sum := by decide
  have hdescent : baseEnd_4443701 < baseStart_4443701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443702 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4443702 : Nat := 118140960795 + 4443702 * 2 ^ 59
def prefixEnd_4443702 : Nat := 4983230072969 + 3 ^ 40 * 4443702 * 2
def baseEnd_4443702 : Nat := 760585003781892743062931

theorem tailTrace_4443702 : CollatzResearch.WordTrace tailWord_4443702 prefixEnd_4443702 760585003781892743062931 := by
  unfold tailWord_4443702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129695434202128295355835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108050084631489368483795573 10129695434202128295355835)
  ·
    refine ⟨15194543151303192443033753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10129695434202128295355835 15194543151303192443033753)
    ·
      refine ⟨11395907363477394332275315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15194543151303192443033753 11395907363477394332275315)
      ·
        refine ⟨17093861045216091498412973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11395907363477394332275315 17093861045216091498412973)
        ·
          refine ⟨6410197891956034311904865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17093861045216091498412973 6410197891956034311904865)
          ·
            refine ⟨4807648418967025733928649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410197891956034311904865 4807648418967025733928649)
            ·
              refine ⟨3605736314225269300446487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807648418967025733928649 3605736314225269300446487)
              ·
                refine ⟨5408604471337903950669731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605736314225269300446487 5408604471337903950669731)
                ·
                  refine ⟨8112906707006855926004597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408604471337903950669731 8112906707006855926004597)
                  ·
                    refine ⟨760585003781892743062931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8112906707006855926004597 760585003781892743062931)
                    ·
                      rfl

theorem cell23_4443702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4443702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443702 prefixEnd_4443702 := by exact prefixLift 4443702
  have htrace : WordTrace (prefixWord ++ tailWord_4443702) baseStart_4443702 baseEnd_4443702 := by
    simpa [prefixWord, tailWord_4443702, baseEnd_4443702] using wordTrace_append hprefix tailTrace_4443702
  have hstable : (prefixWord ++ tailWord_4443702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443702).length < 2 ^ (prefixWord ++ tailWord_4443702).sum := by decide
  have hdescent : baseEnd_4443702 < baseStart_4443702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443705 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4443705 : Nat := 118140960795 + 4443705 * 2 ^ 59
def prefixEnd_4443705 : Nat := 4983230072969 + 3 ^ 40 * 4443705 * 2
def baseEnd_4443705 : Nat := 2281756551787641717451279

theorem tailTrace_4443705 : CollatzResearch.WordTrace tailWord_4443705 prefixEnd_4443705 2281756551787641717451279 := by
  unfold tailWord_4443705
  simp only [CollatzResearch.WordTrace]
  refine ⟨162075236366223184238052569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108050157577482122825368379 162075236366223184238052569)
  ·
    refine ⟨121556427274667388178539427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162075236366223184238052569 121556427274667388178539427)
    ·
      refine ⟨182334640912001082267809141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121556427274667388178539427 182334640912001082267809141)
      ·
        refine ⟨17093872585500101462607107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182334640912001082267809141 17093872585500101462607107)
        ·
          refine ⟨25640808878250152193910661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17093872585500101462607107 25640808878250152193910661)
          ·
            refine ⟨4807651664671903536358249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25640808878250152193910661 4807651664671903536358249)
            ·
              refine ⟨3605738748503927652268687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807651664671903536358249 3605738748503927652268687)
              ·
                refine ⟨5408608122755891478403031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605738748503927652268687 5408608122755891478403031)
                ·
                  refine ⟨8112912184133837217604547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408608122755891478403031 8112912184133837217604547)
                  ·
                    refine ⟨12169368276200755826406821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8112912184133837217604547 12169368276200755826406821)
                    ·
                      refine ⟨2281756551787641717451279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12169368276200755826406821 2281756551787641717451279)
                      ·
                        rfl

theorem cell23_4443705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4443705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443705 prefixEnd_4443705 := by exact prefixLift 4443705
  have htrace : WordTrace (prefixWord ++ tailWord_4443705) baseStart_4443705 baseEnd_4443705 := by
    simpa [prefixWord, tailWord_4443705, baseEnd_4443705] using wordTrace_append hprefix tailTrace_4443705
  have hstable : (prefixWord ++ tailWord_4443705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443705).length < 2 ^ (prefixWord ++ tailWord_4443705).sum := by decide
  have hdescent : baseEnd_4443705 < baseStart_4443705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443738 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_4443738 : Nat := 118140960795 + 4443738 * 2 ^ 59
def prefixEnd_4443738 : Nat := 4983230072969 + 3 ^ 40 * 4443738 * 2
def baseEnd_4443738 : Nat := 2281773496649240088338627

theorem tailTrace_4443738 : CollatzResearch.WordTrace tailWord_4443738 prefixEnd_4443738 2281773496649240088338627 := by
  unfold tailWord_4443738
  simp only [CollatzResearch.WordTrace]
  refine ⟨40519109993775907718500967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108050959983402420582669245 40519109993775907718500967)
  ·
    refine ⟨60778664990663861577751451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40519109993775907718500967 60778664990663861577751451)
    ·
      refine ⟨91167997485995792366627177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60778664990663861577751451 91167997485995792366627177)
      ·
        refine ⟨68375998114496844274970383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91167997485995792366627177 68375998114496844274970383)
        ·
          refine ⟨102563997171745266412455575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68375998114496844274970383 102563997171745266412455575)
          ·
            refine ⟨153845995757617899618683363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102563997171745266412455575 153845995757617899618683363)
            ·
              refine ⟨230768993636426849428025045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153845995757617899618683363 230768993636426849428025045)
              ·
                refine ⟨5408648288353754283469337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 230768993636426849428025045 5408648288353754283469337)
                ·
                  refine ⟨4056486216265315712602003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5408648288353754283469337 4056486216265315712602003)
                  ·
                    refine ⟨6084729324397973568903005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4056486216265315712602003 6084729324397973568903005)
                    ·
                      refine ⟨2281773496649240088338627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084729324397973568903005 2281773496649240088338627)
                      ·
                        rfl

theorem cell23_4443738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_4443738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443738 prefixEnd_4443738 := by exact prefixLift 4443738
  have htrace : WordTrace (prefixWord ++ tailWord_4443738) baseStart_4443738 baseEnd_4443738 := by
    simpa [prefixWord, tailWord_4443738, baseEnd_4443738] using wordTrace_append hprefix tailTrace_4443738
  have hstable : (prefixWord ++ tailWord_4443738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443738).length < 2 ^ (prefixWord ++ tailWord_4443738).sum := by decide
  have hdescent : baseEnd_4443738 < baseStart_4443738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443781 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_4443781 : Nat := 118140960795 + 4443781 * 2 ^ 59
def prefixEnd_4443781 : Nat := 4983230072969 + 3 ^ 40 * 4443781 * 2
def baseEnd_4443781 : Nat := 2281795576317383420100929

theorem tailTrace_4443781 : CollatzResearch.WordTrace tailWord_4443781 prefixEnd_4443781 2281795576317383420100929 := by
  unfold tailWord_4443781
  simp only [CollatzResearch.WordTrace]
  refine ⟨162078008313947849217819197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108052005542631899478546131 162078008313947849217819197)
  ·
    refine ⟨60779253117730443456682199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162078008313947849217819197 60779253117730443456682199)
    ·
      refine ⟨91168879676595665185023299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60779253117730443456682199 91168879676595665185023299)
      ·
        refine ⟨136753319514893497777534949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91168879676595665185023299 136753319514893497777534949)
        ·
          refine ⟨25641247409042530833287803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136753319514893497777534949 25641247409042530833287803)
          ·
            refine ⟨38461871113563796249931705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25641247409042530833287803 38461871113563796249931705)
            ·
              refine ⟨28846403335172847187448779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38461871113563796249931705 28846403335172847187448779)
              ·
                refine ⟨43269605002759270781173169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28846403335172847187448779 43269605002759270781173169)
                ·
                  refine ⟨32452203752069453085879877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43269605002759270781173169 32452203752069453085879877)
                  ·
                    refine ⟨6084788203513022453602477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32452203752069453085879877 6084788203513022453602477)
                    ·
                      refine ⟨2281795576317383420100929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6084788203513022453602477 2281795576317383420100929)
                      ·
                        rfl

theorem cell23_4443781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_4443781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443781 prefixEnd_4443781 := by exact prefixLift 4443781
  have htrace : WordTrace (prefixWord ++ tailWord_4443781) baseStart_4443781 baseEnd_4443781 := by
    simpa [prefixWord, tailWord_4443781, baseEnd_4443781] using wordTrace_append hprefix tailTrace_4443781
  have hstable : (prefixWord ++ tailWord_4443781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443781).length < 2 ^ (prefixWord ++ tailWord_4443781).sum := by decide
  have hdescent : baseEnd_4443781 < baseStart_4443781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443829 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_4443829 : Nat := 118140960795 + 4443829 * 2 ^ 59
def prefixEnd_4443829 : Nat := 4983230072969 + 3 ^ 40 * 4443829 * 2
def baseEnd_4443829 : Nat := 2281820223388799232300709

theorem tailTrace_4443829 : CollatzResearch.WordTrace tailWord_4443829 prefixEnd_4443829 2281820223388799232300709 := by
  unfold tailWord_4443829
  simp only [CollatzResearch.WordTrace]
  refine ⟨162079759017773953415566541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108053172678515968943711027 162079759017773953415566541)
  ·
    refine ⟨60779909631665232530837453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162079759017773953415566541 60779909631665232530837453)
    ·
      refine ⟨22792466111874462199064045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60779909631665232530837453 22792466111874462199064045)
      ·
        refine ⟨8547174791952923324649017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22792466111874462199064045 8547174791952923324649017)
        ·
          refine ⟨6410381093964692493486763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8547174791952923324649017 6410381093964692493486763)
          ·
            refine ⟨9615571640947038740230145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410381093964692493486763 9615571640947038740230145)
            ·
              refine ⟨7211678730710279055172609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9615571640947038740230145 7211678730710279055172609)
              ·
                refine ⟨5408759048032709291379457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7211678730710279055172609 5408759048032709291379457)
                ·
                  refine ⟨4056569286024531968534593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5408759048032709291379457 4056569286024531968534593)
                  ·
                    refine ⟨3042426964518398976400945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4056569286024531968534593 3042426964518398976400945)
                    ·
                      refine ⟨2281820223388799232300709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042426964518398976400945 2281820223388799232300709)
                      ·
                        rfl

theorem cell23_4443829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_4443829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443829 prefixEnd_4443829 := by exact prefixLift 4443829
  have htrace : WordTrace (prefixWord ++ tailWord_4443829) baseStart_4443829 baseEnd_4443829 := by
    simpa [prefixWord, tailWord_4443829, baseEnd_4443829] using wordTrace_append hprefix tailTrace_4443829
  have hstable : (prefixWord ++ tailWord_4443829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443829).length < 2 ^ (prefixWord ++ tailWord_4443829).sum := by decide
  have hdescent : baseEnd_4443829 < baseStart_4443829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443846 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4443846 : Nat := 118140960795 + 4443846 * 2 ^ 59
def prefixEnd_4443846 : Nat := 4983230072969 + 3 ^ 40 * 4443846 * 2
def baseEnd_4443846 : Nat := 2281828952559925665788131

theorem tailTrace_4443846 : CollatzResearch.WordTrace tailWord_4443846 prefixEnd_4443846 2281828952559925665788131 := by
  unfold tailWord_4443846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065011845584761416216731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108053586039141576879290261 5065011845584761416216731)
  ·
    refine ⟨7597517768377142124325097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5065011845584761416216731 7597517768377142124325097)
    ·
      refine ⟨5698138326282856593243823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7597517768377142124325097 5698138326282856593243823)
      ·
        refine ⟨8547207489424284889865735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698138326282856593243823 8547207489424284889865735)
        ·
          refine ⟨12820811234136427334798603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8547207489424284889865735 12820811234136427334798603)
          ·
            refine ⟨19231216851204641002197905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12820811234136427334798603 19231216851204641002197905)
            ·
              refine ⟨14423412638403480751648429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19231216851204641002197905 14423412638403480751648429)
              ·
                refine ⟨5408779739401305281868161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14423412638403480751648429 5408779739401305281868161)
                ·
                  refine ⟨4056584804550978961401121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5408779739401305281868161 4056584804550978961401121)
                  ·
                    refine ⟨3042438603413234221050841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4056584804550978961401121 3042438603413234221050841)
                    ·
                      refine ⟨2281828952559925665788131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042438603413234221050841 2281828952559925665788131)
                      ·
                        rfl

theorem cell23_4443846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4443846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443846 prefixEnd_4443846 := by exact prefixLift 4443846
  have htrace : WordTrace (prefixWord ++ tailWord_4443846) baseStart_4443846 baseEnd_4443846 := by
    simpa [prefixWord, tailWord_4443846, baseEnd_4443846] using wordTrace_append hprefix tailTrace_4443846
  have hstable : (prefixWord ++ tailWord_4443846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443846).length < 2 ^ (prefixWord ++ tailWord_4443846).sum := by decide
  have hdescent : baseEnd_4443846 < baseStart_4443846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443851 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 4]
def baseStart_4443851 : Nat := 118140960795 + 4443851 * 2 ^ 59
def prefixEnd_4443851 : Nat := 4983230072969 + 3 ^ 40 * 4443851 * 2
def baseEnd_4443851 : Nat := 2281831519963198146225607

theorem tailTrace_4443851 : CollatzResearch.WordTrace tailWord_4443851 prefixEnd_4443851 2281831519963198146225607 := by
  unfold tailWord_4443851
  simp only [CollatzResearch.WordTrace]
  refine ⟨162080561423694251172867407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108053707615796167448578271 162080561423694251172867407)
  ·
    refine ⟨243120842135541376759301111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162080561423694251172867407 243120842135541376759301111)
    ·
      refine ⟨364681263203312065138951667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243120842135541376759301111 364681263203312065138951667)
      ·
        refine ⟨547021894804968097708427501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364681263203312065138951667 547021894804968097708427501)
        ·
          refine ⟨205133210551863036640660313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 547021894804968097708427501 205133210551863036640660313)
          ·
            refine ⟨153849907913897277480495235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205133210551863036640660313 153849907913897277480495235)
            ·
              refine ⟨230774861870845916220742853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153849907913897277480495235 230774861870845916220742853)
              ·
                refine ⟨43270286600783609291389285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230774861870845916220742853 43270286600783609291389285)
                ·
                  refine ⟨8113178737646926742135491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43270286600783609291389285 8113178737646926742135491)
                  ·
                    refine ⟨12169768106470390113203237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8113178737646926742135491 12169768106470390113203237)
                    ·
                      refine ⟨2281831519963198146225607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12169768106470390113203237 2281831519963198146225607)
                      ·
                        rfl

theorem cell23_4443851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 4].length) (baseStart_4443851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443851 prefixEnd_4443851 := by exact prefixLift 4443851
  have htrace : WordTrace (prefixWord ++ tailWord_4443851) baseStart_4443851 baseEnd_4443851 := by
    simpa [prefixWord, tailWord_4443851, baseEnd_4443851] using wordTrace_append hprefix tailTrace_4443851
  have hstable : (prefixWord ++ tailWord_4443851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443851).length < 2 ^ (prefixWord ++ tailWord_4443851).sum := by decide
  have hdescent : baseEnd_4443851 < baseStart_4443851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443885 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4443885 : Nat := 118140960795 + 4443885 * 2 ^ 59
def prefixEnd_4443885 : Nat := 4983230072969 + 3 ^ 40 * 4443885 * 2
def baseEnd_4443885 : Nat := 2281848978305451013200451

theorem tailTrace_4443885 : CollatzResearch.WordTrace tailWord_4443885 prefixEnd_4443885 2281848978305451013200451 := by
  unfold tailWord_4443885
  simp only [CollatzResearch.WordTrace]
  refine ⟨162081801505571074979605109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108054534337047383319736739 162081801505571074979605109)
  ·
    refine ⟨15195168891147288279337979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162081801505571074979605109 15195168891147288279337979)
    ·
      refine ⟨22792753336720932419006969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15195168891147288279337979 22792753336720932419006969)
      ·
        refine ⟨17094565002540699314255227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22792753336720932419006969 17094565002540699314255227)
        ·
          refine ⟨25641847503811048971382841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17094565002540699314255227 25641847503811048971382841)
          ·
            refine ⟨19231385627858286728537131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25641847503811048971382841 19231385627858286728537131)
            ·
              refine ⟨28847078441787430092805697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19231385627858286728537131 28847078441787430092805697)
              ·
                refine ⟨21635308831340572569604273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28847078441787430092805697 21635308831340572569604273)
                ·
                  refine ⟨16226481623505429427203205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21635308831340572569604273 16226481623505429427203205)
                  ·
                    refine ⟨3042465304407268017600601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16226481623505429427203205 3042465304407268017600601)
                    ·
                      refine ⟨2281848978305451013200451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042465304407268017600601 2281848978305451013200451)
                      ·
                        rfl

theorem cell23_4443885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4443885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443885 prefixEnd_4443885 := by exact prefixLift 4443885
  have htrace : WordTrace (prefixWord ++ tailWord_4443885) baseStart_4443885 baseEnd_4443885 := by
    simpa [prefixWord, tailWord_4443885, baseEnd_4443885] using wordTrace_append hprefix tailTrace_4443885
  have hstable : (prefixWord ++ tailWord_4443885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443885).length < 2 ^ (prefixWord ++ tailWord_4443885).sum := by decide
  have hdescent : baseEnd_4443885 < baseStart_4443885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443895 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 1, 4]
def baseStart_4443895 : Nat := 118140960795 + 4443895 * 2 ^ 59
def prefixEnd_4443895 : Nat := 4983230072969 + 3 ^ 40 * 4443895 * 2
def baseEnd_4443895 : Nat := 760618037703998658025135

theorem tailTrace_4443895 : CollatzResearch.WordTrace tailWord_4443895 prefixEnd_4443895 760618037703998658025135 := by
  unfold tailWord_4443895
  simp only [CollatzResearch.WordTrace]
  refine ⟨162082166235534846687469139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108054777490356564458312759 162082166235534846687469139)
  ·
    refine ⟨243123249353302270031203709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162082166235534846687469139 243123249353302270031203709)
    ·
      refine ⟨91171218507488351261701391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243123249353302270031203709 91171218507488351261701391)
      ·
        refine ⟨136756827761232526892552087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91171218507488351261701391 136756827761232526892552087)
        ·
          refine ⟨205135241641848790338828131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136756827761232526892552087 205135241641848790338828131)
          ·
            refine ⟨307702862462773185508242197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205135241641848790338828131 307702862462773185508242197)
            ·
              refine ⟨14423571677942493070698853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 307702862462773185508242197 14423571677942493070698853)
              ·
                refine ⟨2704419689614217450756035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14423571677942493070698853 2704419689614217450756035)
                ·
                  refine ⟨4056629534421326176134053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704419689614217450756035 4056629534421326176134053)
                  ·
                    refine ⟨760618037703998658025135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4056629534421326176134053 760618037703998658025135)
                    ·
                      rfl

theorem cell23_4443895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_4443895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443895 prefixEnd_4443895 := by exact prefixLift 4443895
  have htrace : WordTrace (prefixWord ++ tailWord_4443895) baseStart_4443895 baseEnd_4443895 := by
    simpa [prefixWord, tailWord_4443895, baseEnd_4443895] using wordTrace_append hprefix tailTrace_4443895
  have hstable : (prefixWord ++ tailWord_4443895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443895).length < 2 ^ (prefixWord ++ tailWord_4443895).sum := by decide
  have hdescent : baseEnd_4443895 < baseStart_4443895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443951 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 3, 6]
def baseStart_4443951 : Nat := 118140960795 + 4443951 * 2 ^ 59
def prefixEnd_4443951 : Nat := 4983230072969 + 3 ^ 40 * 4443951 * 2
def baseEnd_4443951 : Nat := 760627622676215918325049

theorem tailTrace_4443951 : CollatzResearch.WordTrace tailWord_4443951 prefixEnd_4443951 760627622676215918325049 := by
  unfold tailWord_4443951
  simp only [CollatzResearch.WordTrace]
  refine ⟨162084208723331968251507707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108056139148887978834338471 162084208723331968251507707)
  ·
    refine ⟨243126313084997952377261561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162084208723331968251507707 243126313084997952377261561)
    ·
      refine ⟨182344734813748464282946171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243126313084997952377261561 182344734813748464282946171)
      ·
        refine ⟨273517102220622696424419257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182344734813748464282946171 273517102220622696424419257)
        ·
          refine ⟨205137826665467022318314443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273517102220622696424419257 205137826665467022318314443)
          ·
            refine ⟨307706739998200533477471665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205137826665467022318314443 307706739998200533477471665)
            ·
              refine ⟨230780054998650400108103749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307706739998200533477471665 230780054998650400108103749)
              ·
                refine ⟨43271260312246950020269453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230780054998650400108103749 43271260312246950020269453)
                ·
                  refine ⟨16226722617092606257601045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43271260312246950020269453 16226722617092606257601045)
                  ·
                    refine ⟨760627622676215918325049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16226722617092606257601045 760627622676215918325049)
                    ·
                      rfl

theorem cell23_4443951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_4443951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443951 prefixEnd_4443951 := by exact prefixLift 4443951
  have htrace : WordTrace (prefixWord ++ tailWord_4443951) baseStart_4443951 baseEnd_4443951 := by
    simpa [prefixWord, tailWord_4443951, baseEnd_4443951] using wordTrace_append hprefix tailTrace_4443951
  have hstable : (prefixWord ++ tailWord_4443951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443951).length < 2 ^ (prefixWord ++ tailWord_4443951).sum := by decide
  have hdescent : baseEnd_4443951 < baseStart_4443951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443975 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_4443975 : Nat := 118140960795 + 4443975 * 2 ^ 59
def prefixEnd_4443975 : Nat := 4983230072969 + 3 ^ 40 * 4443975 * 2
def baseEnd_4443975 : Nat := 2281895191564355661075037

theorem tailTrace_4443975 : CollatzResearch.WordTrace tailWord_4443975 prefixEnd_4443975 2281895191564355661075037 := by
  unfold tailWord_4443975
  simp only [CollatzResearch.WordTrace]
  refine ⟨162085084075245020350381379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108056722716830013566920919 162085084075245020350381379)
  ·
    refine ⟨243127626112867530525572069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162085084075245020350381379 243127626112867530525572069)
    ·
      refine ⟨45586429896162661973544763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243127626112867530525572069 45586429896162661973544763)
      ·
        refine ⟨68379644844243992960317145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45586429896162661973544763 68379644844243992960317145)
        ·
          refine ⟨51284733633182994720237859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68379644844243992960317145 51284733633182994720237859)
          ·
            refine ⟨76927100449774492080356789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51284733633182994720237859 76927100449774492080356789)
            ·
              refine ⟨7211915667166358632533449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76927100449774492080356789 7211915667166358632533449)
              ·
                refine ⟨5408936750374768974400087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7211915667166358632533449 5408936750374768974400087)
                ·
                  refine ⟨8113405125562153461600131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408936750374768974400087 8113405125562153461600131)
                  ·
                    refine ⟨12170107688343230192400197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8113405125562153461600131 12170107688343230192400197)
                    ·
                      refine ⟨2281895191564355661075037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12170107688343230192400197 2281895191564355661075037)
                      ·
                        rfl

theorem cell23_4443975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_4443975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443975 prefixEnd_4443975 := by exact prefixLift 4443975
  have htrace : WordTrace (prefixWord ++ tailWord_4443975) baseStart_4443975 baseEnd_4443975 := by
    simpa [prefixWord, tailWord_4443975, baseEnd_4443975] using wordTrace_append hprefix tailTrace_4443975
  have hstable : (prefixWord ++ tailWord_4443975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443975).length < 2 ^ (prefixWord ++ tailWord_4443975).sum := by decide
  have hdescent : baseEnd_4443975 < baseStart_4443975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4443998 : List Nat := [4, 4, 15]
def baseStart_4443998 : Nat := 118140960795 + 4443998 * 2 ^ 59
def prefixEnd_4443998 : Nat := 4983230072969 + 3 ^ 40 * 4443998 * 2
def baseEnd_4443998 : Nat := 347798658987869085671

theorem tailTrace_4443998 : CollatzResearch.WordTrace tailWord_4443998 prefixEnd_4443998 347798658987869085671 := by
  unfold tailWord_4443998
  simp only [CollatzResearch.WordTrace]
  refine ⟨20260740369270211909808581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108057281969441130185645765 20260740369270211909808581)
  ·
    refine ⟨3798888819238164733089109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20260740369270211909808581 3798888819238164733089109)
    ·
      refine ⟨347798658987869085671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 3798888819238164733089109 347798658987869085671)
      ·
        rfl

theorem cell23_4443998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 15].length) (baseStart_4443998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4443998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4443998 prefixEnd_4443998 := by exact prefixLift 4443998
  have htrace : WordTrace (prefixWord ++ tailWord_4443998) baseStart_4443998 baseEnd_4443998 := by
    simpa [prefixWord, tailWord_4443998, baseEnd_4443998] using wordTrace_append hprefix tailTrace_4443998
  have hstable : (prefixWord ++ tailWord_4443998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4443998).length < 2 ^ (prefixWord ++ tailWord_4443998).sum := by decide
  have hdescent : baseEnd_4443998 < baseStart_4443998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4443998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444002 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_4444002 : Nat := 118140960795 + 4444002 * 2 ^ 59
def prefixEnd_4444002 : Nat := 4983230072969 + 3 ^ 40 * 4444002 * 2
def baseEnd_4444002 : Nat := 760636351847342351812471

theorem tailTrace_4444002 : CollatzResearch.WordTrace tailWord_4444002 prefixEnd_4444002 760636351847342351812471 := by
  unfold tailWord_4444002
  simp only [CollatzResearch.WordTrace]
  refine ⟨40521517211536800990403565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108057379230764802641076173 40521517211536800990403565)
  ·
    refine ⟨15195568954326300371401337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40521517211536800990403565 15195568954326300371401337)
    ·
      refine ⟨11396676715744725278551003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15195568954326300371401337 11396676715744725278551003)
      ·
        refine ⟨17095015073617087917826505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11396676715744725278551003 17095015073617087917826505)
        ·
          refine ⟨12821261305212815938369879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17095015073617087917826505 12821261305212815938369879)
          ·
            refine ⟨19231891957819223907554819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12821261305212815938369879 19231891957819223907554819)
            ·
              refine ⟨28847837936728835861332229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19231891957819223907554819 28847837936728835861332229)
              ·
                refine ⟨5408969613136656723999793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28847837936728835861332229 5408969613136656723999793)
                ·
                  refine ⟨4056727209852492542999845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5408969613136656723999793 4056727209852492542999845)
                  ·
                    refine ⟨760636351847342351812471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4056727209852492542999845 760636351847342351812471)
                    ·
                      rfl

theorem cell23_4444002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_4444002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444002 prefixEnd_4444002 := by exact prefixLift 4444002
  have htrace : WordTrace (prefixWord ++ tailWord_4444002) baseStart_4444002 baseEnd_4444002 := by
    simpa [prefixWord, tailWord_4444002, baseEnd_4444002] using wordTrace_append hprefix tailTrace_4444002
  have hstable : (prefixWord ++ tailWord_4444002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444002).length < 2 ^ (prefixWord ++ tailWord_4444002).sum := by decide
  have hdescent : baseEnd_4444002 < baseStart_4444002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444003 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 1, 1, 3]
def baseStart_4444003 : Nat := 118140960795 + 4444003 * 2 ^ 59
def prefixEnd_4444003 : Nat := 4983230072969 + 3 ^ 40 * 4444003 * 2
def baseEnd_4444003 : Nat := 2281909569022681551524909

theorem tailTrace_4444003 : CollatzResearch.WordTrace tailWord_4444003 prefixEnd_4444003 2281909569022681551524909 := by
  unfold tailWord_4444003
  simp only [CollatzResearch.WordTrace]
  refine ⟨162086105319143581132400663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108057403546095720754933775 162086105319143581132400663)
  ·
    refine ⟨243129157978715371698600995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162086105319143581132400663 243129157978715371698600995)
    ·
      refine ⟨364693736968073057547901493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243129157978715371698600995 364693736968073057547901493)
      ·
        refine ⟨34190037840756849145115765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 364693736968073057547901493 34190037840756849145115765)
        ·
          refine ⟨3205316047570954607354603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34190037840756849145115765 3205316047570954607354603)
          ·
            refine ⟨4807974071356431911031905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205316047570954607354603 4807974071356431911031905)
            ·
              refine ⟨3605980553517323933273929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807974071356431911031905 3605980553517323933273929)
              ·
                refine ⟨2704485415137992949955447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605980553517323933273929 2704485415137992949955447)
                ·
                  refine ⟨4056728122706989424933171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704485415137992949955447 4056728122706989424933171)
                  ·
                    refine ⟨6085092184060484137399757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4056728122706989424933171 6085092184060484137399757)
                    ·
                      refine ⟨2281909569022681551524909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085092184060484137399757 2281909569022681551524909)
                      ·
                        rfl

theorem cell23_4444003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_4444003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444003 prefixEnd_4444003 := by exact prefixLift 4444003
  have htrace : WordTrace (prefixWord ++ tailWord_4444003) baseStart_4444003 baseEnd_4444003 := by
    simpa [prefixWord, tailWord_4444003, baseEnd_4444003] using wordTrace_append hprefix tailTrace_4444003
  have hstable : (prefixWord ++ tailWord_4444003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444003).length < 2 ^ (prefixWord ++ tailWord_4444003).sum := by decide
  have hdescent : baseEnd_4444003 < baseStart_4444003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444025 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_4444025 : Nat := 118140960795 + 4444025 * 2 ^ 59
def prefixEnd_4444025 : Nat := 4983230072969 + 3 ^ 40 * 4444025 * 2
def baseEnd_4444025 : Nat := 2281920865597080465449807

theorem tailTrace_4444025 : CollatzResearch.WordTrace tailWord_4444025 prefixEnd_4444025 2281920865597080465449807 := by
  unfold tailWord_4444025
  simp only [CollatzResearch.WordTrace]
  refine ⟨162086907725063878889701529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108057938483375919259801019 162086907725063878889701529)
  ·
    refine ⟨121565180793797909167276147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162086907725063878889701529 121565180793797909167276147)
    ·
      refine ⟨182347771190696863750914221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121565180793797909167276147 182347771190696863750914221)
      ·
        refine ⟨68380414196511323906592833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182347771190696863750914221 68380414196511323906592833)
        ·
          refine ⟨51285310647383492929944625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68380414196511323906592833 51285310647383492929944625)
          ·
            refine ⟨38463982985537619697458469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51285310647383492929944625 38463982985537619697458469)
            ·
              refine ⟨7211996809788303693273463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38463982985537619697458469 7211996809788303693273463)
              ·
                refine ⟨10817995214682455539910195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7211996809788303693273463 10817995214682455539910195)
                ·
                  refine ⟨16226992822023683309865293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10817995214682455539910195 16226992822023683309865293)
                  ·
                    refine ⟨6085122308258881241199485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16226992822023683309865293 6085122308258881241199485)
                    ·
                      refine ⟨2281920865597080465449807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085122308258881241199485 2281920865597080465449807)
                      ·
                        rfl

theorem cell23_4444025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_4444025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444025 prefixEnd_4444025 := by exact prefixLift 4444025
  have htrace : WordTrace (prefixWord ++ tailWord_4444025) baseStart_4444025 baseEnd_4444025 := by
    simpa [prefixWord, tailWord_4444025, baseEnd_4444025] using wordTrace_append hprefix tailTrace_4444025
  have hstable : (prefixWord ++ tailWord_4444025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444025).length < 2 ^ (prefixWord ++ tailWord_4444025).sum := by decide
  have hdescent : baseEnd_4444025 < baseStart_4444025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444088 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 7]
def baseStart_4444088 : Nat := 118140960795 + 4444088 * 2 ^ 59
def prefixEnd_4444088 : Nat := 4983230072969 + 3 ^ 40 * 4444088 * 2
def baseEnd_4444088 : Nat := 253550357208701524329113

theorem tailTrace_4444088 : CollatzResearch.WordTrace tailWord_4444088 prefixEnd_4444088 253550357208701524329113 := by
  unfold tailWord_4444088
  simp only [CollatzResearch.WordTrace]
  refine ⟨81044602761917820324622459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108059470349223760432829945 81044602761917820324622459)
  ·
    refine ⟨121566904142876730486933689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81044602761917820324622459 121566904142876730486933689)
    ·
      refine ⟨91175178107157547865200267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121566904142876730486933689 91175178107157547865200267)
      ·
        refine ⟨136762767160736321797800401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91175178107157547865200267 136762767160736321797800401)
        ·
          refine ⟨102572075370552241348350301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136762767160736321797800401 102572075370552241348350301)
          ·
            refine ⟨38464528263957090505631363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102572075370552241348350301 38464528263957090505631363)
            ·
              refine ⟨57696792395935635758447045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38464528263957090505631363 57696792395935635758447045)
              ·
                refine ⟨10818148574237931704708821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57696792395935635758447045 10818148574237931704708821)
                ·
                  refine ⟨253550357208701524329113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10818148574237931704708821 253550357208701524329113)
                  ·
                    rfl

theorem cell23_4444088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_4444088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444088 prefixEnd_4444088 := by exact prefixLift 4444088
  have htrace : WordTrace (prefixWord ++ tailWord_4444088) baseStart_4444088 baseEnd_4444088 := by
    simpa [prefixWord, tailWord_4444088, baseEnd_4444088] using wordTrace_append hprefix tailTrace_4444088
  have hstable : (prefixWord ++ tailWord_4444088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444088).length < 2 ^ (prefixWord ++ tailWord_4444088).sum := by decide
  have hdescent : baseEnd_4444088 < baseStart_4444088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444122 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_4444122 : Nat := 118140960795 + 4444122 * 2 ^ 59
def prefixEnd_4444122 : Nat := 4983230072969 + 3 ^ 40 * 4444122 * 2
def baseEnd_4444122 : Nat := 253552297024507398437429

theorem tailTrace_4444122 : CollatzResearch.WordTrace tailWord_4444122 prefixEnd_4444122 253552297024507398437429 := by
  unfold tailWord_4444122
  simp only [CollatzResearch.WordTrace]
  refine ⟨40522611401428116113995655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108060297070474976303988413 40522611401428116113995655)
  ·
    refine ⟨60783917102142174170993483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40522611401428116113995655 60783917102142174170993483)
    ·
      refine ⟨91175875653213261256490225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60783917102142174170993483 91175875653213261256490225)
      ·
        refine ⟨68381906739909945942367669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91175875653213261256490225 68381906739909945942367669)
        ·
          refine ⟨6410803756866557432096969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68381906739909945942367669 6410803756866557432096969)
          ·
            refine ⟨4808102817649918074072727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410803756866557432096969 4808102817649918074072727)
            ·
              refine ⟨7212154226474877111109091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808102817649918074072727 7212154226474877111109091)
              ·
                refine ⟨10818231339712315666663637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212154226474877111109091 10818231339712315666663637)
                ·
                  refine ⟨253552297024507398437429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10818231339712315666663637 253552297024507398437429)
                  ·
                    rfl

theorem cell23_4444122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_4444122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444122 prefixEnd_4444122 := by exact prefixLift 4444122
  have htrace : WordTrace (prefixWord ++ tailWord_4444122) baseStart_4444122 baseEnd_4444122 := by
    simpa [prefixWord, tailWord_4444122, baseEnd_4444122] using wordTrace_append hprefix tailTrace_4444122
  have hstable : (prefixWord ++ tailWord_4444122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444122).length < 2 ^ (prefixWord ++ tailWord_4444122).sum := by decide
  have hdescent : baseEnd_4444122 < baseStart_4444122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444155 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 4]
def baseStart_4444155 : Nat := 118140960795 + 4444155 * 2 ^ 59
def prefixEnd_4444155 : Nat := 4983230072969 + 3 ^ 40 * 4444155 * 2
def baseEnd_4444155 : Nat := 2281987618082164956824209

theorem tailTrace_4444155 : CollatzResearch.WordTrace tailWord_4444155 prefixEnd_4444155 2281987618082164956824209 := by
  unfold tailWord_4444155
  simp only [CollatzResearch.WordTrace]
  refine ⟨162091649214592911091933919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108061099476395274061289279 162091649214592911091933919)
  ·
    refine ⟨243137473821889366637900879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162091649214592911091933919 243137473821889366637900879)
    ·
      refine ⟨364706210732834049956851319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243137473821889366637900879 364706210732834049956851319)
      ·
        refine ⟨547059316099251074935276979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364706210732834049956851319 547059316099251074935276979)
        ·
          refine ⟨820588974148876612402915469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547059316099251074935276979 820588974148876612402915469)
          ·
            refine ⟨307720865305828729651093301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 820588974148876612402915469 307720865305828729651093301)
            ·
              refine ⟨28848831122421443404789997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 307720865305828729651093301 28848831122421443404789997)
              ·
                refine ⟨10818311670908041276796249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28848831122421443404789997 10818311670908041276796249)
                ·
                  refine ⟨8113733753181030957597187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10818311670908041276796249 8113733753181030957597187)
                  ·
                    refine ⟨12170600629771546436395781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8113733753181030957597187 12170600629771546436395781)
                    ·
                      refine ⟨2281987618082164956824209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12170600629771546436395781 2281987618082164956824209)
                      ·
                        rfl

theorem cell23_4444155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 4].length) (baseStart_4444155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444155 prefixEnd_4444155 := by exact prefixLift 4444155
  have htrace : WordTrace (prefixWord ++ tailWord_4444155) baseStart_4444155 baseEnd_4444155 := by
    simpa [prefixWord, tailWord_4444155, baseEnd_4444155] using wordTrace_append hprefix tailTrace_4444155
  have hstable : (prefixWord ++ tailWord_4444155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444155).length < 2 ^ (prefixWord ++ tailWord_4444155).sum := by decide
  have hdescent : baseEnd_4444155 < baseStart_4444155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444172 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 2, 4, 2]
def baseStart_4444172 : Nat := 118140960795 + 4444172 * 2 ^ 59
def prefixEnd_4444172 : Nat := 4983230072969 + 3 ^ 40 * 4444172 * 2
def baseEnd_4444172 : Nat := 2281996347253291390311631

theorem tailTrace_4444172 : CollatzResearch.WordTrace tailWord_4444172 prefixEnd_4444172 2281996347253291390311631 := by
  unfold tailWord_4444172
  simp only [CollatzResearch.WordTrace]
  refine ⟨81046134627765661497651385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108061512837020881996868513 81046134627765661497651385)
  ·
    refine ⟨60784600970824246123238539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81046134627765661497651385 60784600970824246123238539)
    ·
      refine ⟨91176901456236369184857809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60784600970824246123238539 91176901456236369184857809)
      ·
        refine ⟨68382676092177276888643357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91176901456236369184857809 68382676092177276888643357)
        ·
          refine ⟨25643503534566478833241259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68382676092177276888643357 25643503534566478833241259)
          ·
            refine ⟨38465255301849718249861889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25643503534566478833241259 38465255301849718249861889)
            ·
              refine ⟨28848941476387288687396417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38465255301849718249861889 28848941476387288687396417)
              ·
                refine ⟨21636706107290466515547313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28848941476387288687396417 21636706107290466515547313)
                ·
                  refine ⟨16227529580467849886660485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21636706107290466515547313 16227529580467849886660485)
                  ·
                    refine ⟨3042661796337721853748841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16227529580467849886660485 3042661796337721853748841)
                    ·
                      refine ⟨2281996347253291390311631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042661796337721853748841 2281996347253291390311631)
                      ·
                        rfl

theorem cell23_4444172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_4444172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444172 prefixEnd_4444172 := by exact prefixLift 4444172
  have htrace : WordTrace (prefixWord ++ tailWord_4444172) baseStart_4444172 baseEnd_4444172 := by
    simpa [prefixWord, tailWord_4444172, baseEnd_4444172] using wordTrace_append hprefix tailTrace_4444172
  have hstable : (prefixWord ++ tailWord_4444172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444172).length < 2 ^ (prefixWord ++ tailWord_4444172).sum := by decide
  have hdescent : baseEnd_4444172 < baseStart_4444172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444173 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4444173 : Nat := 118140960795 + 4444173 * 2 ^ 59
def prefixEnd_4444173 : Nat := 4983230072969 + 3 ^ 40 * 4444173 * 2
def baseEnd_4444173 : Nat := 253555206748216209599903

theorem tailTrace_4444173 : CollatzResearch.WordTrace tailWord_4444173 prefixEnd_4444173 253555206748216209599903 := by
  unfold tailWord_4444173
  simp only [CollatzResearch.WordTrace]
  refine ⟨162092305728527700166089173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108061537152351800110726115 162092305728527700166089173)
  ·
    refine ⟨3799038415512367972642715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 162092305728527700166089173 3799038415512367972642715)
    ·
      refine ⟨5698557623268551958964073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3799038415512367972642715 5698557623268551958964073)
      ·
        refine ⟨4273918217451413969223055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5698557623268551958964073 4273918217451413969223055)
        ·
          refine ⟨6410877326177120953834583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273918217451413969223055 6410877326177120953834583)
          ·
            refine ⟨9616315989265681430751875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410877326177120953834583 9616315989265681430751875)
            ·
              refine ⟨14424473983898522146127813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9616315989265681430751875 14424473983898522146127813)
              ·
                refine ⟨2704588871980972902398965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14424473983898522146127813 2704588871980972902398965)
                ·
                  refine ⟨253555206748216209599903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2704588871980972902398965 253555206748216209599903)
                  ·
                    rfl

theorem cell23_4444173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4444173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444173 prefixEnd_4444173 := by exact prefixLift 4444173
  have htrace : WordTrace (prefixWord ++ tailWord_4444173) baseStart_4444173 baseEnd_4444173 := by
    simpa [prefixWord, tailWord_4444173, baseEnd_4444173] using wordTrace_append hprefix tailTrace_4444173
  have hstable : (prefixWord ++ tailWord_4444173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444173).length < 2 ^ (prefixWord ++ tailWord_4444173).sum := by decide
  have hdescent : baseEnd_4444173 < baseStart_4444173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444189 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_4444189 : Nat := 118140960795 + 4444189 * 2 ^ 59
def prefixEnd_4444189 : Nat := 4983230072969 + 3 ^ 40 * 4444189 * 2
def baseEnd_4444189 : Nat := 2282005076424417823799053

theorem tailTrace_4444189 : CollatzResearch.WordTrace tailWord_4444189 prefixEnd_4444189 2282005076424417823799053 := by
  unfold tailWord_4444189
  simp only [CollatzResearch.WordTrace]
  refine ⟨162092889296469734898671621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108061926197646489932447747 162092889296469734898671621)
  ·
    refine ⟨30392416743088075293500929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162092889296469734898671621 30392416743088075293500929)
    ·
      refine ⟨22794312557316056470125697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30392416743088075293500929 22794312557316056470125697)
      ·
        refine ⟨17095734417987042352594273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22794312557316056470125697 17095734417987042352594273)
        ·
          refine ⟨12821800813490281764445705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17095734417987042352594273 12821800813490281764445705)
          ·
            refine ⟨9616350610117711323334279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12821800813490281764445705 9616350610117711323334279)
            ·
              refine ⟨14424525915176566985001419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9616350610117711323334279 14424525915176566985001419)
              ·
                refine ⟨21636788872764850477502129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14424525915176566985001419 21636788872764850477502129)
                ·
                  refine ⟨16227591654573637858126597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21636788872764850477502129 16227591654573637858126597)
                  ·
                    refine ⟨3042673435232557098398737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16227591654573637858126597 3042673435232557098398737)
                    ·
                      refine ⟨2282005076424417823799053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042673435232557098398737 2282005076424417823799053)
                      ·
                        rfl

theorem cell23_4444189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_4444189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444189 prefixEnd_4444189 := by exact prefixLift 4444189
  have htrace : WordTrace (prefixWord ++ tailWord_4444189) baseStart_4444189 baseEnd_4444189 := by
    simpa [prefixWord, tailWord_4444189, baseEnd_4444189] using wordTrace_append hprefix tailTrace_4444189
  have hstable : (prefixWord ++ tailWord_4444189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444189).length < 2 ^ (prefixWord ++ tailWord_4444189).sum := by decide
  have hdescent : baseEnd_4444189 < baseStart_4444189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444195 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 6]
def baseStart_4444195 : Nat := 118140960795 + 4444195 * 2 ^ 59
def prefixEnd_4444195 : Nat := 4983230072969 + 3 ^ 40 * 4444195 * 2
def baseEnd_4444195 : Nat := 253556461923149422258225

theorem tailTrace_4444195 : CollatzResearch.WordTrace tailWord_4444195 prefixEnd_4444195 253556461923149422258225 := by
  unfold tailWord_4444195
  simp only [CollatzResearch.WordTrace]
  refine ⟨162093108134447997923390039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108062072089631998615593359 162093108134447997923390039)
  ·
    refine ⟨243139662201671996885085059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162093108134447997923390039 243139662201671996885085059)
    ·
      refine ⟨364709493302507995327627589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243139662201671996885085059 364709493302507995327627589)
      ·
        refine ⟨68383029994220249123930173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 364709493302507995327627589 68383029994220249123930173)
        ·
          refine ⟨25643636247832593421473815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68383029994220249123930173 25643636247832593421473815)
          ·
            refine ⟨38465454371748890132210723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25643636247832593421473815 38465454371748890132210723)
            ·
              refine ⟨57698181557623335198316085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38465454371748890132210723 57698181557623335198316085)
              ·
                refine ⟨5409204521027187674842133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57698181557623335198316085 5409204521027187674842133)
                ·
                  refine ⟨253556461923149422258225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5409204521027187674842133 253556461923149422258225)
                  ·
                    rfl

theorem cell23_4444195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 6].length) (baseStart_4444195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444195 prefixEnd_4444195 := by exact prefixLift 4444195
  have htrace : WordTrace (prefixWord ++ tailWord_4444195) baseStart_4444195 baseEnd_4444195 := by
    simpa [prefixWord, tailWord_4444195, baseEnd_4444195] using wordTrace_append hprefix tailTrace_4444195
  have hstable : (prefixWord ++ tailWord_4444195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444195).length < 2 ^ (prefixWord ++ tailWord_4444195).sum := by decide
  have hdescent : baseEnd_4444195 < baseStart_4444195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444209 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_4444209 : Nat := 118140960795 + 4444209 * 2 ^ 59
def prefixEnd_4444209 : Nat := 4983230072969 + 3 ^ 40 * 4444209 * 2
def baseEnd_4444209 : Nat := 2282015346037507745548961

theorem tailTrace_4444209 : CollatzResearch.WordTrace tailWord_4444209 prefixEnd_4444209 2282015346037507745548961 := by
  unfold tailWord_4444209
  simp only [CollatzResearch.WordTrace]
  refine ⟨162093618756397278314399681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108062412504264852209599787 162093618756397278314399681)
  ·
    refine ⟨121570214067297958735799761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162093618756397278314399681 121570214067297958735799761)
    ·
      refine ⟨91177660550473469051849821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121570214067297958735799761 91177660550473469051849821)
      ·
        refine ⟨34191622706427550894443683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91177660550473469051849821 34191622706427550894443683)
        ·
          refine ⟨51287434059641326341665525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34191622706427550894443683 51287434059641326341665525)
          ·
            refine ⟨4808196943091374344531143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51287434059641326341665525 4808196943091374344531143)
            ·
              refine ⟨7212295414637061516796715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808196943091374344531143 7212295414637061516796715)
              ·
                refine ⟨10818443121955592275195073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212295414637061516796715 10818443121955592275195073)
                ·
                  refine ⟨8113832341466694206396305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10818443121955592275195073 8113832341466694206396305)
                  ·
                    refine ⟨6085374256100020654797229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8113832341466694206396305 6085374256100020654797229)
                    ·
                      refine ⟨2282015346037507745548961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085374256100020654797229 2282015346037507745548961)
                      ·
                        rfl

theorem cell23_4444209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_4444209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444209 prefixEnd_4444209 := by exact prefixLift 4444209
  have htrace : WordTrace (prefixWord ++ tailWord_4444209) baseStart_4444209 baseEnd_4444209 := by
    simpa [prefixWord, tailWord_4444209, baseEnd_4444209] using wordTrace_append hprefix tailTrace_4444209
  have hstable : (prefixWord ++ tailWord_4444209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444209).length < 2 ^ (prefixWord ++ tailWord_4444209).sum := by decide
  have hdescent : baseEnd_4444209 < baseStart_4444209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444216 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 1, 4]
def baseStart_4444216 : Nat := 118140960795 + 4444216 * 2 ^ 59
def prefixEnd_4444216 : Nat := 4983230072969 + 3 ^ 40 * 4444216 * 2
def baseEnd_4444216 : Nat := 760672980134029739387143

theorem tailTrace_4444216 : CollatzResearch.WordTrace tailWord_4444216 prefixEnd_4444216 760672980134029739387143 := by
  unfold tailWord_4444216
  simp only [CollatzResearch.WordTrace]
  refine ⟨81046937033685959254952251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108062582711581279006603001 81046937033685959254952251)
  ·
    refine ⟨121570405550528938882428377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81046937033685959254952251 121570405550528938882428377)
    ·
      refine ⟨91177804162896704161821283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121570405550528938882428377 91177804162896704161821283)
      ·
        refine ⟨136766706244345056242731925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91177804162896704161821283 136766706244345056242731925)
        ·
          refine ⟨6410939355203674511378059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136766706244345056242731925 6410939355203674511378059)
          ·
            refine ⟨9616409032805511767067089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410939355203674511378059 9616409032805511767067089)
            ·
              refine ⟨7212306774604133825300317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9616409032805511767067089 7212306774604133825300317)
              ·
                refine ⟨2704615040476550184487619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7212306774604133825300317 2704615040476550184487619)
                ·
                  refine ⟨4056922560714825276731429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704615040476550184487619 4056922560714825276731429)
                  ·
                    refine ⟨760672980134029739387143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4056922560714825276731429 760672980134029739387143)
                    ·
                      rfl

theorem cell23_4444216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_4444216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444216 prefixEnd_4444216 := by exact prefixLift 4444216
  have htrace : WordTrace (prefixWord ++ tailWord_4444216) baseStart_4444216 baseEnd_4444216 := by
    simpa [prefixWord, tailWord_4444216, baseEnd_4444216] using wordTrace_append hprefix tailTrace_4444216
  have hstable : (prefixWord ++ tailWord_4444216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444216).length < 2 ^ (prefixWord ++ tailWord_4444216).sum := by decide
  have hdescent : baseEnd_4444216 < baseStart_4444216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444255 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 1, 6]
def baseStart_4444255 : Nat := 118140960795 + 4444255 * 2 ^ 59
def prefixEnd_4444255 : Nat := 4983230072969 + 3 ^ 40 * 4444255 * 2
def baseEnd_4444255 : Nat := 760679655382538188524583

theorem tailTrace_4444255 : CollatzResearch.WordTrace tailWord_4444255 prefixEnd_4444255 760679655382538188524583 := by
  unfold tailWord_4444255
  simp only [CollatzResearch.WordTrace]
  refine ⟨162095296514230628170574219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108063531009487085447049479 162095296514230628170574219)
  ·
    refine ⟨243142944771345942255861329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162095296514230628170574219 243142944771345942255861329)
    ·
      refine ⟨182357208578509456691895997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243142944771345942255861329 182357208578509456691895997)
      ·
        refine ⟨68383953216941046259460999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182357208578509456691895997 68383953216941046259460999)
        ·
          refine ⟨102575929825411569389191499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68383953216941046259460999 102575929825411569389191499)
          ·
            refine ⟨153863894738117354083787249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102575929825411569389191499 153863894738117354083787249)
            ·
              refine ⟨115397921053588015562840437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153863894738117354083787249 115397921053588015562840437)
              ·
                refine ⟨10818555098773876459016291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115397921053588015562840437 10818555098773876459016291)
                ·
                  refine ⟨16227832648160814688524437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10818555098773876459016291 16227832648160814688524437)
                  ·
                    refine ⟨760679655382538188524583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16227832648160814688524437 760679655382538188524583)
                    ·
                      rfl

theorem cell23_4444255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_4444255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444255 prefixEnd_4444255 := by exact prefixLift 4444255
  have htrace : WordTrace (prefixWord ++ tailWord_4444255) baseStart_4444255 baseEnd_4444255 := by
    simpa [prefixWord, tailWord_4444255, baseEnd_4444255] using wordTrace_append hprefix tailTrace_4444255
  have hstable : (prefixWord ++ tailWord_4444255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444255).length < 2 ^ (prefixWord ++ tailWord_4444255).sum := by decide
  have hdescent : baseEnd_4444255 < baseStart_4444255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444265 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_4444265 : Nat := 118140960795 + 4444265 * 2 ^ 59
def prefixEnd_4444265 : Nat := 4983230072969 + 3 ^ 40 * 4444265 * 2
def baseEnd_4444265 : Nat := 2282044100954159526448703

theorem tailTrace_4444265 : CollatzResearch.WordTrace tailWord_4444265 prefixEnd_4444265 2282044100954159526448703 := by
  unfold tailWord_4444265
  simp only [CollatzResearch.WordTrace]
  refine ⟨162095661244194399878438249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108063774162796266585625499 162095661244194399878438249)
  ·
    refine ⟨121571745933145799908828687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162095661244194399878438249 121571745933145799908828687)
    ·
      refine ⟨182357618899718699863243031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121571745933145799908828687 182357618899718699863243031)
      ·
        refine ⟨273536428349578049794864547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182357618899718699863243031 273536428349578049794864547)
        ·
          refine ⟨410304642524367074692296821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273536428349578049794864547 410304642524367074692296821)
          ·
            refine ⟨38466060236659413252402827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 410304642524367074692296821 38466060236659413252402827)
            ·
              refine ⟨57699090354989119878604241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38466060236659413252402827 57699090354989119878604241)
              ·
                refine ⟨43274317766241839908953181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57699090354989119878604241 43274317766241839908953181)
                ·
                  refine ⟨16227869162340689965857443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43274317766241839908953181 16227869162340689965857443)
                  ·
                    refine ⟨24341803743511034948786165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16227869162340689965857443 24341803743511034948786165)
                    ·
                      refine ⟨2282044100954159526448703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24341803743511034948786165 2282044100954159526448703)
                      ·
                        rfl

theorem cell23_4444265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_4444265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444265 prefixEnd_4444265 := by exact prefixLift 4444265
  have htrace : WordTrace (prefixWord ++ tailWord_4444265) baseStart_4444265 baseEnd_4444265 := by
    simpa [prefixWord, tailWord_4444265, baseEnd_4444265] using wordTrace_append hprefix tailTrace_4444265
  have hstable : (prefixWord ++ tailWord_4444265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444265).length < 2 ^ (prefixWord ++ tailWord_4444265).sum := by decide
  have hdescent : baseEnd_4444265 < baseStart_4444265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444272 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 4, 4]
def baseStart_4444272 : Nat := 118140960795 + 4444272 * 2 ^ 59
def prefixEnd_4444272 : Nat := 4983230072969 + 3 ^ 40 * 4444272 * 2
def baseEnd_4444272 : Nat := 760682565106246999687057

theorem tailTrace_4444272 : CollatzResearch.WordTrace tailWord_4444272 prefixEnd_4444272 760682565106246999687057 := by
  unfold tailWord_4444272
  simp only [CollatzResearch.WordTrace]
  refine ⟨81047958277584520036971535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108063944370112693382628713 81047958277584520036971535)
  ·
    refine ⟨121571937416376780055457303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81047958277584520036971535 121571937416376780055457303)
    ·
      refine ⟨182357906124565170083185955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121571937416376780055457303 182357906124565170083185955)
      ·
        refine ⟨273536859186847755124778933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182357906124565170083185955 273536859186847755124778933)
        ·
          refine ⟨25644080548766977042948025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 273536859186847755124778933 25644080548766977042948025)
          ·
            refine ⟨19233060411575232782211019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25644080548766977042948025 19233060411575232782211019)
            ·
              refine ⟨28849590617362849173316529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19233060411575232782211019 28849590617362849173316529)
              ·
                refine ⟨21637192963022136879987397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28849590617362849173316529 21637192963022136879987397)
                ·
                  refine ⟨4056973680566650664997637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21637192963022136879987397 4056973680566650664997637)
                  ·
                    refine ⟨760682565106246999687057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4056973680566650664997637 760682565106246999687057)
                    ·
                      rfl

theorem cell23_4444272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_4444272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444272 prefixEnd_4444272 := by exact prefixLift 4444272
  have htrace : WordTrace (prefixWord ++ tailWord_4444272) baseStart_4444272 baseEnd_4444272 := by
    simpa [prefixWord, tailWord_4444272, baseEnd_4444272] using wordTrace_append hprefix tailTrace_4444272
  have hstable : (prefixWord ++ tailWord_4444272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444272).length < 2 ^ (prefixWord ++ tailWord_4444272).sum := by decide
  have hdescent : baseEnd_4444272 < baseStart_4444272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444285 : List Nat := [1, 4, 1, 1, 3, 2, 11]
def baseStart_4444285 : Nat := 118140960795 + 4444285 * 2 ^ 59
def prefixEnd_4444285 : Nat := 4983230072969 + 3 ^ 40 * 4444285 * 2
def baseEnd_4444285 : Nat := 28173510747743820348131

theorem tailTrace_4444285 : CollatzResearch.WordTrace tailWord_4444285 prefixEnd_4444285 28173510747743820348131 := by
  unfold tailWord_4444285
  simp only [CollatzResearch.WordTrace]
  refine ⟨162096390704121943294166309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108064260469414628862777539 162096390704121943294166309)
  ·
    refine ⟨30393073257022864367656183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162096390704121943294166309 30393073257022864367656183)
    ·
      refine ⟨45589609885534296551484275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30393073257022864367656183 45589609885534296551484275)
      ·
        refine ⟨68384414828301444827226413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45589609885534296551484275 68384414828301444827226413)
        ·
          refine ⟨25644155560613041810209905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68384414828301444827226413 25644155560613041810209905)
          ·
            refine ⟨19233116670459781357657429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25644155560613041810209905 19233116670459781357657429)
            ·
              refine ⟨28173510747743820348131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19233116670459781357657429 28173510747743820348131)
              ·
                rfl

theorem cell23_4444285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 11].length) (baseStart_4444285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444285 prefixEnd_4444285 := by exact prefixLift 4444285
  have htrace : WordTrace (prefixWord ++ tailWord_4444285) baseStart_4444285 baseEnd_4444285 := by
    simpa [prefixWord, tailWord_4444285, baseEnd_4444285] using wordTrace_append hprefix tailTrace_4444285
  have hstable : (prefixWord ++ tailWord_4444285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444285).length < 2 ^ (prefixWord ++ tailWord_4444285).sum := by decide
  have hdescent : baseEnd_4444285 < baseStart_4444285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444310 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4444310 : Nat := 118140960795 + 4444310 * 2 ^ 59
def prefixEnd_4444310 : Nat := 4983230072969 + 3 ^ 40 * 4444310 * 2
def baseEnd_4444310 : Nat := 760689069194537283461999

theorem tailTrace_4444310 : CollatzResearch.WordTrace tailWord_4444310 prefixEnd_4444310 760689069194537283461999 := by
  unfold tailWord_4444310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10131081408064460785239149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108064868352687581709217589 10131081408064460785239149)
  ·
    refine ⟨3799155528024172794464681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10131081408064460785239149 3799155528024172794464681)
    ·
      refine ⟨2849366646018129595848511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3799155528024172794464681 2849366646018129595848511)
      ·
        refine ⟨4274049969027194393772767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849366646018129595848511 4274049969027194393772767)
        ·
          refine ⟨6411074953540791590659151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4274049969027194393772767 6411074953540791590659151)
          ·
            refine ⟨9616612430311187385988727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6411074953540791590659151 9616612430311187385988727)
            ·
              refine ⟨14424918645466781078983091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9616612430311187385988727 14424918645466781078983091)
              ·
                refine ⟨21637377968200171618474637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14424918645466781078983091 21637377968200171618474637)
                ·
                  refine ⟨8114016738075064356927989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21637377968200171618474637 8114016738075064356927989)
                  ·
                    refine ⟨760689069194537283461999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8114016738075064356927989 760689069194537283461999)
                    ·
                      rfl

theorem cell23_4444310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4444310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444310 prefixEnd_4444310 := by exact prefixLift 4444310
  have htrace : WordTrace (prefixWord ++ tailWord_4444310) baseStart_4444310 baseEnd_4444310 := by
    simpa [prefixWord, tailWord_4444310, baseEnd_4444310] using wordTrace_append hprefix tailTrace_4444310
  have hstable : (prefixWord ++ tailWord_4444310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444310).length < 2 ^ (prefixWord ++ tailWord_4444310).sum := by decide
  have hdescent : baseEnd_4444310 < baseStart_4444310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444333 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_4444333 : Nat := 118140960795 + 4444333 * 2 ^ 59
def prefixEnd_4444333 : Nat := 4983230072969 + 3 ^ 40 * 4444333 * 2
def baseEnd_4444333 : Nat := 2282079017638665260398391

theorem tailTrace_4444333 : CollatzResearch.WordTrace tailWord_4444333 prefixEnd_4444333 2282079017638665260398391 := by
  unfold tailWord_4444333
  simp only [CollatzResearch.WordTrace]
  refine ⟨162098141407948047491913653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108065427605298698327942435 162098141407948047491913653)
  ·
    refine ⟨15196700756995129452366905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162098141407948047491913653 15196700756995129452366905)
    ·
      refine ⟨11397525567746347089275179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15196700756995129452366905 11397525567746347089275179)
      ·
        refine ⟨17096288351619520633912769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11397525567746347089275179 17096288351619520633912769)
        ·
          refine ⟨12822216263714640475434577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17096288351619520633912769 12822216263714640475434577)
          ·
            refine ⟨9616662197785980356575933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12822216263714640475434577 9616662197785980356575933)
            ·
              refine ⟨3606248324169742633715975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9616662197785980356575933 3606248324169742633715975)
              ·
                refine ⟨5409372486254613950573963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606248324169742633715975 5409372486254613950573963)
                ·
                  refine ⟨8114058729381920925860945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5409372486254613950573963 8114058729381920925860945)
                  ·
                    refine ⟨6085544047036440694395709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8114058729381920925860945 6085544047036440694395709)
                    ·
                      refine ⟨2282079017638665260398391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085544047036440694395709 2282079017638665260398391)
                      ·
                        rfl

theorem cell23_4444333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_4444333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444333 prefixEnd_4444333 := by exact prefixLift 4444333
  have htrace : WordTrace (prefixWord ++ tailWord_4444333) baseStart_4444333 baseEnd_4444333 := by
    simpa [prefixWord, tailWord_4444333, baseEnd_4444333] using wordTrace_append hprefix tailTrace_4444333
  have hstable : (prefixWord ++ tailWord_4444333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444333).length < 2 ^ (prefixWord ++ tailWord_4444333).sum := by decide
  have hdescent : baseEnd_4444333 < baseStart_4444333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444352 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_4444352 : Nat := 118140960795 + 4444352 * 2 ^ 59
def prefixEnd_4444352 : Nat := 4983230072969 + 3 ^ 40 * 4444352 * 2
def baseEnd_4444352 : Nat := 2282088773771100686060803

theorem tailTrace_4444352 : CollatzResearch.WordTrace tailWord_4444352 prefixEnd_4444352 2282088773771100686060803 := by
  unfold tailWord_4444352
  simp only [CollatzResearch.WordTrace]
  refine ⟨81049417197439606868427655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108065889596586142491236873 81049417197439606868427655)
  ·
    refine ⟨121574125796159410302641483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81049417197439606868427655 121574125796159410302641483)
    ·
      refine ⟨182361188694239115453962225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121574125796159410302641483 182361188694239115453962225)
      ·
        refine ⟨136770891520679336590471669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182361188694239115453962225 136770891520679336590471669)
        ·
          refine ⟨12822271080063687805356719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136770891520679336590471669 12822271080063687805356719)
          ·
            refine ⟨19233406620095531708035079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12822271080063687805356719 19233406620095531708035079)
            ·
              refine ⟨28850109930143297562052619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19233406620095531708035079 28850109930143297562052619)
              ·
                refine ⟨43275164895214946343078929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28850109930143297562052619 43275164895214946343078929)
                ·
                  refine ⟨32456373671411209757309197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43275164895214946343078929 32456373671411209757309197)
                  ·
                    refine ⟨12171140126779203658990949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32456373671411209757309197 12171140126779203658990949)
                    ·
                      refine ⟨2282088773771100686060803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12171140126779203658990949 2282088773771100686060803)
                      ·
                        rfl

theorem cell23_4444352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_4444352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444352 prefixEnd_4444352 := by exact prefixLift 4444352
  have htrace : WordTrace (prefixWord ++ tailWord_4444352) baseStart_4444352 baseEnd_4444352 := by
    simpa [prefixWord, tailWord_4444352, baseEnd_4444352] using wordTrace_append hprefix tailTrace_4444352
  have hstable : (prefixWord ++ tailWord_4444352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444352).length < 2 ^ (prefixWord ++ tailWord_4444352).sum := by decide
  have hdescent : baseEnd_4444352 < baseStart_4444352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444356 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_4444356 : Nat := 118140960795 + 4444356 * 2 ^ 59
def prefixEnd_4444356 : Nat := 4983230072969 + 3 ^ 40 * 4444356 * 2
def baseEnd_4444356 : Nat := 2282090827693718670410785

theorem tailTrace_4444356 : CollatzResearch.WordTrace tailWord_4444356 prefixEnd_4444356 2282090827693718670410785 := by
  unfold tailWord_4444356
  simp only [CollatzResearch.WordTrace]
  refine ⟨81049490143432361210000461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108065986857909814946667281 81049490143432361210000461)
  ·
    refine ⟨30393558803787135453750173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81049490143432361210000461 30393558803787135453750173)
    ·
      refine ⟨11397584551420175795156315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30393558803787135453750173 11397584551420175795156315)
      ·
        refine ⟨17096376827130263692734473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11397584551420175795156315 17096376827130263692734473)
        ·
          refine ⟨12822282620347697769550855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17096376827130263692734473 12822282620347697769550855)
          ·
            refine ⟨19233423930521546654326283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12822282620347697769550855 19233423930521546654326283)
            ·
              refine ⟨28850135895782319981489425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19233423930521546654326283 28850135895782319981489425)
              ·
                refine ⟨21637601921836739986117069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28850135895782319981489425 21637601921836739986117069)
                ·
                  refine ⟨8114100720688777494793901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21637601921836739986117069 8114100720688777494793901)
                  ·
                    refine ⟨3042787770258291560547713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8114100720688777494793901 3042787770258291560547713)
                    ·
                      refine ⟨2282090827693718670410785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042787770258291560547713 2282090827693718670410785)
                      ·
                        rfl

theorem cell23_4444356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_4444356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444356 prefixEnd_4444356 := by exact prefixLift 4444356
  have htrace : WordTrace (prefixWord ++ tailWord_4444356) baseStart_4444356 baseEnd_4444356 := by
    simpa [prefixWord, tailWord_4444356, baseEnd_4444356] using wordTrace_append hprefix tailTrace_4444356
  have hstable : (prefixWord ++ tailWord_4444356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444356).length < 2 ^ (prefixWord ++ tailWord_4444356).sum := by decide
  have hdescent : baseEnd_4444356 < baseStart_4444356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444362 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_4444362 : Nat := 118140960795 + 4444362 * 2 ^ 59
def prefixEnd_4444362 : Nat := 4983230072969 + 3 ^ 40 * 4444362 * 2
def baseEnd_4444362 : Nat := 760697969525881882311919

theorem tailTrace_4444362 : CollatzResearch.WordTrace tailWord_4444362 prefixEnd_4444362 760697969525881882311919 := by
  unfold tailWord_4444362
  simp only [CollatzResearch.WordTrace]
  refine ⟨40524799781210746361179835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108066132749895323629812893 40524799781210746361179835)
  ·
    refine ⟨60787199671816119541769753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40524799781210746361179835 60787199671816119541769753)
    ·
      refine ⟨45590399753862089656327315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60787199671816119541769753 45590399753862089656327315)
      ·
        refine ⟨68385599630793134484490973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45590399753862089656327315 68385599630793134484490973)
        ·
          refine ⟨25644599861547425431684115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68385599630793134484490973 25644599861547425431684115)
          ·
            refine ⟨38466899792321138147526173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25644599861547425431684115 38466899792321138147526173)
            ·
              refine ⟨14425087422120426805322315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38466899792321138147526173 14425087422120426805322315)
              ·
                refine ⟨21637631133180640207983473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14425087422120426805322315 21637631133180640207983473)
                ·
                  refine ⟨16228223349885480155987605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21637631133180640207983473 16228223349885480155987605)
                  ·
                    refine ⟨760697969525881882311919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16228223349885480155987605 760697969525881882311919)
                    ·
                      rfl

theorem cell23_4444362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_4444362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444362 prefixEnd_4444362 := by exact prefixLift 4444362
  have htrace : WordTrace (prefixWord ++ tailWord_4444362) baseStart_4444362 baseEnd_4444362 := by
    simpa [prefixWord, tailWord_4444362, baseEnd_4444362] using wordTrace_append hprefix tailTrace_4444362
  have hstable : (prefixWord ++ tailWord_4444362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444362).length < 2 ^ (prefixWord ++ tailWord_4444362).sum := by decide
  have hdescent : baseEnd_4444362 < baseStart_4444362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444369 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 1, 4, 2]
def baseStart_4444369 : Nat := 118140960795 + 4444369 * 2 ^ 59
def prefixEnd_4444369 : Nat := 4983230072969 + 3 ^ 40 * 4444369 * 2
def baseEnd_4444369 : Nat := 2282097502942227119548225

theorem tailTrace_4444369 : CollatzResearch.WordTrace tailWord_4444369 prefixEnd_4444369 2282097502942227119548225 := by
  unfold tailWord_4444369
  simp only [CollatzResearch.WordTrace]
  refine ⟨162099454435817625640224161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108066302957211750426816107 162099454435817625640224161)
  ·
    refine ⟨121574590826863219230168121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162099454435817625640224161 121574590826863219230168121)
    ·
      refine ⟨91180943120147414422626091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121574590826863219230168121 91180943120147414422626091)
      ·
        refine ⟨136771414680221121633939137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91180943120147414422626091 136771414680221121633939137)
        ·
          refine ⟨102578561010165841225454353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136771414680221121633939137 102578561010165841225454353)
          ·
            refine ⟨76933920757624380919090765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102578561010165841225454353 76933920757624380919090765)
            ·
              refine ⟨28850220284109142844659037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76933920757624380919090765 28850220284109142844659037)
              ·
                refine ⟨10818832606540928566747139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28850220284109142844659037 10818832606540928566747139)
                ·
                  refine ⟨16228248909811392850120709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10818832606540928566747139 16228248909811392850120709)
                  ·
                    refine ⟨3042796670589636159397633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16228248909811392850120709 3042796670589636159397633)
                    ·
                      refine ⟨2282097502942227119548225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042796670589636159397633 2282097502942227119548225)
                      ·
                        rfl

theorem cell23_4444369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_4444369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444369 prefixEnd_4444369 := by exact prefixLift 4444369
  have htrace : WordTrace (prefixWord ++ tailWord_4444369) baseStart_4444369 baseEnd_4444369 := by
    simpa [prefixWord, tailWord_4444369, baseEnd_4444369] using wordTrace_append hprefix tailTrace_4444369
  have hstable : (prefixWord ++ tailWord_4444369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444369).length < 2 ^ (prefixWord ++ tailWord_4444369).sum := by decide
  have hdescent : baseEnd_4444369 < baseStart_4444369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444420 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_4444420 : Nat := 118140960795 + 4444420 * 2 ^ 59
def prefixEnd_4444420 : Nat := 4983230072969 + 3 ^ 40 * 4444420 * 2
def baseEnd_4444420 : Nat := 2282123690455606420010491

theorem tailTrace_4444420 : CollatzResearch.WordTrace tailWord_4444420 prefixEnd_4444420 2282123690455606420010491 := by
  unfold tailWord_4444420
  simp only [CollatzResearch.WordTrace]
  refine ⟨81050657279316430675165357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108067543039088574233553809 81050657279316430675165357)
  ·
    refine ⟨30393996479743661503187009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81050657279316430675165357 30393996479743661503187009)
    ·
      refine ⟨22795497359807746127390257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30393996479743661503187009 22795497359807746127390257)
      ·
        refine ⟨17096623019855809595542693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22795497359807746127390257 17096623019855809595542693)
        ·
          refine ⟨3205616816222964299164255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17096623019855809595542693 3205616816222964299164255)
          ·
            refine ⟨4808425224334446448746383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205616816222964299164255 4808425224334446448746383)
            ·
              refine ⟨7212637836501669673119575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808425224334446448746383 7212637836501669673119575)
              ·
                refine ⟨10818956754752504509679363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212637836501669673119575 10818956754752504509679363)
                ·
                  refine ⟨16228435132128756764519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10818956754752504509679363 16228435132128756764519045)
                  ·
                    refine ⟨3042831587274141893347321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16228435132128756764519045 3042831587274141893347321)
                    ·
                      refine ⟨2282123690455606420010491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042831587274141893347321 2282123690455606420010491)
                      ·
                        rfl

theorem cell23_4444420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_4444420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444420 prefixEnd_4444420 := by exact prefixLift 4444420
  have htrace : WordTrace (prefixWord ++ tailWord_4444420) baseStart_4444420 baseEnd_4444420 := by
    simpa [prefixWord, tailWord_4444420, baseEnd_4444420] using wordTrace_append hprefix tailTrace_4444420
  have hstable : (prefixWord ++ tailWord_4444420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444420).length < 2 ^ (prefixWord ++ tailWord_4444420).sum := by decide
  have hdescent : baseEnd_4444420 < baseStart_4444420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444456 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 2, 5]
def baseStart_4444456 : Nat := 118140960795 + 4444456 * 2 ^ 59
def prefixEnd_4444456 : Nat := 4983230072969 + 3 ^ 40 * 4444456 * 2
def baseEnd_4444456 : Nat := 760714058586389426386775

theorem tailTrace_4444456 : CollatzResearch.WordTrace tailWord_4444456 prefixEnd_4444456 760714058586389426386775 := by
  unfold tailWord_4444456
  simp only [CollatzResearch.WordTrace]
  refine ⟨81051313793251219749320611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108068418391001626332427481 81051313793251219749320611)
  ·
    refine ⟨121576970689876829623980917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81051313793251219749320611 121576970689876829623980917)
    ·
      refine ⟨11397841002175952777248211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121576970689876829623980917 11397841002175952777248211)
      ·
        refine ⟨17096761503263929165872317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11397841002175952777248211 17096761503263929165872317)
        ·
          refine ⟨6411285563723973437202119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17096761503263929165872317 6411285563723973437202119)
          ·
            refine ⟨9616928345585960155803179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6411285563723973437202119 9616928345585960155803179)
            ·
              refine ⟨14425392518378940233704769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9616928345585960155803179 14425392518378940233704769)
              ·
                refine ⟨10819044388784205175278577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14425392518378940233704769 10819044388784205175278577)
                ·
                  refine ⟨8114283291588153881458933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10819044388784205175278577 8114283291588153881458933)
                  ·
                    refine ⟨760714058586389426386775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8114283291588153881458933 760714058586389426386775)
                    ·
                      rfl

theorem cell23_4444456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_4444456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444456 prefixEnd_4444456 := by exact prefixLift 4444456
  have htrace : WordTrace (prefixWord ++ tailWord_4444456) baseStart_4444456 baseEnd_4444456 := by
    simpa [prefixWord, tailWord_4444456, baseEnd_4444456] using wordTrace_append hprefix tailTrace_4444456
  have hstable : (prefixWord ++ tailWord_4444456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444456).length < 2 ^ (prefixWord ++ tailWord_4444456).sum := by decide
  have hdescent : baseEnd_4444456 < baseStart_4444456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444472 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_4444472 : Nat := 118140960795 + 4444472 * 2 ^ 59
def prefixEnd_4444472 : Nat := 4983230072969 + 3 ^ 40 * 4444472 * 2
def baseEnd_4444472 : Nat := 2282150391449640216560251

theorem tailTrace_4444472 : CollatzResearch.WordTrace tailWord_4444472 prefixEnd_4444472 2282150391449640216560251 := by
  unfold tailWord_4444472
  simp only [CollatzResearch.WordTrace]
  refine ⟨81051605577222237115611835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108068807436296316154149113 81051605577222237115611835)
  ·
    refine ⟨121577408365833355673417753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81051605577222237115611835 121577408365833355673417753)
    ·
      refine ⟨91183056274375016755063315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121577408365833355673417753 91183056274375016755063315)
      ·
        refine ⟨136774584411562525132594973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91183056274375016755063315 136774584411562525132594973)
        ·
          refine ⟨51290469154335946924723115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136774584411562525132594973 51290469154335946924723115)
          ·
            refine ⟨76935703731503920387084673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51290469154335946924723115 76935703731503920387084673)
            ·
              refine ⟨57701777798627940290313505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76935703731503920387084673 57701777798627940290313505)
              ·
                refine ⟨43276333348970955217735129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57701777798627940290313505 43276333348970955217735129)
                ·
                  refine ⟨32457250011728216413301347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43276333348970955217735129 32457250011728216413301347)
                  ·
                    refine ⟨48685875017592324619952021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32457250011728216413301347 48685875017592324619952021)
                    ·
                      refine ⟨2282150391449640216560251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48685875017592324619952021 2282150391449640216560251)
                      ·
                        rfl

theorem cell23_4444472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_4444472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444472 prefixEnd_4444472 := by exact prefixLift 4444472
  have htrace : WordTrace (prefixWord ++ tailWord_4444472) baseStart_4444472 baseEnd_4444472 := by
    simpa [prefixWord, tailWord_4444472, baseEnd_4444472] using wordTrace_append hprefix tailTrace_4444472
  have hstable : (prefixWord ++ tailWord_4444472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444472).length < 2 ^ (prefixWord ++ tailWord_4444472).sum := by decide
  have hdescent : baseEnd_4444472 < baseStart_4444472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444479 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_4444479 : Nat := 118140960795 + 4444479 * 2 ^ 59
def prefixEnd_4444479 : Nat := 4983230072969 + 3 ^ 40 * 4444479 * 2
def baseEnd_4444479 : Nat := 2282153985814221689172719

theorem tailTrace_4444479 : CollatzResearch.WordTrace tailWord_4444479 prefixEnd_4444479 2282153985814221689172719 := by
  unfold tailWord_4444479
  simp only [CollatzResearch.WordTrace]
  refine ⟨162103466465419114426728491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108068977643612742951152327 162103466465419114426728491)
  ·
    refine ⟨243155199698128671640092737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162103466465419114426728491 243155199698128671640092737)
    ·
      refine ⟨182366399773596503730069553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243155199698128671640092737 182366399773596503730069553)
      ·
        refine ⟨136774799830197377797552165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182366399773596503730069553 136774799830197377797552165)
        ·
          refine ⟨25645274968162008337041031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136774799830197377797552165 25645274968162008337041031)
          ·
            refine ⟨38467912452243012505561547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25645274968162008337041031 38467912452243012505561547)
            ·
              refine ⟨57701868678364518758342321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38467912452243012505561547 57701868678364518758342321)
              ·
                refine ⟨43276401508773389068756741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57701868678364518758342321 43276401508773389068756741)
                ·
                  refine ⟨8114325282895010450391889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43276401508773389068756741 8114325282895010450391889)
                  ·
                    refine ⟨6085743962171257837793917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8114325282895010450391889 6085743962171257837793917)
                    ·
                      refine ⟨2282153985814221689172719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085743962171257837793917 2282153985814221689172719)
                      ·
                        rfl

theorem cell23_4444479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_4444479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444479 prefixEnd_4444479 := by exact prefixLift 4444479
  have htrace : WordTrace (prefixWord ++ tailWord_4444479) baseStart_4444479 baseEnd_4444479 := by
    simpa [prefixWord, tailWord_4444479, baseEnd_4444479] using wordTrace_append hprefix tailTrace_4444479
  have hstable : (prefixWord ++ tailWord_4444479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444479).length < 2 ^ (prefixWord ++ tailWord_4444479).sum := by decide
  have hdescent : baseEnd_4444479 < baseStart_4444479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444496 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_4444496 : Nat := 118140960795 + 4444496 * 2 ^ 59
def prefixEnd_4444496 : Nat := 4983230072969 + 3 ^ 40 * 4444496 * 2
def baseEnd_4444496 : Nat := 2282162714985348122660141

theorem tailTrace_4444496 : CollatzResearch.WordTrace tailWord_4444496 prefixEnd_4444496 2282162714985348122660141 := by
  unfold tailWord_4444496
  simp only [CollatzResearch.WordTrace]
  refine ⟨81052043253178763165048671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108069391004238350886731561 81052043253178763165048671)
  ·
    refine ⟨121578064879768144747573007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81052043253178763165048671 121578064879768144747573007)
    ·
      refine ⟨182367097319652217121359511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121578064879768144747573007 182367097319652217121359511)
      ·
        refine ⟨273550645979478325682039267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182367097319652217121359511 273550645979478325682039267)
        ·
          refine ⟨410325968969217488523058901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273550645979478325682039267 410325968969217488523058901)
          ·
            refine ⟨9617014897716034887259193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 410325968969217488523058901 9617014897716034887259193)
            ·
              refine ⟨7212761173287026165444395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9617014897716034887259193 7212761173287026165444395)
              ·
                refine ⟨10819141759930539248166593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212761173287026165444395 10819141759930539248166593)
                ·
                  refine ⟨8114356319947904436124945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10819141759930539248166593 8114356319947904436124945)
                  ·
                    refine ⟨6085767239960928327093709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8114356319947904436124945 6085767239960928327093709)
                    ·
                      refine ⟨2282162714985348122660141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085767239960928327093709 2282162714985348122660141)
                      ·
                        rfl

theorem cell23_4444496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_4444496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444496 prefixEnd_4444496 := by exact prefixLift 4444496
  have htrace : WordTrace (prefixWord ++ tailWord_4444496) baseStart_4444496 baseEnd_4444496 := by
    simpa [prefixWord, tailWord_4444496, baseEnd_4444496] using wordTrace_append hprefix tailTrace_4444496
  have hstable : (prefixWord ++ tailWord_4444496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444496).length < 2 ^ (prefixWord ++ tailWord_4444496).sum := by decide
  have hdescent : baseEnd_4444496 < baseStart_4444496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444520 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 1, 4]
def baseStart_4444520 : Nat := 118140960795 + 4444520 * 2 ^ 59
def prefixEnd_4444520 : Nat := 4983230072969 + 3 ^ 40 * 4444520 * 2
def baseEnd_4444520 : Nat := 760725012840352009586677

theorem tailTrace_4444520 : CollatzResearch.WordTrace tailWord_4444520 prefixEnd_4444520 760725012840352009586677 := by
  unfold tailWord_4444520
  simp only [CollatzResearch.WordTrace]
  refine ⟨81052480929135289214485507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108069974572180385619314009 81052480929135289214485507)
  ·
    refine ⟨121578721393702933821728261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81052480929135289214485507 121578721393702933821728261)
    ·
      refine ⟨22796010261319300091574049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121578721393702933821728261 22796010261319300091574049)
      ·
        refine ⟨17097007695989475068680537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22796010261319300091574049 17097007695989475068680537)
        ·
          refine ⟨12822755771992106301510403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17097007695989475068680537 12822755771992106301510403)
          ·
            refine ⟨19234133657988159452265605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12822755771992106301510403 19234133657988159452265605)
            ·
              refine ⟨3606400060872779897299801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19234133657988159452265605 3606400060872779897299801)
              ·
                refine ⟨2704800045654584922974851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3606400060872779897299801 2704800045654584922974851)
                ·
                  refine ⟨4057200068481877384462277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704800045654584922974851 4057200068481877384462277)
                  ·
                    refine ⟨760725012840352009586677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4057200068481877384462277 760725012840352009586677)
                    ·
                      rfl

theorem cell23_4444520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_4444520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444520 prefixEnd_4444520 := by exact prefixLift 4444520
  have htrace : WordTrace (prefixWord ++ tailWord_4444520) baseStart_4444520 baseEnd_4444520 := by
    simpa [prefixWord, tailWord_4444520, baseEnd_4444520] using wordTrace_append hprefix tailTrace_4444520
  have hstable : (prefixWord ++ tailWord_4444520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444520).length < 2 ^ (prefixWord ++ tailWord_4444520).sum := by decide
  have hdescent : baseEnd_4444520 < baseStart_4444520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444553 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 2, 3, 2]
def baseStart_4444553 : Nat := 118140960795 + 4444553 * 2 ^ 59
def prefixEnd_4444553 : Nat := 4983230072969 + 3 ^ 40 * 4444553 * 2
def baseEnd_4444553 : Nat := 2282191983382654399647379

theorem tailTrace_4444553 : CollatzResearch.WordTrace tailWord_4444553 prefixEnd_4444553 2282191983382654399647379 := by
  unfold tailWord_4444553
  simp only [CollatzResearch.WordTrace]
  refine ⟨162106165467151025064922313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108070776978100683376614875 162106165467151025064922313)
  ·
    refine ⟨121579624100363268798691735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162106165467151025064922313 121579624100363268798691735)
    ·
      refine ⟨182369436150544903198037603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121579624100363268798691735 182369436150544903198037603)
      ·
        refine ⟨273554154225817354797056405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182369436150544903198037603 273554154225817354797056405)
        ·
          refine ⟨12822850979335188506112019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 273554154225817354797056405 12822850979335188506112019)
          ·
            refine ⟨19234276469002782759168029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12822850979335188506112019 19234276469002782759168029)
            ·
              refine ⟨7212853675876043534688011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19234276469002782759168029 7212853675876043534688011)
              ·
                refine ⟨10819280513814065302032017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212853675876043534688011 10819280513814065302032017)
                ·
                  refine ⟨8114460385360548976524013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10819280513814065302032017 8114460385360548976524013)
                  ·
                    refine ⟨3042922644510205866196505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8114460385360548976524013 3042922644510205866196505)
                    ·
                      refine ⟨2282191983382654399647379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3042922644510205866196505 2282191983382654399647379)
                      ·
                        rfl

theorem cell23_4444553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 3, 2].length) (baseStart_4444553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444553 prefixEnd_4444553 := by exact prefixLift 4444553
  have htrace : WordTrace (prefixWord ++ tailWord_4444553) baseStart_4444553 baseEnd_4444553 := by
    simpa [prefixWord, tailWord_4444553, baseEnd_4444553] using wordTrace_append hprefix tailTrace_4444553
  have hstable : (prefixWord ++ tailWord_4444553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444553).length < 2 ^ (prefixWord ++ tailWord_4444553).sum := by decide
  have hdescent : baseEnd_4444553 < baseStart_4444553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444569 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_4444569 : Nat := 118140960795 + 4444569 * 2 ^ 59
def prefixEnd_4444569 : Nat := 4983230072969 + 3 ^ 40 * 4444569 * 2
def baseEnd_4444569 : Nat := 2282200199073126337047305

theorem tailTrace_4444569 : CollatzResearch.WordTrace tailWord_4444569 prefixEnd_4444569 2282200199073126337047305 := by
  unfold tailWord_4444569
  simp only [CollatzResearch.WordTrace]
  refine ⟨162106749035093059797504761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108071166023395373198336507 162106749035093059797504761)
  ·
    refine ⟨121580061776319794848128571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162106749035093059797504761 121580061776319794848128571)
    ·
      refine ⟨182370092664479692272192857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121580061776319794848128571 182370092664479692272192857)
      ·
        refine ⟨136777569498359769204144643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182370092664479692272192857 136777569498359769204144643)
        ·
          refine ⟨205166354247539653806216965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136777569498359769204144643 205166354247539653806216965)
          ·
            refine ⟨38468691421413685088665681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205166354247539653806216965 38468691421413685088665681)
            ·
              refine ⟨28851518566060263816499261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38468691421413685088665681 28851518566060263816499261)
              ·
                refine ⟨10819319462272598931187223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28851518566060263816499261 10819319462272598931187223)
                ·
                  refine ⟨16228979193408898396780835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10819319462272598931187223 16228979193408898396780835)
                  ·
                    refine ⟨24343468790113347595171253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16228979193408898396780835 24343468790113347595171253)
                    ·
                      refine ⟨2282200199073126337047305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24343468790113347595171253 2282200199073126337047305)
                      ·
                        rfl

theorem cell23_4444569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_4444569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444569 prefixEnd_4444569 := by exact prefixLift 4444569
  have htrace : WordTrace (prefixWord ++ tailWord_4444569) baseStart_4444569 baseEnd_4444569 := by
    simpa [prefixWord, tailWord_4444569, baseEnd_4444569] using wordTrace_append hprefix tailTrace_4444569
  have hstable : (prefixWord ++ tailWord_4444569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444569).length < 2 ^ (prefixWord ++ tailWord_4444569).sum := by decide
  have hdescent : baseEnd_4444569 < baseStart_4444569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444576 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 4, 4]
def baseStart_4444576 : Nat := 118140960795 + 4444576 * 2 ^ 59
def prefixEnd_4444576 : Nat := 4983230072969 + 3 ^ 40 * 4444576 * 2
def baseEnd_4444576 : Nat := 760734597812569269886591

theorem tailTrace_4444576 : CollatzResearch.WordTrace tailWord_4444576 prefixEnd_4444576 760734597812569269886591 := by
  unfold tailWord_4444576
  simp only [CollatzResearch.WordTrace]
  refine ⟨81053502173033849996504791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108071336230711799995339721 81053502173033849996504791)
  ·
    refine ⟨121580253259550774994757187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81053502173033849996504791 121580253259550774994757187)
    ·
      refine ⟨182370379889326162492135781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121580253259550774994757187 182370379889326162492135781)
      ·
        refine ⟨34194446229248655467275459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182370379889326162492135781 34194446229248655467275459)
        ·
          refine ⟨51291669343872983200913189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34194446229248655467275459 51291669343872983200913189)
          ·
            refine ⟨9617188001976184350171223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51291669343872983200913189 9617188001976184350171223)
            ·
              refine ⟨14425782002964276525256835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9617188001976184350171223 14425782002964276525256835)
              ·
                refine ⟨21638673004446414787885253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14425782002964276525256835 21638673004446414787885253)
                ·
                  refine ⟨4057251188333702772728485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21638673004446414787885253 4057251188333702772728485)
                  ·
                    refine ⟨760734597812569269886591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4057251188333702772728485 760734597812569269886591)
                    ·
                      rfl

theorem cell23_4444576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_4444576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444576 prefixEnd_4444576 := by exact prefixLift 4444576
  have htrace : WordTrace (prefixWord ++ tailWord_4444576) baseStart_4444576 baseEnd_4444576 := by
    simpa [prefixWord, tailWord_4444576, baseEnd_4444576] using wordTrace_append hprefix tailTrace_4444576
  have hstable : (prefixWord ++ tailWord_4444576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444576).length < 2 ^ (prefixWord ++ tailWord_4444576).sum := by decide
  have hdescent : baseEnd_4444576 < baseStart_4444576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444606 : List Nat := [4, 2, 1, 1, 1, 1, 6, 7]
def baseStart_4444606 : Nat := 118140960795 + 4444606 * 2 ^ 59
def prefixEnd_4444606 : Nat := 4983230072969 + 3 ^ 40 * 4444606 * 2
def baseEnd_4444606 : Nat := 84526636957679358973505

theorem tailTrace_4444606 : CollatzResearch.WordTrace tailWord_4444606 prefixEnd_4444606 84526636957679358973505 := by
  unfold tailWord_4444606
  simp only [CollatzResearch.WordTrace]
  refine ⟨20263512316994876889575209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108072065690639343411067781 20263512316994876889575209)
  ·
    refine ⟨15197634237746157667181407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20263512316994876889575209 15197634237746157667181407)
    ·
      refine ⟨22796451356619236500772111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15197634237746157667181407 22796451356619236500772111)
      ·
        refine ⟨34194677034928854751158167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22796451356619236500772111 34194677034928854751158167)
        ·
          refine ⟨51292015552393282126737251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34194677034928854751158167 51292015552393282126737251)
          ·
            refine ⟨76938023328589923190105877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51292015552393282126737251 76938023328589923190105877)
            ·
              refine ⟨3606469843527652649536213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76938023328589923190105877 3606469843527652649536213)
              ·
                refine ⟨84526636957679358973505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3606469843527652649536213 84526636957679358973505)
                ·
                  rfl

theorem cell23_4444606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_4444606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444606 prefixEnd_4444606 := by exact prefixLift 4444606
  have htrace : WordTrace (prefixWord ++ tailWord_4444606) baseStart_4444606 baseEnd_4444606 := by
    simpa [prefixWord, tailWord_4444606, baseEnd_4444606] using wordTrace_append hprefix tailTrace_4444606
  have hstable : (prefixWord ++ tailWord_4444606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444606).length < 2 ^ (prefixWord ++ tailWord_4444606).sum := by decide
  have hdescent : baseEnd_4444606 < baseStart_4444606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444633 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 3]
def baseStart_4444633 : Nat := 118140960795 + 4444633 * 2 ^ 59
def prefixEnd_4444633 : Nat := 4983230072969 + 3 ^ 40 * 4444633 * 2
def baseEnd_4444633 : Nat := 2282233061835014086647011

theorem tailTrace_4444633 : CollatzResearch.WordTrace tailWord_4444633 prefixEnd_4444633 2282233061835014086647011 := by
  unfold tailWord_4444633
  simp only [CollatzResearch.WordTrace]
  refine ⟨162109083306861198727834553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108072722204574132485223035 162109083306861198727834553)
  ·
    refine ⟨121581812480145899045875915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162109083306861198727834553 121581812480145899045875915)
    ·
      refine ⟨182372718720218848568813873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121581812480145899045875915 182372718720218848568813873)
      ·
        refine ⟨136779539040164136426610405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182372718720218848568813873 136779539040164136426610405)
        ·
          refine ⟨25646163570030775579989451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136779539040164136426610405 25646163570030775579989451)
          ·
            refine ⟨38469245355046163369984177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25646163570030775579989451 38469245355046163369984177)
            ·
              refine ⟨28851934016284622527488133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38469245355046163369984177 28851934016284622527488133)
              ·
                refine ⟨5409737628053366723904025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28851934016284622527488133 5409737628053366723904025)
                ·
                  refine ⟨4057303221040025042928019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5409737628053366723904025 4057303221040025042928019)
                  ·
                    refine ⟨6085954831560037564392029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4057303221040025042928019 6085954831560037564392029)
                    ·
                      refine ⟨2282233061835014086647011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085954831560037564392029 2282233061835014086647011)
                      ·
                        rfl

theorem cell23_4444633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_4444633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444633 prefixEnd_4444633 := by exact prefixLift 4444633
  have htrace : WordTrace (prefixWord ++ tailWord_4444633) baseStart_4444633 baseEnd_4444633 := by
    simpa [prefixWord, tailWord_4444633, baseEnd_4444633] using wordTrace_append hprefix tailTrace_4444633
  have hstable : (prefixWord ++ tailWord_4444633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444633).length < 2 ^ (prefixWord ++ tailWord_4444633).sum := by decide
  have hdescent : baseEnd_4444633 < baseStart_4444633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444650 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_4444650 : Nat := 118140960795 + 4444650 * 2 ^ 59
def prefixEnd_4444650 : Nat := 4983230072969 + 3 ^ 40 * 4444650 * 2
def baseEnd_4444650 : Nat := 2282241791006140520134433

theorem tailTrace_4444650 : CollatzResearch.WordTrace tailWord_4444650 prefixEnd_4444650 2282241791006140520134433 := by
  unfold tailWord_4444650
  simp only [CollatzResearch.WordTrace]
  refine ⟨40527425836949902657800851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108073135565199740420802269 40527425836949902657800851)
  ·
    refine ⟨60791138755424853986701277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40527425836949902657800851 60791138755424853986701277)
    ·
      refine ⟨22796677033284320245012979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60791138755424853986701277 22796677033284320245012979)
      ·
        refine ⟨34195015549926480367519469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22796677033284320245012979 34195015549926480367519469)
        ·
          refine ⟨12823130831222430137819801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34195015549926480367519469 12823130831222430137819801)
          ·
            refine ⟨9617348123416822603364851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12823130831222430137819801 9617348123416822603364851)
            ·
              refine ⟨14426022185125233905047277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9617348123416822603364851 14426022185125233905047277)
              ·
                refine ⟨5409758319421962714392729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14426022185125233905047277 5409758319421962714392729)
                ·
                  refine ⟨4057318739566472035794547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5409758319421962714392729 4057318739566472035794547)
                  ·
                    refine ⟨6085978109349708053691821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4057318739566472035794547 6085978109349708053691821)
                    ·
                      refine ⟨2282241791006140520134433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6085978109349708053691821 2282241791006140520134433)
                      ·
                        rfl

theorem cell23_4444650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_4444650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444650 prefixEnd_4444650 := by exact prefixLift 4444650
  have htrace : WordTrace (prefixWord ++ tailWord_4444650) baseStart_4444650 baseEnd_4444650 := by
    simpa [prefixWord, tailWord_4444650, baseEnd_4444650] using wordTrace_append hprefix tailTrace_4444650
  have hstable : (prefixWord ++ tailWord_4444650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444650).length < 2 ^ (prefixWord ++ tailWord_4444650).sum := by decide
  have hdescent : baseEnd_4444650 < baseStart_4444650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444659 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5]
def baseStart_4444659 : Nat := 118140960795 + 4444659 * 2 ^ 59
def prefixEnd_4444659 : Nat := 4983230072969 + 3 ^ 40 * 4444659 * 2
def baseEnd_4444659 : Nat := 2282246412332030984921891

theorem tailTrace_4444659 : CollatzResearch.WordTrace tailWord_4444659 prefixEnd_4444659 2282246412332030984921891 := by
  unfold tailWord_4444659
  simp only [CollatzResearch.WordTrace]
  refine ⟨162110031604767005168281031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108073354403178003445520687 162110031604767005168281031)
  ·
    refine ⟨243165047407150507752421547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162110031604767005168281031 243165047407150507752421547)
    ·
      refine ⟨364747571110725761628632321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243165047407150507752421547 364747571110725761628632321)
      ·
        refine ⟨273560678333044321221474241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364747571110725761628632321 273560678333044321221474241)
        ·
          refine ⟨205170508749783240916105681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273560678333044321221474241 205170508749783240916105681)
          ·
            refine ⟨153877881562337430687079261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205170508749783240916105681 153877881562337430687079261)
            ·
              refine ⟨57704205585876536507654723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153877881562337430687079261 57704205585876536507654723)
              ·
                refine ⟨86556308378814804761482085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57704205585876536507654723 86556308378814804761482085)
                ·
                  refine ⟨16229307821027775892777891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86556308378814804761482085 16229307821027775892777891)
                  ·
                    refine ⟨24343961731541663839166837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16229307821027775892777891 24343961731541663839166837)
                    ·
                      refine ⟨2282246412332030984921891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24343961731541663839166837 2282246412332030984921891)
                      ·
                        rfl

theorem cell23_4444659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_4444659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444659 prefixEnd_4444659 := by exact prefixLift 4444659
  have htrace : WordTrace (prefixWord ++ tailWord_4444659) baseStart_4444659 baseEnd_4444659 := by
    simpa [prefixWord, tailWord_4444659, baseEnd_4444659] using wordTrace_append hprefix tailTrace_4444659
  have hstable : (prefixWord ++ tailWord_4444659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444659).length < 2 ^ (prefixWord ++ tailWord_4444659).sum := by decide
  have hdescent : baseEnd_4444659 < baseStart_4444659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444673 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_4444673 : Nat := 118140960795 + 4444673 * 2 ^ 59
def prefixEnd_4444673 : Nat := 4983230072969 + 3 ^ 40 * 4444673 * 2
def baseEnd_4444673 : Nat := 2282253601061193930146827

theorem tailTrace_4444673 : CollatzResearch.WordTrace tailWord_4444673 prefixEnd_4444673 2282253601061193930146827 := by
  unfold tailWord_4444673
  simp only [CollatzResearch.WordTrace]
  refine ⟨162110542226716285559290673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108073694817810857039527115 162110542226716285559290673)
  ·
    refine ⟨121582906670037214169468005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162110542226716285559290673 121582906670037214169468005)
    ·
      refine ⟨22796795000631977656775251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121582906670037214169468005 22796795000631977656775251)
      ·
        refine ⟨34195192500947966485162877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22796795000631977656775251 34195192500947966485162877)
        ·
          refine ⟨12823197187855487431936079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34195192500947966485162877 12823197187855487431936079)
          ·
            refine ⟨19234795781783231147904119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12823197187855487431936079 19234795781783231147904119)
            ·
              refine ⟨28852193672674846721856179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19234795781783231147904119 28852193672674846721856179)
              ·
                refine ⟨43278290509012270082784269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28852193672674846721856179 43278290509012270082784269)
                ·
                  refine ⟨16229358940879601281044101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43278290509012270082784269 16229358940879601281044101)
                  ·
                    refine ⟨3043004801414925240195769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16229358940879601281044101 3043004801414925240195769)
                    ·
                      refine ⟨2282253601061193930146827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043004801414925240195769 2282253601061193930146827)
                      ·
                        rfl

theorem cell23_4444673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_4444673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444673 prefixEnd_4444673 := by exact prefixLift 4444673
  have htrace : WordTrace (prefixWord ++ tailWord_4444673) baseStart_4444673 baseEnd_4444673 := by
    simpa [prefixWord, tailWord_4444673, baseEnd_4444673] using wordTrace_append hprefix tailTrace_4444673
  have hstable : (prefixWord ++ tailWord_4444673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444673).length < 2 ^ (prefixWord ++ tailWord_4444673).sum := by decide
  have hdescent : baseEnd_4444673 < baseStart_4444673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444719 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_4444719 : Nat := 118140960795 + 4444719 * 2 ^ 59
def prefixEnd_4444719 : Nat := 4983230072969 + 3 ^ 40 * 4444719 * 2
def baseEnd_4444719 : Nat := 2282277221171300750171615

theorem tailTrace_4444719 : CollatzResearch.WordTrace tailWord_4444719 prefixEnd_4444719 2282277221171300750171615 := by
  unfold tailWord_4444719
  simp only [CollatzResearch.WordTrace]
  refine ⟨162112219984549635415465211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108074813323033090276976807 162112219984549635415465211)
  ·
    refine ⟨243168329976824453123197817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162112219984549635415465211 243168329976824453123197817)
    ·
      refine ⟨182376247482618339842398363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243168329976824453123197817 182376247482618339842398363)
      ·
        refine ⟨273564371223927509763597545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182376247482618339842398363 273564371223927509763597545)
        ·
          refine ⟨205173278417945632322698159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273564371223927509763597545 205173278417945632322698159)
          ·
            refine ⟨307759917626918448484047239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205173278417945632322698159 307759917626918448484047239)
            ·
              refine ⟨461639876440377672726070859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307759917626918448484047239 461639876440377672726070859)
              ·
                refine ⟨692459814660566509089106289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461639876440377672726070859 692459814660566509089106289)
                ·
                  refine ⟨519344860995424881816829717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 692459814660566509089106289 519344860995424881816829717)
                  ·
                    refine ⟨24344290359160541335163893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 519344860995424881816829717 24344290359160541335163893)
                    ·
                      refine ⟨2282277221171300750171615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24344290359160541335163893 2282277221171300750171615)
                      ·
                        rfl

theorem cell23_4444719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_4444719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444719 prefixEnd_4444719 := by exact prefixLift 4444719
  have htrace : WordTrace (prefixWord ++ tailWord_4444719) baseStart_4444719 baseEnd_4444719 := by
    simpa [prefixWord, tailWord_4444719, baseEnd_4444719] using wordTrace_append hprefix tailTrace_4444719
  have hstable : (prefixWord ++ tailWord_4444719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444719).length < 2 ^ (prefixWord ++ tailWord_4444719).sum := by decide
  have hdescent : baseEnd_4444719 < baseStart_4444719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444739 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 10]
def baseStart_4444739 : Nat := 118140960795 + 4444739 * 2 ^ 59
def prefixEnd_4444739 : Nat := 4983230072969 + 3 ^ 40 * 4444739 * 2
def baseEnd_4444739 : Nat := 760762496928130223973841

theorem tailTrace_4444739 : CollatzResearch.WordTrace tailWord_4444739 prefixEnd_4444739 760762496928130223973841 := by
  unfold tailWord_4444739
  simp only [CollatzResearch.WordTrace]
  refine ⟨162112949444477178831193271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108075299629651452554128847 162112949444477178831193271)
  ·
    refine ⟨243169424166715768246789907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162112949444477178831193271 243169424166715768246789907)
    ·
      refine ⟨364754136250073652370184861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243169424166715768246789907 364754136250073652370184861)
      ·
        refine ⟨136782801093777619638819323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 364754136250073652370184861 136782801093777619638819323)
        ·
          refine ⟨205174201640666429458228985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136782801093777619638819323 205174201640666429458228985)
          ·
            refine ⟨153880651230499822093671739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205174201640666429458228985 153880651230499822093671739)
            ·
              refine ⟨230820976845749733140507609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153880651230499822093671739 230820976845749733140507609)
              ·
                refine ⟨173115732634312299855380707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230820976845749733140507609 173115732634312299855380707)
                ·
                  refine ⟨259673598951468449783071061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173115732634312299855380707 259673598951468449783071061)
                  ·
                    refine ⟨760762496928130223973841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 259673598951468449783071061 760762496928130223973841)
                    ·
                      rfl

theorem cell23_4444739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_4444739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444739 prefixEnd_4444739 := by exact prefixLift 4444739
  have htrace : WordTrace (prefixWord ++ tailWord_4444739) baseStart_4444739 baseEnd_4444739 := by
    simpa [prefixWord, tailWord_4444739, baseEnd_4444739] using wordTrace_append hprefix tailTrace_4444739
  have hstable : (prefixWord ++ tailWord_4444739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444739).length < 2 ^ (prefixWord ++ tailWord_4444739).sum := by decide
  have hdescent : baseEnd_4444739 < baseStart_4444739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444807 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 1, 4]
def baseStart_4444807 : Nat := 118140960795 + 4444807 * 2 ^ 59
def prefixEnd_4444807 : Nat := 4983230072969 + 3 ^ 40 * 4444807 * 2
def baseEnd_4444807 : Nat := 760774135822965468623737

theorem tailTrace_4444807 : CollatzResearch.WordTrace tailWord_4444807 prefixEnd_4444807 760774135822965468623737 := by
  unfold tailWord_4444807
  simp only [CollatzResearch.WordTrace]
  refine ⟨162115429608230826444668675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108076953072153884296445783 162115429608230826444668675)
  ·
    refine ⟨243173144412346239667003013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162115429608230826444668675 243173144412346239667003013)
    ·
      refine ⟨45594964577314919937563065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243173144412346239667003013 45594964577314919937563065)
      ·
        refine ⟨34196223432986189953172299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45594964577314919937563065 34196223432986189953172299)
        ·
          refine ⟨51294335149479284929758449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34196223432986189953172299 51294335149479284929758449)
          ·
            refine ⟨38470751362109463697318837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51294335149479284929758449 38470751362109463697318837)
            ·
              refine ⟨3606632940197762221623641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38470751362109463697318837 3606632940197762221623641)
              ·
                refine ⟨2704974705148321666217731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3606632940197762221623641 2704974705148321666217731)
                ·
                  refine ⟨4057462057722482499326597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704974705148321666217731 4057462057722482499326597)
                  ·
                    refine ⟨760774135822965468623737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4057462057722482499326597 760774135822965468623737)
                    ·
                      rfl

theorem cell23_4444807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_4444807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444807 prefixEnd_4444807 := by exact prefixLift 4444807
  have htrace : WordTrace (prefixWord ++ tailWord_4444807) baseStart_4444807 baseEnd_4444807 := by
    simpa [prefixWord, tailWord_4444807, baseEnd_4444807] using wordTrace_append hprefix tailTrace_4444807
  have hstable : (prefixWord ++ tailWord_4444807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444807).length < 2 ^ (prefixWord ++ tailWord_4444807).sum := by decide
  have hdescent : baseEnd_4444807 < baseStart_4444807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444820 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 6]
def baseStart_4444820 : Nat := 118140960795 + 4444820 * 2 ^ 59
def prefixEnd_4444820 : Nat := 4983230072969 + 3 ^ 40 * 4444820 * 2
def baseEnd_4444820 : Nat := 253592120301933872778739

theorem tailTrace_4444820 : CollatzResearch.WordTrace tailWord_4444820 prefixEnd_4444820 253592120301933872778739 := by
  unfold tailWord_4444820
  simp only [CollatzResearch.WordTrace]
  refine ⟨81057951878591864832445957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108077269171455819776594609 81057951878591864832445957)
  ·
    refine ⟨15198365977235974656083617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81057951878591864832445957 15198365977235974656083617)
    ·
      refine ⟨11398774482926980992062713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15198365977235974656083617 11398774482926980992062713)
      ·
        refine ⟨8549080862195235744047035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11398774482926980992062713 8549080862195235744047035)
        ·
          refine ⟨12823621293292853616070553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8549080862195235744047035 12823621293292853616070553)
          ·
            refine ⟨9617715969969640212052915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12823621293292853616070553 9617715969969640212052915)
            ·
              refine ⟨14426573954954460318079373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9617715969969640212052915 14426573954954460318079373)
              ·
                refine ⟨5409965233107922619279765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14426573954954460318079373 5409965233107922619279765)
                ·
                  refine ⟨253592120301933872778739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5409965233107922619279765 253592120301933872778739)
                  ·
                    rfl

theorem cell23_4444820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_4444820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444820 prefixEnd_4444820 := by exact prefixLift 4444820
  have htrace : WordTrace (prefixWord ++ tailWord_4444820) baseStart_4444820 baseEnd_4444820 := by
    simpa [prefixWord, tailWord_4444820, baseEnd_4444820] using wordTrace_append hprefix tailTrace_4444820
  have hstable : (prefixWord ++ tailWord_4444820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444820).length < 2 ^ (prefixWord ++ tailWord_4444820).sum := by decide
  have hdescent : baseEnd_4444820 < baseStart_4444820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444864 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 1, 1, 3]
def baseStart_4444864 : Nat := 118140960795 + 4444864 * 2 ^ 59
def prefixEnd_4444864 : Nat := 4983230072969 + 3 ^ 40 * 4444864 * 2
def baseEnd_4444864 : Nat := 2282351675866202682858449

theorem tailTrace_4444864 : CollatzResearch.WordTrace tailWord_4444864 prefixEnd_4444864 2282351675866202682858449 := by
  unfold tailWord_4444864
  simp only [CollatzResearch.WordTrace]
  refine ⟨81058754284512162589746823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108078339046016216786329097 81058754284512162589746823)
  ·
    refine ⟨121588131426768243884620235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81058754284512162589746823 121588131426768243884620235)
    ·
      refine ⟨182382197140152365826930353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121588131426768243884620235 182382197140152365826930353)
      ·
        refine ⟨136786647855114274370197765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182382197140152365826930353 136786647855114274370197765)
        ·
          refine ⟨25647496472833926444412081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136786647855114274370197765 25647496472833926444412081)
          ·
            refine ⟨19235622354625444833309061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25647496472833926444412081 19235622354625444833309061)
            ·
              refine ⟨3606679191492270906245449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19235622354625444833309061 3606679191492270906245449)
              ·
                refine ⟨2705009393619203179684087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3606679191492270906245449 2705009393619203179684087)
                ·
                  refine ⟨4057514090428804769526131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705009393619203179684087 4057514090428804769526131)
                  ·
                    refine ⟨6086271135643207154289197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4057514090428804769526131 6086271135643207154289197)
                    ·
                      refine ⟨2282351675866202682858449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086271135643207154289197 2282351675866202682858449)
                      ·
                        rfl

theorem cell23_4444864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_4444864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444864 prefixEnd_4444864 := by exact prefixLift 4444864
  have htrace : WordTrace (prefixWord ++ tailWord_4444864) baseStart_4444864 baseEnd_4444864 := by
    simpa [prefixWord, tailWord_4444864, baseEnd_4444864] using wordTrace_append hprefix tailTrace_4444864
  have hstable : (prefixWord ++ tailWord_4444864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444864).length < 2 ^ (prefixWord ++ tailWord_4444864).sum := by decide
  have hdescent : baseEnd_4444864 < baseStart_4444864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444887 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 3, 2, 2]
def baseStart_4444887 : Nat := 118140960795 + 4444887 * 2 ^ 59
def prefixEnd_4444887 : Nat := 4983230072969 + 3 ^ 40 * 4444887 * 2
def baseEnd_4444887 : Nat := 2282363485921256092870843

theorem tailTrace_4444887 : CollatzResearch.WordTrace tailWord_4444887 prefixEnd_4444887 2282363485921256092870843 := by
  unfold tailWord_4444887
  simp only [CollatzResearch.WordTrace]
  refine ⟨162118347447941000107580915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108078898298627333405053943 162118347447941000107580915)
  ·
    refine ⟨243177521171911500161371373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162118347447941000107580915 243177521171911500161371373)
    ·
      refine ⟨91191570439466812560514265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243177521171911500161371373 91191570439466812560514265)
      ·
        refine ⟨68393677829600109420385699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91191570439466812560514265 68393677829600109420385699)
        ·
          refine ⟨102590516744400164130578549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68393677829600109420385699 102590516744400164130578549)
          ·
            refine ⟨9617860944787515387241739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102590516744400164130578549 9617860944787515387241739)
            ·
              refine ⟨14426791417181273080862609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9617860944787515387241739 14426791417181273080862609)
              ·
                refine ⟨10820093562885954810646957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14426791417181273080862609 10820093562885954810646957)
                ·
                  refine ⟨4057535086082233053992609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10820093562885954810646957 4057535086082233053992609)
                  ·
                    refine ⟨3043151314561674790494457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4057535086082233053992609 3043151314561674790494457)
                    ·
                      refine ⟨2282363485921256092870843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043151314561674790494457 2282363485921256092870843)
                      ·
                        rfl

theorem cell23_4444887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_4444887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444887 prefixEnd_4444887 := by exact prefixLift 4444887
  have htrace : WordTrace (prefixWord ++ tailWord_4444887) baseStart_4444887 baseEnd_4444887 := by
    simpa [prefixWord, tailWord_4444887, baseEnd_4444887] using wordTrace_append hprefix tailTrace_4444887
  have hstable : (prefixWord ++ tailWord_4444887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444887).length < 2 ^ (prefixWord ++ tailWord_4444887).sum := by decide
  have hdescent : baseEnd_4444887 < baseStart_4444887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444890 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_4444890 : Nat := 118140960795 + 4444890 * 2 ^ 59
def prefixEnd_4444890 : Nat := 4983230072969 + 3 ^ 40 * 4444890 * 2
def baseEnd_4444890 : Nat := 2282365026363219581133329

theorem tailTrace_4444890 : CollatzResearch.WordTrace tailWord_4444890 prefixEnd_4444890 2282365026363219581133329 := by
  unfold tailWord_4444890
  simp only [CollatzResearch.WordTrace]
  refine ⟨40529614216732532904985031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108078971244620087746626749 40529614216732532904985031)
  ·
    refine ⟨60794421325098799357477547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40529614216732532904985031 60794421325098799357477547)
    ·
      refine ⟨91191631987648199036216321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60794421325098799357477547 91191631987648199036216321)
      ·
        refine ⟨68393723990736149277162241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91191631987648199036216321 68393723990736149277162241)
        ·
          refine ⟨51295292993052111957871681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68393723990736149277162241 51295292993052111957871681)
          ·
            refine ⟨38471469744789083968403761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51295292993052111957871681 38471469744789083968403761)
            ·
              refine ⟨28853602308591812976302821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38471469744789083968403761 28853602308591812976302821)
              ·
                refine ⟨5410050432860964933056779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28853602308591812976302821 5410050432860964933056779)
                ·
                  refine ⟨8115075649291447399585169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5410050432860964933056779 8115075649291447399585169)
                  ·
                    refine ⟨6086306736968585549688877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8115075649291447399585169 6086306736968585549688877)
                    ·
                      refine ⟨2282365026363219581133329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086306736968585549688877 2282365026363219581133329)
                      ·
                        rfl

theorem cell23_4444890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_4444890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444890 prefixEnd_4444890 := by exact prefixLift 4444890
  have htrace : WordTrace (prefixWord ++ tailWord_4444890) baseStart_4444890 baseEnd_4444890 := by
    simpa [prefixWord, tailWord_4444890, baseEnd_4444890] using wordTrace_append hprefix tailTrace_4444890
  have hstable : (prefixWord ++ tailWord_4444890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444890).length < 2 ^ (prefixWord ++ tailWord_4444890).sum := by decide
  have hdescent : baseEnd_4444890 < baseStart_4444890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444904 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_4444904 : Nat := 118140960795 + 4444904 * 2 ^ 59
def prefixEnd_4444904 : Nat := 4983230072969 + 3 ^ 40 * 4444904 * 2
def baseEnd_4444904 : Nat := 2282372215092382526358265

theorem tailTrace_4444904 : CollatzResearch.WordTrace tailWord_4444904 prefixEnd_4444904 2282372215092382526358265 := by
  unfold tailWord_4444904
  simp only [CollatzResearch.WordTrace]
  refine ⟨81059483744439706005474883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108079311659252941340633177 81059483744439706005474883)
  ·
    refine ⟨121589225616659559008212325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81059483744439706005474883 121589225616659559008212325)
    ·
      refine ⟨22797979803123667314039811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121589225616659559008212325 22797979803123667314039811)
      ·
        refine ⟨34196969704685500971059717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22797979803123667314039811 34196969704685500971059717)
        ·
          refine ⟨6411931819628531432073697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34196969704685500971059717 6411931819628531432073697)
          ·
            refine ⟨4808948864721398574055273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6411931819628531432073697 4808948864721398574055273)
            ·
              refine ⟨3606711648541048930541455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808948864721398574055273 3606711648541048930541455)
              ·
                refine ⟨5410067472811573395812183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606711648541048930541455 5410067472811573395812183)
                ·
                  refine ⟨8115101209217360093718275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5410067472811573395812183 8115101209217360093718275)
                  ·
                    refine ⟨12172651813826040140577413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8115101209217360093718275 12172651813826040140577413)
                    ·
                      refine ⟨2282372215092382526358265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12172651813826040140577413 2282372215092382526358265)
                      ·
                        rfl

theorem cell23_4444904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_4444904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444904 prefixEnd_4444904 := by exact prefixLift 4444904
  have htrace : WordTrace (prefixWord ++ tailWord_4444904) baseStart_4444904 baseEnd_4444904 := by
    simpa [prefixWord, tailWord_4444904, baseEnd_4444904] using wordTrace_append hprefix tailTrace_4444904
  have hstable : (prefixWord ++ tailWord_4444904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444904).length < 2 ^ (prefixWord ++ tailWord_4444904).sum := by decide
  have hdescent : baseEnd_4444904 < baseStart_4444904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444920 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_4444920 : Nat := 118140960795 + 4444920 * 2 ^ 59
def prefixEnd_4444920 : Nat := 4983230072969 + 3 ^ 40 * 4444920 * 2
def baseEnd_4444920 : Nat := 2282380430782854463758191

theorem tailTrace_4444920 : CollatzResearch.WordTrace tailWord_4444920 prefixEnd_4444920 2282380430782854463758191 := by
  unfold tailWord_4444920
  simp only [CollatzResearch.WordTrace]
  refine ⟨81059775528410723371766107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108079700704547631162354809 81059775528410723371766107)
  ·
    refine ⟨121589663292616085057649161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81059775528410723371766107 121589663292616085057649161)
    ·
      refine ⟨91192247469462063793236871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121589663292616085057649161 91192247469462063793236871)
      ·
        refine ⟨136788371204193095689855307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91192247469462063793236871 136788371204193095689855307)
        ·
          refine ⟨205182556806289643534782961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136788371204193095689855307 205182556806289643534782961)
          ·
            refine ⟨153886917604717232651087221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205182556806289643534782961 153886917604717232651087221)
            ·
              refine ⟨14426898525442240561039427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153886917604717232651087221 14426898525442240561039427)
              ·
                refine ⟨21640347788163360841559141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14426898525442240561039427 21640347788163360841559141)
                ·
                  refine ⟨4057565210280630157792339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21640347788163360841559141 4057565210280630157792339)
                  ·
                    refine ⟨6086347815420945236688509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4057565210280630157792339 6086347815420945236688509)
                    ·
                      refine ⟨2282380430782854463758191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086347815420945236688509 2282380430782854463758191)
                      ·
                        rfl

theorem cell23_4444920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_4444920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444920 prefixEnd_4444920 := by exact prefixLift 4444920
  have htrace : WordTrace (prefixWord ++ tailWord_4444920) baseStart_4444920 baseEnd_4444920 := by
    simpa [prefixWord, tailWord_4444920, baseEnd_4444920] using wordTrace_append hprefix tailTrace_4444920
  have hstable : (prefixWord ++ tailWord_4444920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444920).length < 2 ^ (prefixWord ++ tailWord_4444920).sum := by decide
  have hdescent : baseEnd_4444920 < baseStart_4444920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444947 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 1, 3, 2]
def baseStart_4444947 : Nat := 118140960795 + 4444947 * 2 ^ 59
def prefixEnd_4444947 : Nat := 4983230072969 + 3 ^ 40 * 4444947 * 2
def baseEnd_4444947 : Nat := 2282394294760525858120567

theorem tailTrace_4444947 : CollatzResearch.WordTrace tailWord_4444947 prefixEnd_4444947 2282394294760525858120567 := by
  unfold tailWord_4444947
  simp only [CollatzResearch.WordTrace]
  refine ⟨162120535827723630354765095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108080357218482420236510063 162120535827723630354765095)
  ·
    refine ⟨243180803741585445532147643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162120535827723630354765095 243180803741585445532147643)
    ·
      refine ⟨364771205612378168298221465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243180803741585445532147643 364771205612378168298221465)
      ·
        refine ⟨273578404209283626223666099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364771205612378168298221465 273578404209283626223666099)
        ·
          refine ⟨410367606313925439335499149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273578404209283626223666099 410367606313925439335499149)
          ·
            refine ⟨153887852367722039750812181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410367606313925439335499149 153887852367722039750812181)
            ·
              refine ⟨7213493079736970613319321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153887852367722039750812181 7213493079736970613319321)
              ·
                refine ⟨5410119809802727959989491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7213493079736970613319321 5410119809802727959989491)
                ·
                  refine ⟨8115179714704091939984237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5410119809802727959989491 8115179714704091939984237)
                  ·
                    refine ⟨3043192393014034477494089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8115179714704091939984237 3043192393014034477494089)
                    ·
                      refine ⟨2282394294760525858120567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043192393014034477494089 2282394294760525858120567)
                      ·
                        rfl

theorem cell23_4444947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 3, 2].length) (baseStart_4444947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444947 prefixEnd_4444947 := by exact prefixLift 4444947
  have htrace : WordTrace (prefixWord ++ tailWord_4444947) baseStart_4444947 baseEnd_4444947 := by
    simpa [prefixWord, tailWord_4444947, baseEnd_4444947] using wordTrace_append hprefix tailTrace_4444947
  have hstable : (prefixWord ++ tailWord_4444947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444947).length < 2 ^ (prefixWord ++ tailWord_4444947).sum := by decide
  have hdescent : baseEnd_4444947 < baseStart_4444947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444963 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 3]
def baseStart_4444963 : Nat := 118140960795 + 4444963 * 2 ^ 59
def prefixEnd_4444963 : Nat := 4983230072969 + 3 ^ 40 * 4444963 * 2
def baseEnd_4444963 : Nat := 2282402510450997795520493

theorem tailTrace_4444963 : CollatzResearch.WordTrace tailWord_4444963 prefixEnd_4444963 2282402510450997795520493 := by
  unfold tailWord_4444963
  simp only [CollatzResearch.WordTrace]
  refine ⟨162121119395665665087347543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108080746263777110058231695 162121119395665665087347543)
  ·
    refine ⟨243181679093498497631021315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162121119395665665087347543 243181679093498497631021315)
    ·
      refine ⟨364772518640247746446531973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243181679093498497631021315 364772518640247746446531973)
      ·
        refine ⟨68394847245046452458724745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 364772518640247746446531973 68394847245046452458724745)
        ·
          refine ⟨51296135433784839344043559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68394847245046452458724745 51296135433784839344043559)
          ·
            refine ⟨76944203150677259016065339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51296135433784839344043559 76944203150677259016065339)
            ·
              refine ⟨115416304726015888524098009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76944203150677259016065339 115416304726015888524098009)
              ·
                refine ⟨86562228544511916393073507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115416304726015888524098009 86562228544511916393073507)
                ·
                  refine ⟨129843342816767874589610261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86562228544511916393073507 129843342816767874589610261)
                  ·
                    refine ⟨6086406694535994121387981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 129843342816767874589610261 6086406694535994121387981)
                    ·
                      refine ⟨2282402510450997795520493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086406694535994121387981 2282402510450997795520493)
                      ·
                        rfl

theorem cell23_4444963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_4444963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444963 prefixEnd_4444963 := by exact prefixLift 4444963
  have htrace : WordTrace (prefixWord ++ tailWord_4444963) baseStart_4444963 baseEnd_4444963 := by
    simpa [prefixWord, tailWord_4444963, baseEnd_4444963] using wordTrace_append hprefix tailTrace_4444963
  have hstable : (prefixWord ++ tailWord_4444963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444963).length < 2 ^ (prefixWord ++ tailWord_4444963).sum := by decide
  have hdescent : baseEnd_4444963 < baseStart_4444963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444977 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 4, 2, 2]
def baseStart_4444977 : Nat := 118140960795 + 4444977 * 2 ^ 59
def prefixEnd_4444977 : Nat := 4983230072969 + 3 ^ 40 * 4444977 * 2
def baseEnd_4444977 : Nat := 2282409699180160740745429

theorem tailTrace_4444977 : CollatzResearch.WordTrace tailWord_4444977 prefixEnd_4444977 2282409699180160740745429 := by
  unfold tailWord_4444977
  simp only [CollatzResearch.WordTrace]
  refine ⟨162121630017614945478357185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108081086678409963652238123 162121630017614945478357185)
  ·
    refine ⟨121591222513211209108767889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162121630017614945478357185 121591222513211209108767889)
    ·
      refine ⟨91193416884908406831575917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121591222513211209108767889 91193416884908406831575917)
      ·
        refine ⟨34197531331840652561840969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91193416884908406831575917 34197531331840652561840969)
        ·
          refine ⟨25648148498880489421380727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34197531331840652561840969 25648148498880489421380727)
          ·
            refine ⟨38472222748320734132071091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25648148498880489421380727 38472222748320734132071091)
            ·
              refine ⟨57708334122481101198106637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38472222748320734132071091 57708334122481101198106637)
              ·
                refine ⟨21640625295930412949289989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57708334122481101198106637 21640625295930412949289989)
                ·
                  refine ⟨4057617242986952427991873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21640625295930412949289989 4057617242986952427991873)
                  ·
                    refine ⟨3043212932240214320993905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4057617242986952427991873 3043212932240214320993905)
                    ·
                      refine ⟨2282409699180160740745429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043212932240214320993905 2282409699180160740745429)
                      ·
                        rfl

theorem cell23_4444977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_4444977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4444977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4444977 prefixEnd_4444977 := by exact prefixLift 4444977
  have htrace : WordTrace (prefixWord ++ tailWord_4444977) baseStart_4444977 baseEnd_4444977 := by
    simpa [prefixWord, tailWord_4444977, baseEnd_4444977] using wordTrace_append hprefix tailTrace_4444977
  have hstable : (prefixWord ++ tailWord_4444977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444977).length < 2 ^ (prefixWord ++ tailWord_4444977).sum := by decide
  have hdescent : baseEnd_4444977 < baseStart_4444977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445023 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_4445023 : Nat := 118140960795 + 4445023 * 2 ^ 59
def prefixEnd_4445023 : Nat := 4983230072969 + 3 ^ 40 * 4445023 * 2
def baseEnd_4445023 : Nat := 2282433319290267560770217

theorem tailTrace_4445023 : CollatzResearch.WordTrace tailWord_4445023 prefixEnd_4445023 2282433319290267560770217 := by
  unfold tailWord_4445023
  simp only [CollatzResearch.WordTrace]
  refine ⟨162123307775448295334531723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108082205183632196889687815 162123307775448295334531723)
  ·
    refine ⟨243184961663172443001797585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162123307775448295334531723 243184961663172443001797585)
    ·
      refine ⟨182388721247379332251348189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243184961663172443001797585 182388721247379332251348189)
      ·
        refine ⟨68395770467767249594255571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182388721247379332251348189 68395770467767249594255571)
        ·
          refine ⟨102593655701650874391383357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68395770467767249594255571 102593655701650874391383357)
          ·
            refine ⟨38472620888119077896768759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102593655701650874391383357 38472620888119077896768759)
            ·
              refine ⟨57708931332178616845153139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38472620888119077896768759 57708931332178616845153139)
              ·
                refine ⟨86563396998267925267729709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57708931332178616845153139 86563396998267925267729709)
                ·
                  refine ⟨32461273874350471975398641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86563396998267925267729709 32461273874350471975398641)
                  ·
                    refine ⟨24345955405762853981548981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32461273874350471975398641 24345955405762853981548981)
                    ·
                      refine ⟨2282433319290267560770217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24345955405762853981548981 2282433319290267560770217)
                      ·
                        rfl

theorem cell23_4445023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_4445023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445023 prefixEnd_4445023 := by exact prefixLift 4445023
  have htrace : WordTrace (prefixWord ++ tailWord_4445023) baseStart_4445023 baseEnd_4445023 := by
    simpa [prefixWord, tailWord_4445023, baseEnd_4445023] using wordTrace_append hprefix tailTrace_4445023
  have hstable : (prefixWord ++ tailWord_4445023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445023).length < 2 ^ (prefixWord ++ tailWord_4445023).sum := by decide
  have hdescent : baseEnd_4445023 < baseStart_4445023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445033 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_4445033 : Nat := 118140960795 + 4445033 * 2 ^ 59
def prefixEnd_4445033 : Nat := 4983230072969 + 3 ^ 40 * 4445033 * 2
def baseEnd_4445033 : Nat := 2282438454096812521645171

theorem tailTrace_4445033 : CollatzResearch.WordTrace tailWord_4445033 prefixEnd_4445033 2282438454096812521645171 := by
  unfold tailWord_4445033
  simp only [CollatzResearch.WordTrace]
  refine ⟨162123672505412067042395753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108082448336941378028263835 162123672505412067042395753)
  ·
    refine ⟨121592754379059050281796815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162123672505412067042395753 121592754379059050281796815)
    ·
      refine ⟨182389131568588575422695223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121592754379059050281796815 182389131568588575422695223)
      ·
        refine ⟨273583697352882863134042835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182389131568588575422695223 273583697352882863134042835)
        ·
          refine ⟨410375546029324294701064253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273583697352882863134042835 410375546029324294701064253)
          ·
            refine ⟨153890829760996610512899095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410375546029324294701064253 153890829760996610512899095)
            ·
              refine ⟨230836244641494915769348643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153890829760996610512899095 230836244641494915769348643)
              ·
                refine ⟨346254366962242373654022965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230836244641494915769348643 346254366962242373654022965)
                ·
                  refine ⟨32461346902710222530064653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 346254366962242373654022965 32461346902710222530064653)
                  ·
                    refine ⟨12173005088516333448774245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32461346902710222530064653 12173005088516333448774245)
                    ·
                      refine ⟨2282438454096812521645171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12173005088516333448774245 2282438454096812521645171)
                      ·
                        rfl

theorem cell23_4445033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_4445033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445033 prefixEnd_4445033 := by exact prefixLift 4445033
  have htrace : WordTrace (prefixWord ++ tailWord_4445033) baseStart_4445033 baseEnd_4445033 := by
    simpa [prefixWord, tailWord_4445033, baseEnd_4445033] using wordTrace_append hprefix tailTrace_4445033
  have hstable : (prefixWord ++ tailWord_4445033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445033).length < 2 ^ (prefixWord ++ tailWord_4445033).sum := by decide
  have hdescent : baseEnd_4445033 < baseStart_4445033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445073 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 8]
def baseStart_4445073 : Nat := 118140960795 + 4445073 * 2 ^ 59
def prefixEnd_4445073 : Nat := 4983230072969 + 3 ^ 40 * 4445073 * 2
def baseEnd_4445073 : Nat := 253606554813665818349443

theorem tailTrace_4445073 : CollatzResearch.WordTrace tailWord_4445073 prefixEnd_4445073 253606554813665818349443 := by
  unfold tailWord_4445073
  simp only [CollatzResearch.WordTrace]
  refine ⟨162125131425267153873851873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108083420950178102582567915 162125131425267153873851873)
  ·
    refine ⟨121593848568950365405388905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162125131425267153873851873 121593848568950365405388905)
    ·
      refine ⟨91195386426712774054041679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121593848568950365405388905 91195386426712774054041679)
      ·
        refine ⟨136793079640069161081062519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91195386426712774054041679 136793079640069161081062519)
        ·
          refine ⟨205189619460103741621593779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136793079640069161081062519 205189619460103741621593779)
          ·
            refine ⟨307784429190155612432390669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205189619460103741621593779 307784429190155612432390669)
            ·
              refine ⟨115419160946308354662146501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307784429190155612432390669 115419160946308354662146501)
              ·
                refine ⟨21641092677432816499152469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115419160946308354662146501 21641092677432816499152469)
                ·
                  refine ⟨253606554813665818349443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21641092677432816499152469 253606554813665818349443)
                  ·
                    rfl

theorem cell23_4445073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_4445073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445073 prefixEnd_4445073 := by exact prefixLift 4445073
  have htrace : WordTrace (prefixWord ++ tailWord_4445073) baseStart_4445073 baseEnd_4445073 := by
    simpa [prefixWord, tailWord_4445073, baseEnd_4445073] using wordTrace_append hprefix tailTrace_4445073
  have hstable : (prefixWord ++ tailWord_4445073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445073).length < 2 ^ (prefixWord ++ tailWord_4445073).sum := by decide
  have hdescent : baseEnd_4445073 < baseStart_4445073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445103 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 9]
def baseStart_4445103 : Nat := 118140960795 + 4445103 * 2 ^ 59
def prefixEnd_4445103 : Nat := 4983230072969 + 3 ^ 40 * 4445103 * 2
def baseEnd_4445103 : Nat := 760824799247542415923283

theorem tailTrace_4445103 : CollatzResearch.WordTrace tailWord_4445103 prefixEnd_4445103 760824799247542415923283 := by
  unfold tailWord_4445103
  simp only [CollatzResearch.WordTrace]
  refine ⟨162126225615158468997443963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108084150410105645998295975 162126225615158468997443963)
  ·
    refine ⟨243189338422737703496165945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162126225615158468997443963 243189338422737703496165945)
    ·
      refine ⟨182392003817053277622124459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243189338422737703496165945 182392003817053277622124459)
      ·
        refine ⟨273588005725579916433186689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182392003817053277622124459 273588005725579916433186689)
        ·
          refine ⟨205191004294184937324890017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273588005725579916433186689 205191004294184937324890017)
          ·
            refine ⟨153893253220638702993667513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205191004294184937324890017 153893253220638702993667513)
            ·
              refine ⟨115419939915479027245250635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153893253220638702993667513 115419939915479027245250635)
              ·
                refine ⟨173129909873218540867875953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115419939915479027245250635 173129909873218540867875953)
                ·
                  refine ⟨129847432404913905650906965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173129909873218540867875953 129847432404913905650906965)
                  ·
                    refine ⟨760824799247542415923283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 129847432404913905650906965 760824799247542415923283)
                    ·
                      rfl

theorem cell23_4445103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_4445103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445103 prefixEnd_4445103 := by exact prefixLift 4445103
  have htrace : WordTrace (prefixWord ++ tailWord_4445103) baseStart_4445103 baseEnd_4445103 := by
    simpa [prefixWord, tailWord_4445103, baseEnd_4445103] using wordTrace_append hprefix tailTrace_4445103
  have hstable : (prefixWord ++ tailWord_4445103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445103).length < 2 ^ (prefixWord ++ tailWord_4445103).sum := by decide
  have hdescent : baseEnd_4445103 < baseStart_4445103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445127 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_4445127 : Nat := 118140960795 + 4445127 * 2 ^ 59
def prefixEnd_4445127 : Nat := 4983230072969 + 3 ^ 40 * 4445127 * 2
def baseEnd_4445127 : Nat := 2282486721278335153869739

theorem tailTrace_4445127 : CollatzResearch.WordTrace tailWord_4445127 prefixEnd_4445127 2282486721278335153869739 := by
  unfold tailWord_4445127
  simp only [CollatzResearch.WordTrace]
  refine ⟨162127100967071521096317635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108084733978047680730878423 162127100967071521096317635)
  ·
    refine ⟨243190651450607281644476453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162127100967071521096317635 243190651450607281644476453)
    ·
      refine ⟨45598247146988865308339335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243190651450607281644476453 45598247146988865308339335)
      ·
        refine ⟨68397370720483297962509003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45598247146988865308339335 68397370720483297962509003)
        ·
          refine ⟨102596056080724946943763505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68397370720483297962509003 102596056080724946943763505)
          ·
            refine ⟨76947042060543710207822629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102596056080724946943763505 76947042060543710207822629)
            ·
              refine ⟨14427570386351945663966743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76947042060543710207822629 14427570386351945663966743)
              ·
                refine ⟨21641355579527918495950115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14427570386351945663966743 21641355579527918495950115)
                ·
                  refine ⟨32462033369291877743925173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21641355579527918495950115 32462033369291877743925173)
                  ·
                    refine ⟨3043315628371113538492985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32462033369291877743925173 3043315628371113538492985)
                    ·
                      refine ⟨2282486721278335153869739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043315628371113538492985 2282486721278335153869739)
                      ·
                        rfl

theorem cell23_4445127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_4445127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445127 prefixEnd_4445127 := by exact prefixLift 4445127
  have htrace : WordTrace (prefixWord ++ tailWord_4445127) baseStart_4445127 baseEnd_4445127 := by
    simpa [prefixWord, tailWord_4445127, baseEnd_4445127] using wordTrace_append hprefix tailTrace_4445127
  have hstable : (prefixWord ++ tailWord_4445127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445127).length < 2 ^ (prefixWord ++ tailWord_4445127).sum := by decide
  have hdescent : baseEnd_4445127 < baseStart_4445127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445128 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 1, 4]
def baseStart_4445128 : Nat := 118140960795 + 4445128 * 2 ^ 59
def prefixEnd_4445128 : Nat := 4983230072969 + 3 ^ 40 * 4445128 * 2
def baseEnd_4445128 : Nat := 760829078252996549985745

theorem tailTrace_4445128 : CollatzResearch.WordTrace tailWord_4445128 prefixEnd_4445128 760829078252996549985745 := by
  unfold tailWord_4445128
  simp only [CollatzResearch.WordTrace]
  refine ⟨81063568720033949133552019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108084758293378598844736025 81063568720033949133552019)
  ·
    refine ⟨121595353080050923700328029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81063568720033949133552019 121595353080050923700328029)
    ·
      refine ⟨45598257405019096387623011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121595353080050923700328029 45598257405019096387623011)
      ·
        refine ⟨68397386107528644581434517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45598257405019096387623011 68397386107528644581434517)
        ·
          refine ⟨3206127473790405214754743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68397386107528644581434517 3206127473790405214754743)
          ·
            refine ⟨4809191210685607822132115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206127473790405214754743 4809191210685607822132115)
            ·
              refine ⟨7213786816028411733198173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809191210685607822132115 7213786816028411733198173)
              ·
                refine ⟨2705170056010654399949315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7213786816028411733198173 2705170056010654399949315)
                ·
                  refine ⟨4057755084015981599923973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705170056010654399949315 4057755084015981599923973)
                  ·
                    refine ⟨760829078252996549985745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4057755084015981599923973 760829078252996549985745)
                    ·
                      rfl

theorem cell23_4445128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_4445128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445128 prefixEnd_4445128 := by exact prefixLift 4445128
  have htrace : WordTrace (prefixWord ++ tailWord_4445128) baseStart_4445128 baseEnd_4445128 := by
    simpa [prefixWord, tailWord_4445128, baseEnd_4445128] using wordTrace_append hprefix tailTrace_4445128
  have hstable : (prefixWord ++ tailWord_4445128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445128).length < 2 ^ (prefixWord ++ tailWord_4445128).sum := by decide
  have hdescent : baseEnd_4445128 < baseStart_4445128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445144 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 2, 3, 2]
def baseStart_4445144 : Nat := 118140960795 + 4445144 * 2 ^ 59
def prefixEnd_4445144 : Nat := 4983230072969 + 3 ^ 40 * 4445144 * 2
def baseEnd_4445144 : Nat := 2282495450449461587357161

theorem tailTrace_4445144 : CollatzResearch.WordTrace tailWord_4445144 prefixEnd_4445144 2282495450449461587357161 := by
  unfold tailWord_4445144
  simp only [CollatzResearch.WordTrace]
  refine ⟨81063860504004966499843243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108085147338673288666457657 81063860504004966499843243)
  ·
    refine ⟨121595790756007449749764865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81063860504004966499843243 121595790756007449749764865)
    ·
      refine ⟨91196843067005587312323649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121595790756007449749764865 91196843067005587312323649)
      ·
        refine ⟨68397632300254190484242737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91196843067005587312323649 68397632300254190484242737)
        ·
          refine ⟨51298224225190642863182053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68397632300254190484242737 51298224225190642863182053)
          ·
            refine ⟨9618417042223245536846635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51298224225190642863182053 9618417042223245536846635)
            ·
              refine ⟨14427625563334868305269953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618417042223245536846635 14427625563334868305269953)
              ·
                refine ⟨10820719172501151228952465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14427625563334868305269953 10820719172501151228952465)
                ·
                  refine ⟨8115539379375863421714349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10820719172501151228952465 8115539379375863421714349)
                  ·
                    refine ⟨3043327267265948783142881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8115539379375863421714349 3043327267265948783142881)
                    ·
                      refine ⟨2282495450449461587357161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043327267265948783142881 2282495450449461587357161)
                      ·
                        rfl

theorem cell23_4445144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_4445144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445144 prefixEnd_4445144 := by exact prefixLift 4445144
  have htrace : WordTrace (prefixWord ++ tailWord_4445144) baseStart_4445144 baseEnd_4445144 := by
    simpa [prefixWord, tailWord_4445144, baseEnd_4445144] using wordTrace_append hprefix tailTrace_4445144
  have hstable : (prefixWord ++ tailWord_4445144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445144).length < 2 ^ (prefixWord ++ tailWord_4445144).sum := by decide
  have hdescent : baseEnd_4445144 < baseStart_4445144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445151 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 3]
def baseStart_4445151 : Nat := 118140960795 + 4445151 * 2 ^ 59
def prefixEnd_4445151 : Nat := 4983230072969 + 3 ^ 40 * 4445151 * 2
def baseEnd_4445151 : Nat := 2282499044814043059969629

theorem tailTrace_4445151 : CollatzResearch.WordTrace tailWord_4445151 prefixEnd_4445151 2282499044814043059969629 := by
  unfold tailWord_4445151
  simp only [CollatzResearch.WordTrace]
  refine ⟨162127976318984573195191307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108085317545989715463460871 162127976318984573195191307)
  ·
    refine ⟨243191964478476859792786961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162127976318984573195191307 243191964478476859792786961)
    ·
      refine ⟨182393973358857644844590221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243191964478476859792786961 182393973358857644844590221)
      ·
        refine ⟨68397740009571616816721333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182393973358857644844590221 68397740009571616816721333)
        ·
          refine ⟨6412288125897339076567625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68397740009571616816721333 6412288125897339076567625)
          ·
            refine ⟨4809216094423004307425719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6412288125897339076567625 4809216094423004307425719)
            ·
              refine ⟨7213824141634506461138579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809216094423004307425719 7213824141634506461138579)
              ·
                refine ⟨10820736212451759691707869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213824141634506461138579 10820736212451759691707869)
                ·
                  refine ⟨4057776079669409884390451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10820736212451759691707869 4057776079669409884390451)
                  ·
                    refine ⟨6086664119504114826585677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4057776079669409884390451 6086664119504114826585677)
                    ·
                      refine ⟨2282499044814043059969629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086664119504114826585677 2282499044814043059969629)
                      ·
                        rfl

theorem cell23_4445151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_4445151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445151 prefixEnd_4445151 := by exact prefixLift 4445151
  have htrace : WordTrace (prefixWord ++ tailWord_4445151) baseStart_4445151 baseEnd_4445151 := by
    simpa [prefixWord, tailWord_4445151, baseEnd_4445151] using wordTrace_append hprefix tailTrace_4445151
  have hstable : (prefixWord ++ tailWord_4445151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445151).length < 2 ^ (prefixWord ++ tailWord_4445151).sum := by decide
  have hdescent : baseEnd_4445151 < baseStart_4445151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445174 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4445174 : Nat := 118140960795 + 4445174 * 2 ^ 59
def prefixEnd_4445174 : Nat := 4983230072969 + 3 ^ 40 * 4445174 * 2
def baseEnd_4445174 : Nat := 2282510854869096469982023

theorem tailTrace_4445174 : CollatzResearch.WordTrace tailWord_4445174 prefixEnd_4445174 2282510854869096469982023 := by
  unfold tailWord_4445174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133050949868828007704911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108085876798600832082185717 10133050949868828007704911)
  ·
    refine ⟨15199576424803242011557367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10133050949868828007704911 15199576424803242011557367)
    ·
      refine ⟨22799364637204863017336051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15199576424803242011557367 22799364637204863017336051)
      ·
        refine ⟨34199046955807294526004077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22799364637204863017336051 34199046955807294526004077)
        ·
          refine ⟨12824642608427735447251529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34199046955807294526004077 12824642608427735447251529)
          ·
            refine ⟨9618481956320801585438647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12824642608427735447251529 9618481956320801585438647)
            ·
              refine ⟨14427722934481202378157971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618481956320801585438647 14427722934481202378157971)
              ·
                refine ⟨21641584401721803567236957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14427722934481202378157971 21641584401721803567236957)
                ·
                  refine ⟨8115594150645676337713859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21641584401721803567236957 8115594150645676337713859)
                  ·
                    refine ⟨12173391225968514506570789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8115594150645676337713859 12173391225968514506570789)
                    ·
                      refine ⟨2282510854869096469982023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12173391225968514506570789 2282510854869096469982023)
                      ·
                        rfl

theorem cell23_4445174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4445174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445174 prefixEnd_4445174 := by exact prefixLift 4445174
  have htrace : WordTrace (prefixWord ++ tailWord_4445174) baseStart_4445174 baseEnd_4445174 := by
    simpa [prefixWord, tailWord_4445174, baseEnd_4445174] using wordTrace_append hprefix tailTrace_4445174
  have hstable : (prefixWord ++ tailWord_4445174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445174).length < 2 ^ (prefixWord ++ tailWord_4445174).sum := by decide
  have hdescent : baseEnd_4445174 < baseStart_4445174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445177 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_4445177 : Nat := 118140960795 + 4445177 * 2 ^ 59
def prefixEnd_4445177 : Nat := 4983230072969 + 3 ^ 40 * 4445177 * 2
def baseEnd_4445177 : Nat := 2282512395311059958244509

theorem tailTrace_4445177 : CollatzResearch.WordTrace tailWord_4445177 prefixEnd_4445177 2282512395311059958244509 := by
  unfold tailWord_4445177
  simp only [CollatzResearch.WordTrace]
  refine ⟨162128924616890379635637785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108085949744593586423758523 162128924616890379635637785)
  ·
    refine ⟨121596693462667784726728339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162128924616890379635637785 121596693462667784726728339)
    ·
      refine ⟨182395040194001677090092509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121596693462667784726728339 182395040194001677090092509)
      ·
        refine ⟨68398140072750628908784691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182395040194001677090092509 68398140072750628908784691)
        ·
          refine ⟨102597210109125943363177037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68398140072750628908784691 102597210109125943363177037)
          ·
            refine ⟨38473953790922228761191389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102597210109125943363177037 38473953790922228761191389)
            ·
              refine ⟨14427732671595835785446771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38473953790922228761191389 14427732671595835785446771)
              ·
                refine ⟨21641599007393753678170157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14427732671595835785446771 21641599007393753678170157)
                ·
                  refine ⟨8115599627772657629313809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21641599007393753678170157 8115599627772657629313809)
                  ·
                    refine ⟨6086699720829493221985357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8115599627772657629313809 6086699720829493221985357)
                    ·
                      refine ⟨2282512395311059958244509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086699720829493221985357 2282512395311059958244509)
                      ·
                        rfl

theorem cell23_4445177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_4445177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445177 prefixEnd_4445177 := by exact prefixLift 4445177
  have htrace : WordTrace (prefixWord ++ tailWord_4445177) baseStart_4445177 baseEnd_4445177 := by
    simpa [prefixWord, tailWord_4445177, baseEnd_4445177] using wordTrace_append hprefix tailTrace_4445177
  have hstable : (prefixWord ++ tailWord_4445177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445177).length < 2 ^ (prefixWord ++ tailWord_4445177).sum := by decide
  have hdescent : baseEnd_4445177 < baseStart_4445177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445180 : List Nat := [2, 2, 2, 1, 2, 3, 2, 9]
def baseStart_4445180 : Nat := 118140960795 + 4445180 * 2 ^ 59
def prefixEnd_4445180 : Nat := 4983230072969 + 3 ^ 40 * 4445180 * 2
def baseEnd_4445180 : Nat := 84537553176037905426185

theorem tailTrace_4445180 : CollatzResearch.WordTrace tailWord_4445180 prefixEnd_4445180 84537553176037905426185 := by
  unfold tailWord_4445180
  simp only [CollatzResearch.WordTrace]
  refine ⟨81064517017939755573998497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108086022690586340765331329 81064517017939755573998497)
  ·
    refine ⟨60798387763454816680498873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81064517017939755573998497 60798387763454816680498873)
    ·
      refine ⟨45598790822591112510374155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60798387763454816680498873 45598790822591112510374155)
      ·
        refine ⟨68398186233886668765561233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45598790822591112510374155 68398186233886668765561233)
        ·
          refine ⟨51298639675415001574170925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68398186233886668765561233 51298639675415001574170925)
          ·
            refine ⟨19236989878280625590314097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51298639675415001574170925 19236989878280625590314097)
            ·
              refine ⟨14427742408710469192735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19236989878280625590314097 14427742408710469192735573)
              ·
                refine ⟨84537553176037905426185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14427742408710469192735573 84537553176037905426185)
                ·
                  rfl

theorem cell23_4445180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 9].length) (baseStart_4445180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445180 prefixEnd_4445180 := by exact prefixLift 4445180
  have htrace : WordTrace (prefixWord ++ tailWord_4445180) baseStart_4445180 baseEnd_4445180 := by
    simpa [prefixWord, tailWord_4445180, baseEnd_4445180] using wordTrace_append hprefix tailTrace_4445180
  have hstable : (prefixWord ++ tailWord_4445180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445180).length < 2 ^ (prefixWord ++ tailWord_4445180).sum := by decide
  have hdescent : baseEnd_4445180 < baseStart_4445180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445194 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_4445194 : Nat := 118140960795 + 4445194 * 2 ^ 59
def prefixEnd_4445194 : Nat := 4983230072969 + 3 ^ 40 * 4445194 * 2
def baseEnd_4445194 : Nat := 2282521124482186391731931

theorem tailTrace_4445194 : CollatzResearch.WordTrace tailWord_4445194 prefixEnd_4445194 2282521124482186391731931 := by
  unfold tailWord_4445194
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532386164457197884751659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108086363105219194359337757 40532386164457197884751659)
  ·
    refine ⟨60798579246685796827127489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40532386164457197884751659 60798579246685796827127489)
    ·
      refine ⟨45598934435014347620345617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60798579246685796827127489 45598934435014347620345617)
      ·
        refine ⟨34199200826260760715259213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45598934435014347620345617 34199200826260760715259213)
        ·
          refine ⟨12824700309847785268222205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34199200826260760715259213 12824700309847785268222205)
          ·
            refine ⟨4809262616192919475583327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12824700309847785268222205 4809262616192919475583327)
            ·
              refine ⟨7213893924289379213374991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809262616192919475583327 7213893924289379213374991)
              ·
                refine ⟨10820840886434068820062487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213893924289379213374991 10820840886434068820062487)
                ·
                  refine ⟨16231261329651103230093731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10820840886434068820062487 16231261329651103230093731)
                  ·
                    refine ⟨24346891994476654845140597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16231261329651103230093731 24346891994476654845140597)
                    ·
                      refine ⟨2282521124482186391731931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24346891994476654845140597 2282521124482186391731931)
                      ·
                        rfl

theorem cell23_4445194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_4445194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445194 prefixEnd_4445194 := by exact prefixLift 4445194
  have htrace : WordTrace (prefixWord ++ tailWord_4445194) baseStart_4445194 baseEnd_4445194 := by
    simpa [prefixWord, tailWord_4445194, baseEnd_4445194] using wordTrace_append hprefix tailTrace_4445194
  have hstable : (prefixWord ++ tailWord_4445194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445194).length < 2 ^ (prefixWord ++ tailWord_4445194).sum := by decide
  have hdescent : baseEnd_4445194 < baseStart_4445194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445197 : List Nat := [1, 7, 1, 14]
def baseStart_4445197 : Nat := 118140960795 + 4445197 * 2 ^ 59
def prefixEnd_4445197 : Nat := 4983230072969 + 3 ^ 40 * 4445197 * 2
def baseEnd_4445197 : Nat := 1043677487391015034291

theorem tailTrace_4445197 : CollatzResearch.WordTrace tailWord_4445197 prefixEnd_4445197 1043677487391015034291 := by
  unfold tailWord_4445197
  simp only [CollatzResearch.WordTrace]
  refine ⟨162129654076817923051365845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108086436051211948700910563 162129654076817923051365845)
  ·
    refine ⟨3799913767425420071516387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 162129654076817923051365845 3799913767425420071516387)
    ·
      refine ⟨5699870651138130107274581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3799913767425420071516387 5699870651138130107274581)
      ·
        refine ⟨1043677487391015034291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5699870651138130107274581 1043677487391015034291)
        ·
          rfl

theorem cell23_4445197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 14].length) (baseStart_4445197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445197 prefixEnd_4445197 := by exact prefixLift 4445197
  have htrace : WordTrace (prefixWord ++ tailWord_4445197) baseStart_4445197 baseEnd_4445197 := by
    simpa [prefixWord, tailWord_4445197, baseEnd_4445197] using wordTrace_append hprefix tailTrace_4445197
  have hstable : (prefixWord ++ tailWord_4445197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445197).length < 2 ^ (prefixWord ++ tailWord_4445197).sum := by decide
  have hdescent : baseEnd_4445197 < baseStart_4445197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445202 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4445202 : Nat := 118140960795 + 4445202 * 2 ^ 59
def prefixEnd_4445202 : Nat := 4983230072969 + 3 ^ 40 * 4445202 * 2
def baseEnd_4445202 : Nat := 2282525232327422360431895

theorem tailTrace_4445202 : CollatzResearch.WordTrace tailWord_4445202 prefixEnd_4445202 2282525232327422360431895 := by
  unfold tailWord_4445202
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532459110449952226324465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108086557627866539270198573 40532459110449952226324465)
  ·
    refine ⟨30399344332837464169743349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40532459110449952226324465 30399344332837464169743349)
    ·
      refine ⟨2849938531203512265913439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30399344332837464169743349 2849938531203512265913439)
      ·
        refine ⟨4274907796805268398870159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849938531203512265913439 4274907796805268398870159)
        ·
          refine ⟨6412361695207902598305239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4274907796805268398870159 6412361695207902598305239)
          ·
            refine ⟨9618542542811853897457859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412361695207902598305239 9618542542811853897457859)
            ·
              refine ⟨14427813814217780846186789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618542542811853897457859 14427813814217780846186789)
              ·
                refine ⟨2705215090165833908660023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14427813814217780846186789 2705215090165833908660023)
                ·
                  refine ⟨4057822635248750862990035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705215090165833908660023 4057822635248750862990035)
                  ·
                    refine ⟨6086733952873126294485053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4057822635248750862990035 6086733952873126294485053)
                    ·
                      refine ⟨2282525232327422360431895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086733952873126294485053 2282525232327422360431895)
                      ·
                        rfl

theorem cell23_4445202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4445202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445202 prefixEnd_4445202 := by exact prefixLift 4445202
  have htrace : WordTrace (prefixWord ++ tailWord_4445202) baseStart_4445202 baseEnd_4445202 := by
    simpa [prefixWord, tailWord_4445202, baseEnd_4445202] using wordTrace_append hprefix tailTrace_4445202
  have hstable : (prefixWord ++ tailWord_4445202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445202).length < 2 ^ (prefixWord ++ tailWord_4445202).sum := by decide
  have hdescent : baseEnd_4445202 < baseStart_4445202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445208 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 1, 2, 2]
def baseStart_4445208 : Nat := 118140960795 + 4445208 * 2 ^ 59
def prefixEnd_4445208 : Nat := 4983230072969 + 3 ^ 40 * 4445208 * 2
def baseEnd_4445208 : Nat := 2282528313211349336956867

theorem tailTrace_4445208 : CollatzResearch.WordTrace tailWord_4445208 prefixEnd_4445208 2282528313211349336956867 := by
  unfold tailWord_4445208
  simp only [CollatzResearch.WordTrace]
  refine ⟨81065027639889035965008139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108086703519852047953344185 81065027639889035965008139)
  ·
    refine ⟨121597541459833553947512209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81065027639889035965008139 121597541459833553947512209)
    ·
      refine ⟨91198156094875165460634157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121597541459833553947512209 91198156094875165460634157)
      ·
        refine ⟨34199308535578187047737809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91198156094875165460634157 34199308535578187047737809)
        ·
          refine ⟨25649481401683640285803357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34199308535578187047737809 25649481401683640285803357)
          ·
            refine ⟨9618555525631365107176259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25649481401683640285803357 9618555525631365107176259)
            ·
              refine ⟨14427833288447047660764389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618555525631365107176259 14427833288447047660764389)
              ·
                refine ⟨2705218741583821436393323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14427833288447047660764389 2705218741583821436393323)
                ·
                  refine ⟨4057828112375732154589985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705218741583821436393323 4057828112375732154589985)
                  ·
                    refine ⟨3043371084281799115942489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4057828112375732154589985 3043371084281799115942489)
                    ·
                      refine ⟨2282528313211349336956867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043371084281799115942489 2282528313211349336956867)
                      ·
                        rfl

theorem cell23_4445208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_4445208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445208 prefixEnd_4445208 := by exact prefixLift 4445208
  have htrace : WordTrace (prefixWord ++ tailWord_4445208) baseStart_4445208 baseEnd_4445208 := by
    simpa [prefixWord, tailWord_4445208, baseEnd_4445208] using wordTrace_append hprefix tailTrace_4445208
  have hstable : (prefixWord ++ tailWord_4445208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445208).length < 2 ^ (prefixWord ++ tailWord_4445208).sum := by decide
  have hdescent : baseEnd_4445208 < baseStart_4445208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445210 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_4445210 : Nat := 118140960795 + 4445210 * 2 ^ 59
def prefixEnd_4445210 : Nat := 4983230072969 + 3 ^ 40 * 4445210 * 2
def baseEnd_4445210 : Nat := 760843113390886109710619

theorem tailTrace_4445210 : CollatzResearch.WordTrace tailWord_4445210 prefixEnd_4445210 760843113390886109710619 := by
  unfold tailWord_4445210
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532532056442706567897271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108086752150513884181059389 40532532056442706567897271)
  ·
    refine ⟨60798798084664059851845907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40532532056442706567897271 60798798084664059851845907)
    ·
      refine ⟨91198197126996089777768861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60798798084664059851845907 91198197126996089777768861)
      ·
        refine ⟨34199323922623533666663323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91198197126996089777768861 34199323922623533666663323)
        ·
          refine ⟨51298985883935300499994985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34199323922623533666663323 51298985883935300499994985)
          ·
            refine ⟨38474239412951475374996239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51298985883935300499994985 38474239412951475374996239)
            ·
              refine ⟨57711359119427213062494359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38474239412951475374996239 57711359119427213062494359)
              ·
                refine ⟨86567038679140819593741539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57711359119427213062494359 86567038679140819593741539)
                ·
                  refine ⟨129850558018711229390612309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86567038679140819593741539 129850558018711229390612309)
                  ·
                    refine ⟨760843113390886109710619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 129850558018711229390612309 760843113390886109710619)
                    ·
                      rfl

theorem cell23_4445210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_4445210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445210 prefixEnd_4445210 := by exact prefixLift 4445210
  have htrace : WordTrace (prefixWord ++ tailWord_4445210) baseStart_4445210 baseEnd_4445210 := by
    simpa [prefixWord, tailWord_4445210, baseEnd_4445210] using wordTrace_append hprefix tailTrace_4445210
  have hstable : (prefixWord ++ tailWord_4445210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445210).length < 2 ^ (prefixWord ++ tailWord_4445210).sum := by decide
  have hdescent : baseEnd_4445210 < baseStart_4445210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445234 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_4445234 : Nat := 118140960795 + 4445234 * 2 ^ 59
def prefixEnd_4445234 : Nat := 4983230072969 + 3 ^ 40 * 4445234 * 2
def baseEnd_4445234 : Nat := 2282541663708366235231747

theorem tailTrace_4445234 : CollatzResearch.WordTrace tailWord_4445234 prefixEnd_4445234 2282541663708366235231747 := by
  unfold tailWord_4445234
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532750894420969592615689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108087335718455918913641837 40532750894420969592615689)
  ·
    refine ⟨30399563170815727194461767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40532750894420969592615689 30399563170815727194461767)
    ·
      refine ⟨45599344756223590791692651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30399563170815727194461767 45599344756223590791692651)
      ·
        refine ⟨68399017134335386187538977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45599344756223590791692651 68399017134335386187538977)
        ·
          refine ⟨51299262850751539640654233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68399017134335386187538977 51299262850751539640654233)
          ·
            refine ⟨38474447138063654730490675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51299262850751539640654233 38474447138063654730490675)
            ·
              refine ⟨57711670707095482095736013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38474447138063654730490675 57711670707095482095736013)
              ·
                refine ⟨21641876515160805785901005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57711670707095482095736013 21641876515160805785901005)
                ·
                  refine ⟨8115703693185302169712877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21641876515160805785901005 8115703693185302169712877)
                  ·
                    refine ⟨3043388884944488313642329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8115703693185302169712877 3043388884944488313642329)
                    ·
                      refine ⟨2282541663708366235231747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043388884944488313642329 2282541663708366235231747)
                      ·
                        rfl

theorem cell23_4445234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_4445234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445234 prefixEnd_4445234 := by exact prefixLift 4445234
  have htrace : WordTrace (prefixWord ++ tailWord_4445234) baseStart_4445234 baseEnd_4445234 := by
    simpa [prefixWord, tailWord_4445234, baseEnd_4445234] using wordTrace_append hprefix tailTrace_4445234
  have hstable : (prefixWord ++ tailWord_4445234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445234).length < 2 ^ (prefixWord ++ tailWord_4445234).sum := by decide
  have hdescent : baseEnd_4445234 < baseStart_4445234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445281 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_4445281 : Nat := 118140960795 + 4445281 * 2 ^ 59
def prefixEnd_4445281 : Nat := 4983230072969 + 3 ^ 40 * 4445281 * 2
def baseEnd_4445281 : Nat := 2282565797299127551344031

theorem tailTrace_4445281 : CollatzResearch.WordTrace tailWord_4445281 prefixEnd_4445281 2282565797299127551344031 := by
  unfold tailWord_4445281
  simp only [CollatzResearch.WordTrace]
  refine ⟨162132717808513605397423697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108088478539009070264949131 162132717808513605397423697)
  ·
    refine ⟨121599538356385204048067773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162132717808513605397423697 121599538356385204048067773)
    ·
      refine ⟨45599826883644451518025415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121599538356385204048067773 45599826883644451518025415)
      ·
        refine ⟨68399740325466677277038123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45599826883644451518025415 68399740325466677277038123)
        ·
          refine ⟨102599610488200015915557185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68399740325466677277038123 102599610488200015915557185)
          ·
            refine ⟨76949707866150011936667889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102599610488200015915557185 76949707866150011936667889)
            ·
              refine ⟨57712280899612508952500917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76949707866150011936667889 57712280899612508952500917)
              ·
                refine ⟨5410526334338672714296961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57712280899612508952500917 5410526334338672714296961)
                ·
                  refine ⟨4057894750754004535722721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5410526334338672714296961 4057894750754004535722721)
                  ·
                    refine ⟨3043421063065503401792041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4057894750754004535722721 3043421063065503401792041)
                    ·
                      refine ⟨2282565797299127551344031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043421063065503401792041 2282565797299127551344031)
                      ·
                        rfl

theorem cell23_4445281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_4445281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445281 prefixEnd_4445281 := by exact prefixLift 4445281
  have htrace : WordTrace (prefixWord ++ tailWord_4445281) baseStart_4445281 baseEnd_4445281 := by
    simpa [prefixWord, tailWord_4445281, baseEnd_4445281] using wordTrace_append hprefix tailTrace_4445281
  have hstable : (prefixWord ++ tailWord_4445281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445281).length < 2 ^ (prefixWord ++ tailWord_4445281).sum := by decide
  have hdescent : baseEnd_4445281 < baseStart_4445281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445287 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 7]
def baseStart_4445287 : Nat := 118140960795 + 4445287 * 2 ^ 59
def prefixEnd_4445287 : Nat := 4983230072969 + 3 ^ 40 * 4445287 * 2
def baseEnd_4445287 : Nat := 253618764242561614207667

theorem tailTrace_4445287 : CollatzResearch.WordTrace tailWord_4445287 prefixEnd_4445287 253618764242561614207667 := by
  unfold tailWord_4445287
  simp only [CollatzResearch.WordTrace]
  refine ⟨162132936646491868422142115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108088624430994578948094743 162132936646491868422142115)
  ·
    refine ⟨243199404969737802633213173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162132936646491868422142115 243199404969737802633213173)
    ·
      refine ⟨22799944215912918996863735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 243199404969737802633213173 22799944215912918996863735)
      ·
        refine ⟨34199916323869378495295603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22799944215912918996863735 34199916323869378495295603)
        ·
          refine ⟨51299874485804067742943405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34199916323869378495295603 51299874485804067742943405)
          ·
            refine ⟨19237452932176525403603777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51299874485804067742943405 19237452932176525403603777)
            ·
              refine ⟨14428089699132394052702833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19237452932176525403603777 14428089699132394052702833)
              ·
                refine ⟨10821067274349295539527125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14428089699132394052702833 10821067274349295539527125)
                ·
                  refine ⟨253618764242561614207667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10821067274349295539527125 253618764242561614207667)
                  ·
                    rfl

theorem cell23_4445287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 7].length) (baseStart_4445287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445287 prefixEnd_4445287 := by exact prefixLift 4445287
  have htrace : WordTrace (prefixWord ++ tailWord_4445287) baseStart_4445287 baseEnd_4445287 := by
    simpa [prefixWord, tailWord_4445287, baseEnd_4445287] using wordTrace_append hprefix tailTrace_4445287
  have hstable : (prefixWord ++ tailWord_4445287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445287).length < 2 ^ (prefixWord ++ tailWord_4445287).sum := by decide
  have hdescent : baseEnd_4445287 < baseStart_4445287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445297 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_4445297 : Nat := 118140960795 + 4445297 * 2 ^ 59
def prefixEnd_4445297 : Nat := 4983230072969 + 3 ^ 40 * 4445297 * 2
def baseEnd_4445297 : Nat := 2282574012989599488743957

theorem tailTrace_4445297 : CollatzResearch.WordTrace tailWord_4445297 prefixEnd_4445297 2282574012989599488743957 := by
  unfold tailWord_4445297
  simp only [CollatzResearch.WordTrace]
  refine ⟨162133301376455640130006145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108088867584303760086670763 162133301376455640130006145)
  ·
    refine ⟨121599976032341730097504609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162133301376455640130006145 121599976032341730097504609)
    ·
      refine ⟨91199982024256297573128457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121599976032341730097504609 91199982024256297573128457)
      ·
        refine ⟨68399986518192223179846343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91199982024256297573128457 68399986518192223179846343)
        ·
          refine ⟨102599979777288334769769515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68399986518192223179846343 102599979777288334769769515)
          ·
            refine ⟨153899969665932502154654273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102599979777288334769769515 153899969665932502154654273)
            ·
              refine ⟨115424977249449376615990705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153899969665932502154654273 115424977249449376615990705)
              ·
                refine ⟨86568732937087032461993029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115424977249449376615990705 86568732937087032461993029)
                ·
                  refine ⟨16231637425703818586623693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86568732937087032461993029 16231637425703818586623693)
                  ·
                    refine ⟨6086864034638931969983885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16231637425703818586623693 6086864034638931969983885)
                    ·
                      refine ⟨2282574012989599488743957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6086864034638931969983885 2282574012989599488743957)
                      ·
                        rfl

theorem cell23_4445297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_4445297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445297 prefixEnd_4445297 := by exact prefixLift 4445297
  have htrace : WordTrace (prefixWord ++ tailWord_4445297) baseStart_4445297 baseEnd_4445297 := by
    simpa [prefixWord, tailWord_4445297, baseEnd_4445297] using wordTrace_append hprefix tailTrace_4445297
  have hstable : (prefixWord ++ tailWord_4445297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445297).length < 2 ^ (prefixWord ++ tailWord_4445297).sum := by decide
  have hdescent : baseEnd_4445297 < baseStart_4445297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445301 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4445301 : Nat := 118140960795 + 4445301 * 2 ^ 59
def prefixEnd_4445301 : Nat := 4983230072969 + 3 ^ 40 * 4445301 * 2
def baseEnd_4445301 : Nat := 2282576066912217473093939

theorem tailTrace_4445301 : CollatzResearch.WordTrace tailWord_4445301 prefixEnd_4445301 2282576066912217473093939 := by
  unfold tailWord_4445301
  simp only [CollatzResearch.WordTrace]
  refine ⟨162133447268441148813151757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108088964845627432542101171 162133447268441148813151757)
  ·
    refine ⟨60800042725665430804931909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162133447268441148813151757 60800042725665430804931909)
    ·
      refine ⟨11400008011062268275924733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60800042725665430804931909 11400008011062268275924733)
      ·
        refine ⟨4275003004148350603471775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11400008011062268275924733 4275003004148350603471775)
        ·
          refine ⟨6412504506222525905207663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275003004148350603471775 6412504506222525905207663)
          ·
            refine ⟨9618756759333788857811495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412504506222525905207663 9618756759333788857811495)
            ·
              refine ⟨14428135139000683286717243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618756759333788857811495 14428135139000683286717243)
              ·
                refine ⟨21642202708501024930075865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14428135139000683286717243 21642202708501024930075865)
                ·
                  refine ⟨16231652031375768697556899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21642202708501024930075865 16231652031375768697556899)
                  ·
                    refine ⟨24347478047063653046335349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16231652031375768697556899 24347478047063653046335349)
                    ·
                      refine ⟨2282576066912217473093939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24347478047063653046335349 2282576066912217473093939)
                      ·
                        rfl

theorem cell23_4445301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4445301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445301 prefixEnd_4445301 := by exact prefixLift 4445301
  have htrace : WordTrace (prefixWord ++ tailWord_4445301) baseStart_4445301 baseEnd_4445301 := by
    simpa [prefixWord, tailWord_4445301, baseEnd_4445301] using wordTrace_append hprefix tailTrace_4445301
  have hstable : (prefixWord ++ tailWord_4445301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445301).length < 2 ^ (prefixWord ++ tailWord_4445301).sum := by decide
  have hdescent : baseEnd_4445301 < baseStart_4445301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445304 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 5]
def baseStart_4445304 : Nat := 118140960795 + 4445304 * 2 ^ 59
def prefixEnd_4445304 : Nat := 4983230072969 + 3 ^ 40 * 4445304 * 2
def baseEnd_4445304 : Nat := 253619734150464551261825

theorem tailTrace_4445304 : CollatzResearch.WordTrace tailWord_4445304 prefixEnd_4445304 253619734150464551261825 := by
  unfold tailWord_4445304
  simp only [CollatzResearch.WordTrace]
  refine ⟨81066778343715140162755483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108089037791620186883673977 81066778343715140162755483)
  ·
    refine ⟨121600167515572710244133225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81066778343715140162755483 121600167515572710244133225)
    ·
      refine ⟨91200125636679532683099919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121600167515572710244133225 91200125636679532683099919)
      ·
        refine ⟨136800188455019299024649879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91200125636679532683099919 136800188455019299024649879)
        ·
          refine ⟨205200282682528948536974819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136800188455019299024649879 205200282682528948536974819)
          ·
            refine ⟨307800424023793422805462229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205200282682528948536974819 307800424023793422805462229)
            ·
              refine ⟨7214072438057658347003021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 307800424023793422805462229 7214072438057658347003021)
              ·
                refine ⟨2705277164271621880126133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7214072438057658347003021 2705277164271621880126133)
                ·
                  refine ⟨253619734150464551261825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2705277164271621880126133 253619734150464551261825)
                  ·
                    rfl

theorem cell23_4445304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 5].length) (baseStart_4445304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445304 prefixEnd_4445304 := by exact prefixLift 4445304
  have htrace : WordTrace (prefixWord ++ tailWord_4445304) baseStart_4445304 baseEnd_4445304 := by
    simpa [prefixWord, tailWord_4445304, baseEnd_4445304] using wordTrace_append hprefix tailTrace_4445304
  have hstable : (prefixWord ++ tailWord_4445304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445304).length < 2 ^ (prefixWord ++ tailWord_4445304).sum := by decide
  have hdescent : baseEnd_4445304 < baseStart_4445304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445321 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 5]
def baseStart_4445321 : Nat := 118140960795 + 4445321 * 2 ^ 59
def prefixEnd_4445321 : Nat := 4983230072969 + 3 ^ 40 * 4445321 * 2
def baseEnd_4445321 : Nat := 253620704058367488315983

theorem tailTrace_4445321 : CollatzResearch.WordTrace tailWord_4445321 prefixEnd_4445321 253620704058367488315983 := by
  unfold tailWord_4445321
  simp only [CollatzResearch.WordTrace]
  refine ⟨162134176728368692228879817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108089451152245794819253211 162134176728368692228879817)
  ·
    refine ⟨121600632546276519171659863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162134176728368692228879817 121600632546276519171659863)
    ·
      refine ⟨182400948819414778757489795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121600632546276519171659863 182400948819414778757489795)
      ·
        refine ⟨273601423229122168136234693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182400948819414778757489795 273601423229122168136234693)
        ·
          refine ⟨51300266855460406525544005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273601423229122168136234693 51300266855460406525544005)
          ·
            refine ⟨9618800035398826223539501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51300266855460406525544005 9618800035398826223539501)
            ·
              refine ⟨3607050013274559833827313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9618800035398826223539501 3607050013274559833827313)
              ·
                refine ⟨2705287509955919875370485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3607050013274559833827313 2705287509955919875370485)
                ·
                  refine ⟨253620704058367488315983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2705287509955919875370485 253620704058367488315983)
                  ·
                    rfl

theorem cell23_4445321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 5].length) (baseStart_4445321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445321 prefixEnd_4445321 := by exact prefixLift 4445321
  have htrace : WordTrace (prefixWord ++ tailWord_4445321) baseStart_4445321 baseEnd_4445321 := by
    simpa [prefixWord, tailWord_4445321, baseEnd_4445321] using wordTrace_append hprefix tailTrace_4445321
  have hstable : (prefixWord ++ tailWord_4445321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445321).length < 2 ^ (prefixWord ++ tailWord_4445321).sum := by decide
  have hdescent : baseEnd_4445321 < baseStart_4445321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445351 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4445351 : Nat := 118140960795 + 4445351 * 2 ^ 59
def prefixEnd_4445351 : Nat := 4983230072969 + 3 ^ 40 * 4445351 * 2
def baseEnd_4445351 : Nat := 760867246981647425822903

theorem tailTrace_4445351 : CollatzResearch.WordTrace tailWord_4445351 prefixEnd_4445351 760867246981647425822903 := by
  unfold tailWord_4445351
  simp only [CollatzResearch.WordTrace]
  refine ⟨162135270918260007352471907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108090180612173338234981271 162135270918260007352471907)
  ·
    refine ⟨243202906377390011028707861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162135270918260007352471907 243202906377390011028707861)
    ·
      refine ⟨11400136236440156766970681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 243202906377390011028707861 11400136236440156766970681)
      ·
        refine ⟨8550102177330117575228011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11400136236440156766970681 8550102177330117575228011)
        ·
          refine ⟨12825153265995176362842017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8550102177330117575228011 12825153265995176362842017)
          ·
            refine ⟨9618864949496382272131513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12825153265995176362842017 9618864949496382272131513)
            ·
              refine ⟨7214148712122286704098635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9618864949496382272131513 7214148712122286704098635)
              ·
                refine ⟨10821223068183430056147953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7214148712122286704098635 10821223068183430056147953)
                ·
                  refine ⟨8115917301137572542110965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10821223068183430056147953 8115917301137572542110965)
                  ·
                    refine ⟨760867246981647425822903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8115917301137572542110965 760867246981647425822903)
                    ·
                      rfl

theorem cell23_4445351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4445351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445351 prefixEnd_4445351 := by exact prefixLift 4445351
  have htrace : WordTrace (prefixWord ++ tailWord_4445351) baseStart_4445351 baseEnd_4445351 := by
    simpa [prefixWord, tailWord_4445351, baseEnd_4445351] using wordTrace_append hprefix tailTrace_4445351
  have hstable : (prefixWord ++ tailWord_4445351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445351).length < 2 ^ (prefixWord ++ tailWord_4445351).sum := by decide
  have hdescent : baseEnd_4445351 < baseStart_4445351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445367 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_4445367 : Nat := 118140960795 + 4445367 * 2 ^ 59
def prefixEnd_4445367 : Nat := 4983230072969 + 3 ^ 40 * 4445367 * 2
def baseEnd_4445367 : Nat := 2282609956635414214868635

theorem tailTrace_4445367 : CollatzResearch.WordTrace tailWord_4445367 prefixEnd_4445367 2282609956635414214868635 := by
  unfold tailWord_4445367
  simp only [CollatzResearch.WordTrace]
  refine ⟨162135854486202042085054355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108090569657468028056702903 162135854486202042085054355)
  ·
    refine ⟨243203781729303063127581533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162135854486202042085054355 243203781729303063127581533)
    ·
      refine ⟨91201418148488648672843075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243203781729303063127581533 91201418148488648672843075)
      ·
        refine ⟨136802127222732973009264613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91201418148488648672843075 136802127222732973009264613)
        ·
          refine ⟨25650398854262432439237115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136802127222732973009264613 25650398854262432439237115)
          ·
            refine ⟨38475598281393648658855673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25650398854262432439237115 38475598281393648658855673)
            ·
              refine ⟨28856698711045236494141755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38475598281393648658855673 28856698711045236494141755)
              ·
                refine ⟨43285048066567854741212633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28856698711045236494141755 43285048066567854741212633)
                ·
                  refine ⟨32463786049925891055909475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43285048066567854741212633 32463786049925891055909475)
                  ·
                    refine ⟨48695679074888836583864213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32463786049925891055909475 48695679074888836583864213)
                    ·
                      refine ⟨2282609956635414214868635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48695679074888836583864213 2282609956635414214868635)
                      ·
                        rfl

theorem cell23_4445367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_4445367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445367 prefixEnd_4445367 := by exact prefixLift 4445367
  have htrace : WordTrace (prefixWord ++ tailWord_4445367) baseStart_4445367 baseEnd_4445367 := by
    simpa [prefixWord, tailWord_4445367, baseEnd_4445367] using wordTrace_append hprefix tailTrace_4445367
  have hstable : (prefixWord ++ tailWord_4445367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445367).length < 2 ^ (prefixWord ++ tailWord_4445367).sum := by decide
  have hdescent : baseEnd_4445367 < baseStart_4445367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445394 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_4445394 : Nat := 118140960795 + 4445394 * 2 ^ 59
def prefixEnd_4445394 : Nat := 4983230072969 + 3 ^ 40 * 4445394 * 2
def baseEnd_4445394 : Nat := 253624868957009512136779

theorem tailTrace_4445394 : CollatzResearch.WordTrace tailWord_4445394 prefixEnd_4445394 253624868957009512136779 := by
  unfold tailWord_4445394
  simp only [CollatzResearch.WordTrace]
  refine ⟨40534209814276056424071809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108091226171402817130858157 40534209814276056424071809)
  ·
    refine ⟨30400657360707042318053857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40534209814276056424071809 30400657360707042318053857)
    ·
      refine ⟨22800493020530281738540393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30400657360707042318053857 22800493020530281738540393)
      ·
        refine ⟨17100369765397711303905295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22800493020530281738540393 17100369765397711303905295)
        ·
          refine ⟨25650554648096566955857943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17100369765397711303905295 25650554648096566955857943)
          ·
            refine ⟨38475831972144850433786915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25650554648096566955857943 38475831972144850433786915)
            ·
              refine ⟨57713747958217275650680373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38475831972144850433786915 57713747958217275650680373)
              ·
                refine ⟨5410663871082869592251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57713747958217275650680373 5410663871082869592251285)
                ·
                  refine ⟨253624868957009512136779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5410663871082869592251285 253624868957009512136779)
                  ·
                    rfl

theorem cell23_4445394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_4445394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445394 prefixEnd_4445394 := by exact prefixLift 4445394
  have htrace : WordTrace (prefixWord ++ tailWord_4445394) baseStart_4445394 baseEnd_4445394 := by
    simpa [prefixWord, tailWord_4445394, baseEnd_4445394] using wordTrace_append hprefix tailTrace_4445394
  have hstable : (prefixWord ++ tailWord_4445394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445394).length < 2 ^ (prefixWord ++ tailWord_4445394).sum := by decide
  have hdescent : baseEnd_4445394 < baseStart_4445394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445405 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4445405 : Nat := 118140960795 + 4445405 * 2 ^ 59
def prefixEnd_4445405 : Nat := 4983230072969 + 3 ^ 40 * 4445405 * 2
def baseEnd_4445405 : Nat := 2282629468900285066193461

theorem tailTrace_4445405 : CollatzResearch.WordTrace tailWord_4445405 prefixEnd_4445405 2282629468900285066193461 := by
  unfold tailWord_4445405
  simp only [CollatzResearch.WordTrace]
  refine ⟨162137240460064374574937669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108091493640042916383291779 162137240460064374574937669)
  ·
    refine ⟨30400732586262070232800813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162137240460064374574937669 30400732586262070232800813)
    ·
      refine ⟨11400274719848276337300305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30400732586262070232800813 11400274719848276337300305)
      ·
        refine ⟨8550206039886207252975229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11400274719848276337300305 8550206039886207252975229)
        ·
          refine ⟨3206327264957327719865711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8550206039886207252975229 3206327264957327719865711)
          ·
            refine ⟨4809490897435991579798567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206327264957327719865711 4809490897435991579798567)
            ·
              refine ⟨7214236346153987369697851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809490897435991579798567 7214236346153987369697851)
              ·
                refine ⟨10821354519230981054546777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7214236346153987369697851 10821354519230981054546777)
                ·
                  refine ⟨8116015889423235790910083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10821354519230981054546777 8116015889423235790910083)
                  ·
                    refine ⟨12174023834134853686365125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8116015889423235790910083 12174023834134853686365125)
                    ·
                      refine ⟨2282629468900285066193461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12174023834134853686365125 2282629468900285066193461)
                      ·
                        rfl

theorem cell23_4445405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4445405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445405 prefixEnd_4445405 := by exact prefixLift 4445405
  have htrace : WordTrace (prefixWord ++ tailWord_4445405) baseStart_4445405 baseEnd_4445405 := by
    simpa [prefixWord, tailWord_4445405, baseEnd_4445405] using wordTrace_append hprefix tailTrace_4445405
  have hstable : (prefixWord ++ tailWord_4445405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445405).length < 2 ^ (prefixWord ++ tailWord_4445405).sum := by decide
  have hdescent : baseEnd_4445405 < baseStart_4445405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445415 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 1, 4]
def baseStart_4445415 : Nat := 118140960795 + 4445415 * 2 ^ 59
def prefixEnd_4445415 : Nat := 4983230072969 + 3 ^ 40 * 4445415 * 2
def baseEnd_4445415 : Nat := 760878201235610009022805

theorem tailTrace_4445415 : CollatzResearch.WordTrace tailWord_4445415 prefixEnd_4445415 760878201235610009022805 := by
  unfold tailWord_4445415
  simp only [CollatzResearch.WordTrace]
  refine ⟨162137605190028146282801699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108091736793352097521867799 162137605190028146282801699)
  ·
    refine ⟨243206407785042219424202549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162137605190028146282801699 243206407785042219424202549)
    ·
      refine ⟨22800600729847708071018989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 243206407785042219424202549 22800600729847708071018989)
      ·
        refine ⟨8550225273692890526632121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22800600729847708071018989 8550225273692890526632121)
        ·
          refine ⟨6412668955269667894974091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8550225273692890526632121 6412668955269667894974091)
          ·
            refine ⟨9619003432904501842461137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412668955269667894974091 9619003432904501842461137)
            ·
              refine ⟨7214252574678376381845853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9619003432904501842461137 7214252574678376381845853)
              ·
                refine ⟨2705344715504391143192195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7214252574678376381845853 2705344715504391143192195)
                ·
                  refine ⟨4058017073256586714788293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705344715504391143192195 4058017073256586714788293)
                  ·
                    refine ⟨760878201235610009022805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058017073256586714788293 760878201235610009022805)
                    ·
                      rfl

theorem cell23_4445415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_4445415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445415 prefixEnd_4445415 := by exact prefixLift 4445415
  have htrace : WordTrace (prefixWord ++ tailWord_4445415) baseStart_4445415 baseEnd_4445415 := by
    simpa [prefixWord, tailWord_4445415, baseEnd_4445415] using wordTrace_append hprefix tailTrace_4445415
  have hstable : (prefixWord ++ tailWord_4445415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445415).length < 2 ^ (prefixWord ++ tailWord_4445415).sum := by decide
  have hdescent : baseEnd_4445415 < baseStart_4445415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445437 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_4445437 : Nat := 118140960795 + 4445437 * 2 ^ 59
def prefixEnd_4445437 : Nat := 4983230072969 + 3 ^ 40 * 4445437 * 2
def baseEnd_4445437 : Nat := 760881966760409646997771

theorem tailTrace_4445437 : CollatzResearch.WordTrace tailWord_4445437 prefixEnd_4445437 760881966760409646997771 := by
  unfold tailWord_4445437
  simp only [CollatzResearch.WordTrace]
  refine ⟨162138407595948444040102565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108092271730632296026735043 162138407595948444040102565)
  ·
    refine ⟨30400951424240333257519231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162138407595948444040102565 30400951424240333257519231)
    ·
      refine ⟨45601427136360499886278847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30400951424240333257519231 45601427136360499886278847)
      ·
        refine ⟨68402140704540749829418271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45601427136360499886278847 68402140704540749829418271)
        ·
          refine ⟨102603211056811124744127407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68402140704540749829418271 102603211056811124744127407)
          ·
            refine ⟨153904816585216687116191111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102603211056811124744127407 153904816585216687116191111)
            ·
              refine ⟨230857224877825030674286667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153904816585216687116191111 230857224877825030674286667)
              ·
                refine ⟨346285837316737546011430001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230857224877825030674286667 346285837316737546011430001)
                ·
                  refine ⟨259714377987553159508572501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346285837316737546011430001 259714377987553159508572501)
                  ·
                    refine ⟨760881966760409646997771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 259714377987553159508572501 760881966760409646997771)
                    ·
                      rfl

theorem cell23_4445437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_4445437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445437 prefixEnd_4445437 := by exact prefixLift 4445437
  have htrace : WordTrace (prefixWord ++ tailWord_4445437) baseStart_4445437 baseEnd_4445437 := by
    simpa [prefixWord, tailWord_4445437, baseEnd_4445437] using wordTrace_append hprefix tailTrace_4445437
  have hstable : (prefixWord ++ tailWord_4445437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445437).length < 2 ^ (prefixWord ++ tailWord_4445437).sum := by decide
  have hdescent : baseEnd_4445437 < baseStart_4445437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445438 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4445438 : Nat := 118140960795 + 4445438 * 2 ^ 59
def prefixEnd_4445438 : Nat := 4983230072969 + 3 ^ 40 * 4445438 * 2
def baseEnd_4445438 : Nat := 2282646413761883437080809

theorem tailTrace_4445438 : CollatzResearch.WordTrace tailWord_4445438 prefixEnd_4445438 2282646413761883437080809 := by
  unfold tailWord_4445438
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267305508618102651361121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108092296045963214140592645 20267305508618102651361121)
  ·
    refine ⟨15200479131463576988520841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20267305508618102651361121 15200479131463576988520841)
    ·
      refine ⟨11400359348597682741390631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15200479131463576988520841 11400359348597682741390631)
      ·
        refine ⟨17100539022896524112085947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11400359348597682741390631 17100539022896524112085947)
        ·
          refine ⟨25650808534344786168128921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17100539022896524112085947 25650808534344786168128921)
          ·
            refine ⟨19238106400758589626096691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25650808534344786168128921 19238106400758589626096691)
            ·
              refine ⟨28857159601137884439145037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19238106400758589626096691 28857159601137884439145037)
              ·
                refine ⟨10821434850426706664679389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28857159601137884439145037 10821434850426706664679389)
                ·
                  refine ⟨4058038068910014999254771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10821434850426706664679389 4058038068910014999254771)
                  ·
                    refine ⟨6087057103365022498882157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058038068910014999254771 6087057103365022498882157)
                    ·
                      refine ⟨2282646413761883437080809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087057103365022498882157 2282646413761883437080809)
                      ·
                        rfl

theorem cell23_4445438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4445438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445438 prefixEnd_4445438 := by exact prefixLift 4445438
  have htrace : WordTrace (prefixWord ++ tailWord_4445438) baseStart_4445438 baseEnd_4445438 := by
    simpa [prefixWord, tailWord_4445438, baseEnd_4445438] using wordTrace_append hprefix tailTrace_4445438
  have hstable : (prefixWord ++ tailWord_4445438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445438).length < 2 ^ (prefixWord ++ tailWord_4445438).sum := by decide
  have hdescent : baseEnd_4445438 < baseStart_4445438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445472 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4445472 : Nat := 118140960795 + 4445472 * 2 ^ 59
def prefixEnd_4445472 : Nat := 4983230072969 + 3 ^ 40 * 4445472 * 2
def baseEnd_4445472 : Nat := 2282663872104136304055653

theorem tailTrace_4445472 : CollatzResearch.WordTrace tailWord_4445472 prefixEnd_4445472 2282663872104136304055653 := by
  unfold tailWord_4445472
  simp only [CollatzResearch.WordTrace]
  refine ⟨81069842075410822508813335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108093122767214430011751113 81069842075410822508813335)
  ·
    refine ⟨121604763113116233763220003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81069842075410822508813335 121604763113116233763220003)
    ·
      refine ⟨182407144669674350644830005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121604763113116233763220003 182407144669674350644830005)
      ·
        refine ⟨17100669812781970372952813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182407144669674350644830005 17100669812781970372952813)
        ·
          refine ⟨6412751179793238889857305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17100669812781970372952813 6412751179793238889857305)
          ·
            refine ⟨4809563384844929167392979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6412751179793238889857305 4809563384844929167392979)
            ·
              refine ⟨7214345077267393751089469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809563384844929167392979 7214345077267393751089469)
              ·
                refine ⟨2705379403975272656658551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7214345077267393751089469 2705379403975272656658551)
                ·
                  refine ⟨4058069105962908984987827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705379403975272656658551 4058069105962908984987827)
                  ·
                    refine ⟨6087103658944363477481741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058069105962908984987827 6087103658944363477481741)
                    ·
                      refine ⟨2282663872104136304055653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087103658944363477481741 2282663872104136304055653)
                      ·
                        rfl

theorem cell23_4445472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4445472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445472 prefixEnd_4445472 := by exact prefixLift 4445472
  have htrace : WordTrace (prefixWord ++ tailWord_4445472) baseStart_4445472 baseEnd_4445472 := by
    simpa [prefixWord, tailWord_4445472, baseEnd_4445472] using wordTrace_append hprefix tailTrace_4445472
  have hstable : (prefixWord ++ tailWord_4445472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445472).length < 2 ^ (prefixWord ++ tailWord_4445472).sum := by decide
  have hdescent : baseEnd_4445472 < baseStart_4445472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445505 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4445505 : Nat := 118140960795 + 4445505 * 2 ^ 59
def prefixEnd_4445505 : Nat := 4983230072969 + 3 ^ 40 * 4445505 * 2
def baseEnd_4445505 : Nat := 760893605655244891647667

theorem tailTrace_4445505 : CollatzResearch.WordTrace tailWord_4445505 prefixEnd_4445505 760893605655244891647667 := by
  unfold tailWord_4445505
  simp only [CollatzResearch.WordTrace]
  refine ⟨162140887759702091653577969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108093925173134727769051979 162140887759702091653577969)
  ·
    refine ⟨121605665819776568740183477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162140887759702091653577969 121605665819776568740183477)
    ·
      refine ⟨11400531170604053319392201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121605665819776568740183477 11400531170604053319392201)
      ·
        refine ⟨8550398377953039989544151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11400531170604053319392201 8550398377953039989544151)
        ·
          refine ⟨12825597566929559984316227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8550398377953039989544151 12825597566929559984316227)
          ·
            refine ⟨19238396350394339976474341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12825597566929559984316227 19238396350394339976474341)
            ·
              refine ⟨3607199315698938745588939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19238396350394339976474341 3607199315698938745588939)
              ·
                refine ⟨5410798973548408118383409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607199315698938745588939 5410798973548408118383409)
                ·
                  refine ⟨4058099230161306088787557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5410798973548408118383409 4058099230161306088787557)
                  ·
                    refine ⟨760893605655244891647667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058099230161306088787557 760893605655244891647667)
                    ·
                      rfl

theorem cell23_4445505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4445505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445505 prefixEnd_4445505 := by exact prefixLift 4445505
  have htrace : WordTrace (prefixWord ++ tailWord_4445505) baseStart_4445505 baseEnd_4445505 := by
    simpa [prefixWord, tailWord_4445505, baseEnd_4445505] using wordTrace_append hprefix tailTrace_4445505
  have hstable : (prefixWord ++ tailWord_4445505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445505).length < 2 ^ (prefixWord ++ tailWord_4445505).sum := by decide
  have hdescent : baseEnd_4445505 < baseStart_4445505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445546 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4445546 : Nat := 118140960795 + 4445546 * 2 ^ 59
def prefixEnd_4445546 : Nat := 4983230072969 + 3 ^ 40 * 4445546 * 2
def baseEnd_4445546 : Nat := 2282701869672569014530313

theorem tailTrace_4445546 : CollatzResearch.WordTrace tailWord_4445546 prefixEnd_4445546 2282701869672569014530313 := by
  unfold tailWord_4445546
  simp only [CollatzResearch.WordTrace]
  refine ⟨40535595788138388913955123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108094922101702370437213661 40535595788138388913955123)
  ·
    refine ⟨60803393682207583370932685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40535595788138388913955123 60803393682207583370932685)
    ·
      refine ⟨22801272630827843764099757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60803393682207583370932685 22801272630827843764099757)
      ·
        refine ⟨8550477236560441411537409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22801272630827843764099757 8550477236560441411537409)
        ·
          refine ⟨6412857927420331058653057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8550477236560441411537409 6412857927420331058653057)
          ·
            refine ⟨4809643445565248293989793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6412857927420331058653057 4809643445565248293989793)
            ·
              refine ⟨3607232584173936220492345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4809643445565248293989793 3607232584173936220492345)
              ·
                refine ⟨2705424438130452165369259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3607232584173936220492345 2705424438130452165369259)
                ·
                  refine ⟨4058136657195678248053889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705424438130452165369259 4058136657195678248053889)
                  ·
                    refine ⟨3043602492896758686040417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058136657195678248053889 3043602492896758686040417)
                    ·
                      refine ⟨2282701869672569014530313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043602492896758686040417 2282701869672569014530313)
                      ·
                        rfl

theorem cell23_4445546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4445546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445546 prefixEnd_4445546 := by exact prefixLift 4445546
  have htrace : WordTrace (prefixWord ++ tailWord_4445546) baseStart_4445546 baseEnd_4445546 := by
    simpa [prefixWord, tailWord_4445546, baseEnd_4445546] using wordTrace_append hprefix tailTrace_4445546
  have hstable : (prefixWord ++ tailWord_4445546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445546).length < 2 ^ (prefixWord ++ tailWord_4445546).sum := by decide
  have hdescent : baseEnd_4445546 < baseStart_4445546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445551 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 3, 4, 2]
def baseStart_4445551 : Nat := 118140960795 + 4445551 * 2 ^ 59
def prefixEnd_4445551 : Nat := 4983230072969 + 3 ^ 40 * 4445551 * 2
def baseEnd_4445551 : Nat := 2282704437075841494967789

theorem tailTrace_4445551 : CollatzResearch.WordTrace tailWord_4445551 prefixEnd_4445551 2282704437075841494967789 := by
  unfold tailWord_4445551
  simp only [CollatzResearch.WordTrace]
  refine ⟨162142565517535441509752507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108095043678356961006501671 162142565517535441509752507)
  ·
    refine ⟨243213848276303162264628761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162142565517535441509752507 243213848276303162264628761)
    ·
      refine ⟨182410386207227371698471571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243213848276303162264628761 182410386207227371698471571)
      ·
        refine ⟨273615579310841057547707357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182410386207227371698471571 273615579310841057547707357)
        ·
          refine ⟨102605842241565396580390259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273615579310841057547707357 102605842241565396580390259)
          ·
            refine ⟨153908763362348094870585389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102605842241565396580390259 153908763362348094870585389)
            ·
              refine ⟨57715786260880535576469521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153908763362348094870585389 57715786260880535576469521)
              ·
                refine ⟨43286839695660401682352141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57715786260880535576469521 43286839695660401682352141)
                ·
                  refine ⟨16232564885872650630882053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43286839695660401682352141 16232564885872650630882053)
                  ·
                    refine ⟨3043605916101121993290385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16232564885872650630882053 3043605916101121993290385)
                    ·
                      refine ⟨2282704437075841494967789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043605916101121993290385 2282704437075841494967789)
                      ·
                        rfl

theorem cell23_4445551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4, 2].length) (baseStart_4445551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445551 prefixEnd_4445551 := by exact prefixLift 4445551
  have htrace : WordTrace (prefixWord ++ tailWord_4445551) baseStart_4445551 baseEnd_4445551 := by
    simpa [prefixWord, tailWord_4445551, baseEnd_4445551] using wordTrace_append hprefix tailTrace_4445551
  have hstable : (prefixWord ++ tailWord_4445551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445551).length < 2 ^ (prefixWord ++ tailWord_4445551).sum := by decide
  have hdescent : baseEnd_4445551 < baseStart_4445551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445602 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_4445602 : Nat := 118140960795 + 4445602 * 2 ^ 59
def prefixEnd_4445602 : Nat := 4983230072969 + 3 ^ 40 * 4445602 * 2
def baseEnd_4445602 : Nat := 2282730624589220795430055

theorem tailTrace_4445602 : CollatzResearch.WordTrace tailWord_4445602 prefixEnd_4445602 2282730624589220795430055 := by
  unfold tailWord_4445602
  simp only [CollatzResearch.WordTrace]
  refine ⟨40536106410087669304964765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108096283760233784813239373 40536106410087669304964765)
  ·
    refine ⟨15201039903782875989361787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40536106410087669304964765 15201039903782875989361787)
    ·
      refine ⟨22801559855674313984042681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15201039903782875989361787 22801559855674313984042681)
      ·
        refine ⟨17101169891755735488032011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22801559855674313984042681 17101169891755735488032011)
        ·
          refine ⟨25651754837633603232048017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17101169891755735488032011 25651754837633603232048017)
          ·
            refine ⟨19238816128225202424036013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25651754837633603232048017 19238816128225202424036013)
            ·
              refine ⟨7214556048084450909013505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19238816128225202424036013 7214556048084450909013505)
              ·
                refine ⟨5410917036063338181760129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7214556048084450909013505 5410917036063338181760129)
                ·
                  refine ⟨4058187777047503636320097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5410917036063338181760129 4058187777047503636320097)
                  ·
                    refine ⟨3043640832785627727240073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058187777047503636320097 3043640832785627727240073)
                    ·
                      refine ⟨2282730624589220795430055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043640832785627727240073 2282730624589220795430055)
                      ·
                        rfl

theorem cell23_4445602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_4445602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445602 prefixEnd_4445602 := by exact prefixLift 4445602
  have htrace : WordTrace (prefixWord ++ tailWord_4445602) baseStart_4445602 baseEnd_4445602 := by
    simpa [prefixWord, tailWord_4445602, baseEnd_4445602] using wordTrace_append hprefix tailTrace_4445602
  have hstable : (prefixWord ++ tailWord_4445602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445602).length < 2 ^ (prefixWord ++ tailWord_4445602).sum := by decide
  have hdescent : baseEnd_4445602 < baseStart_4445602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445611 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 6, 5, 2]
def baseStart_4445611 : Nat := 118140960795 + 4445611 * 2 ^ 59
def prefixEnd_4445611 : Nat := 4983230072969 + 3 ^ 40 * 4445611 * 2
def baseEnd_4445611 : Nat := 2282735245915111260217513

theorem tailTrace_4445611 : CollatzResearch.WordTrace tailWord_4445611 prefixEnd_4445611 2282735245915111260217513 := by
  unfold tailWord_4445611
  simp only [CollatzResearch.WordTrace]
  refine ⟨162144753897318071756936687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108096502598212047837957791 162144753897318071756936687)
  ·
    refine ⟨243217130845977107635405031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162144753897318071756936687 243217130845977107635405031)
    ·
      refine ⟨364825696268965661453107547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243217130845977107635405031 364825696268965661453107547)
      ·
        refine ⟨547238544403448492179661321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364825696268965661453107547 547238544403448492179661321)
        ·
          refine ⟨410428908302586369134745991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547238544403448492179661321 410428908302586369134745991)
          ·
            refine ⟨615643362453879553702118987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410428908302586369134745991 615643362453879553702118987)
            ·
              refine ⟨923465043680819330553178481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615643362453879553702118987 923465043680819330553178481)
              ·
                refine ⟨692598782760614497914883861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923465043680819330553178481 692598782760614497914883861)
                ·
                  refine ⟨32465567941903804589760181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 692598782760614497914883861 32465567941903804589760181)
                  ·
                    refine ⟨3043646994553481680290017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32465567941903804589760181 3043646994553481680290017)
                    ·
                      refine ⟨2282735245915111260217513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043646994553481680290017 2282735245915111260217513)
                      ·
                        rfl

theorem cell23_4445611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5, 2].length) (baseStart_4445611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445611 prefixEnd_4445611 := by exact prefixLift 4445611
  have htrace : WordTrace (prefixWord ++ tailWord_4445611) baseStart_4445611 baseEnd_4445611 := by
    simpa [prefixWord, tailWord_4445611, baseEnd_4445611] using wordTrace_append hprefix tailTrace_4445611
  have hstable : (prefixWord ++ tailWord_4445611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445611).length < 2 ^ (prefixWord ++ tailWord_4445611).sum := by decide
  have hdescent : baseEnd_4445611 < baseStart_4445611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445621 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4445621 : Nat := 118140960795 + 4445621 * 2 ^ 59
def prefixEnd_4445621 : Nat := 4983230072969 + 3 ^ 40 * 4445621 * 2
def baseEnd_4445621 : Nat := 760913460240552073697489

theorem tailTrace_4445621 : CollatzResearch.WordTrace tailWord_4445621 prefixEnd_4445621 760913460240552073697489 := by
  unfold tailWord_4445621
  simp only [CollatzResearch.WordTrace]
  refine ⟨162145118627281843464800717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108096745751521228976533811 162145118627281843464800717)
  ·
    refine ⟨60804419485230691299300269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162145118627281843464800717 60804419485230691299300269)
    ·
      refine ⟨22801657306961509237237601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60804419485230691299300269 22801657306961509237237601)
      ·
        refine ⟨17101242980221131927928201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22801657306961509237237601 17101242980221131927928201)
        ·
          refine ⟨12825932235165848945946151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17101242980221131927928201 12825932235165848945946151)
          ·
            refine ⟨19238898352748773418919227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12825932235165848945946151 19238898352748773418919227)
            ·
              refine ⟨28858347529123160128378841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19238898352748773418919227 28858347529123160128378841)
              ·
                refine ⟨21643760646842370096284131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28858347529123160128378841 21643760646842370096284131)
                ·
                  refine ⟨32465640970263555144426197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21643760646842370096284131 32465640970263555144426197)
                  ·
                    refine ⟨760913460240552073697489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32465640970263555144426197 760913460240552073697489)
                    ·
                      rfl

theorem cell23_4445621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4445621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445621 prefixEnd_4445621 := by exact prefixLift 4445621
  have htrace : WordTrace (prefixWord ++ tailWord_4445621) baseStart_4445621 baseEnd_4445621 := by
    simpa [prefixWord, tailWord_4445621, baseEnd_4445621] using wordTrace_append hprefix tailTrace_4445621
  have hstable : (prefixWord ++ tailWord_4445621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445621).length < 2 ^ (prefixWord ++ tailWord_4445621).sum := by decide
  have hdescent : baseEnd_4445621 < baseStart_4445621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445641 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_4445641 : Nat := 118140960795 + 4445641 * 2 ^ 59
def prefixEnd_4445641 : Nat := 4983230072969 + 3 ^ 40 * 4445641 * 2
def baseEnd_4445641 : Nat := 2282750650334746142842375

theorem tailTrace_4445641 : CollatzResearch.WordTrace tailWord_4445641 prefixEnd_4445641 2282750650334746142842375 := by
  unfold tailWord_4445641
  simp only [CollatzResearch.WordTrace]
  refine ⟨162145848087209386880528777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108097232058139591253685851 162145848087209386880528777)
  ·
    refine ⟨121609386065407040160396583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162145848087209386880528777 121609386065407040160396583)
    ·
      refine ⟨182414079098110560240594875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121609386065407040160396583 182414079098110560240594875)
      ·
        refine ⟨273621118647165840360892313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182414079098110560240594875 273621118647165840360892313)
        ·
          refine ⟨205215838985374380270669235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273621118647165840360892313 205215838985374380270669235)
          ·
            refine ⟨307823758478061570406003853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205215838985374380270669235 307823758478061570406003853)
            ·
              refine ⟨115433909429273088902251445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307823758478061570406003853 115433909429273088902251445)
              ·
                refine ⟨10821929008994352084586073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115433909429273088902251445 10821929008994352084586073)
                ·
                  refine ⟨8116446756745764063439555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10821929008994352084586073 8116446756745764063439555)
                  ·
                    refine ⟨12174670135118646095159333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8116446756745764063439555 12174670135118646095159333)
                    ·
                      refine ⟨2282750650334746142842375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12174670135118646095159333 2282750650334746142842375)
                      ·
                        rfl

theorem cell23_4445641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_4445641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445641 prefixEnd_4445641 := by exact prefixLift 4445641
  have htrace : WordTrace (prefixWord ++ tailWord_4445641) baseStart_4445641 baseEnd_4445641 := by
    simpa [prefixWord, tailWord_4445641, baseEnd_4445641] using wordTrace_append hprefix tailTrace_4445641
  have hstable : (prefixWord ++ tailWord_4445641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445641).length < 2 ^ (prefixWord ++ tailWord_4445641).sum := by decide
  have hdescent : baseEnd_4445641 < baseStart_4445641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445658 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_4445658 : Nat := 118140960795 + 4445658 * 2 ^ 59
def prefixEnd_4445658 : Nat := 4983230072969 + 3 ^ 40 * 4445658 * 2
def baseEnd_4445658 : Nat := 2282759379505872576329797

theorem tailTrace_4445658 : CollatzResearch.WordTrace tailWord_4445658 prefixEnd_4445658 2282759379505872576329797 := by
  unfold tailWord_4445658
  simp only [CollatzResearch.WordTrace]
  refine ⟨40536617032036949695974407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108097645418765199189265085 40536617032036949695974407)
  ·
    refine ⟨60804925548055424543961611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40536617032036949695974407 60804925548055424543961611)
    ·
      refine ⟨91207388322083136815942417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60804925548055424543961611 91207388322083136815942417)
      ·
        refine ⟨68405541241562352611956813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91207388322083136815942417 68405541241562352611956813)
        ·
          refine ⟨25652077965585882229483805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68405541241562352611956813 25652077965585882229483805)
          ·
            refine ⟨9619529237094705836056427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25652077965585882229483805 9619529237094705836056427)
            ·
              refine ⟨14429293855642058754084641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9619529237094705836056427 14429293855642058754084641)
              ·
                refine ⟨10821970391731544065563481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14429293855642058754084641 10821970391731544065563481)
                ·
                  refine ⟨8116477793798658049172611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10821970391731544065563481 8116477793798658049172611)
                  ·
                    refine ⟨12174716690697987073758917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8116477793798658049172611 12174716690697987073758917)
                    ·
                      refine ⟨2282759379505872576329797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12174716690697987073758917 2282759379505872576329797)
                      ·
                        rfl

theorem cell23_4445658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_4445658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445658 prefixEnd_4445658 := by exact prefixLift 4445658
  have htrace : WordTrace (prefixWord ++ tailWord_4445658) baseStart_4445658 baseEnd_4445658 := by
    simpa [prefixWord, tailWord_4445658, baseEnd_4445658] using wordTrace_append hprefix tailTrace_4445658
  have hstable : (prefixWord ++ tailWord_4445658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445658).length < 2 ^ (prefixWord ++ tailWord_4445658).sum := by decide
  have hdescent : baseEnd_4445658 < baseStart_4445658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445678 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_4445678 : Nat := 118140960795 + 4445678 * 2 ^ 59
def prefixEnd_4445678 : Nat := 4983230072969 + 3 ^ 40 * 4445678 * 2
def baseEnd_4445678 : Nat := 2282769649118962498079705

theorem tailTrace_4445678 : CollatzResearch.WordTrace tailWord_4445678 prefixEnd_4445678 2282769649118962498079705 := by
  unfold tailWord_4445678
  simp only [CollatzResearch.WordTrace]
  refine ⟨20268399698509417774953211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108098131725383561466417125 20268399698509417774953211)
  ·
    refine ⟨30402599547764126662429817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20268399698509417774953211 30402599547764126662429817)
    ·
      refine ⟨22801949660823094996822363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30402599547764126662429817 22801949660823094996822363)
      ·
        refine ⟨34202924491234642495233545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22801949660823094996822363 34202924491234642495233545)
        ·
          refine ⟨25652193368425981871425159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34202924491234642495233545 25652193368425981871425159)
          ·
            refine ⟨38478290052638972807137739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25652193368425981871425159 38478290052638972807137739)
            ·
              refine ⟨57717435078958459210706609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38478290052638972807137739 57717435078958459210706609)
              ·
                refine ⟨43288076309218844408029957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57717435078958459210706609 43288076309218844408029957)
                ·
                  refine ⟨8116514307978533326505617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43288076309218844408029957 8116514307978533326505617)
                  ·
                    refine ⟨6087385730983899994879213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8116514307978533326505617 6087385730983899994879213)
                    ·
                      refine ⟨2282769649118962498079705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087385730983899994879213 2282769649118962498079705)
                      ·
                        rfl

theorem cell23_4445678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_4445678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445678 prefixEnd_4445678 := by exact prefixLift 4445678
  have htrace : WordTrace (prefixWord ++ tailWord_4445678) baseStart_4445678 baseEnd_4445678 := by
    simpa [prefixWord, tailWord_4445678, baseEnd_4445678] using wordTrace_append hprefix tailTrace_4445678
  have hstable : (prefixWord ++ tailWord_4445678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445678).length < 2 ^ (prefixWord ++ tailWord_4445678).sum := by decide
  have hdescent : baseEnd_4445678 < baseStart_4445678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445725 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_4445725 : Nat := 118140960795 + 4445725 * 2 ^ 59
def prefixEnd_4445725 : Nat := 4983230072969 + 3 ^ 40 * 4445725 * 2
def baseEnd_4445725 : Nat := 2282793782709723814191989

theorem tailTrace_4445725 : CollatzResearch.WordTrace tailWord_4445725 prefixEnd_4445725 2282793782709723814191989 := by
  unfold tailWord_4445725
  simp only [CollatzResearch.WordTrace]
  refine ⟨162148911818905069226586629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108099274545936712817724419 162148911818905069226586629)
  ·
    refine ⟨30402920966044700479984993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162148911818905069226586629 30402920966044700479984993)
    ·
      refine ⟨22802190724533525359988745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30402920966044700479984993 22802190724533525359988745)
      ·
        refine ⟨17101643043400144019991559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22802190724533525359988745 17101643043400144019991559)
        ·
          refine ⟨25652464565100216029987339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17101643043400144019991559 25652464565100216029987339)
          ·
            refine ⟨38478696847650324044981009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25652464565100216029987339 38478696847650324044981009)
            ·
              refine ⟨28859022635737743033735757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38478696847650324044981009 28859022635737743033735757)
              ·
                refine ⟨10822133488401653637650909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28859022635737743033735757 10822133488401653637650909)
                ·
                  refine ⟨4058300058150620114119091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10822133488401653637650909 4058300058150620114119091)
                  ·
                    refine ⟨6087450087225930171178637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058300058150620114119091 6087450087225930171178637)
                    ·
                      refine ⟨2282793782709723814191989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087450087225930171178637 2282793782709723814191989)
                      ·
                        rfl

theorem cell23_4445725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_4445725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445725 prefixEnd_4445725 := by exact prefixLift 4445725
  have htrace : WordTrace (prefixWord ++ tailWord_4445725) baseStart_4445725 baseEnd_4445725 := by
    simpa [prefixWord, tailWord_4445725, baseEnd_4445725] using wordTrace_append hprefix tailTrace_4445725
  have hstable : (prefixWord ++ tailWord_4445725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445725).length < 2 ^ (prefixWord ++ tailWord_4445725).sum := by decide
  have hdescent : baseEnd_4445725 < baseStart_4445725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445726 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4445726 : Nat := 118140960795 + 4445726 * 2 ^ 59
def prefixEnd_4445726 : Nat := 4983230072969 + 3 ^ 40 * 4445726 * 2
def baseEnd_4445726 : Nat := 2282794296190378310279485

theorem tailTrace_4445726 : CollatzResearch.WordTrace tailWord_4445726 prefixEnd_4445726 2282794296190378310279485 := by
  unfold tailWord_4445726
  simp only [CollatzResearch.WordTrace]
  refine ⟨20268618536487680799671629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108099298861267630931582021 20268618536487680799671629)
  ·
    refine ⟨7600731951182880299876861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20268618536487680799671629 7600731951182880299876861)
    ·
      refine ⟨2850274481693580112453823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7600731951182880299876861 2850274481693580112453823)
      ·
        refine ⟨4275411722540370168680735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850274481693580112453823 4275411722540370168680735)
        ·
          refine ⟨6413117583810555253021103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275411722540370168680735 6413117583810555253021103)
          ·
            refine ⟨9619676375715832879531655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413117583810555253021103 9619676375715832879531655)
            ·
              refine ⟨14429514563573749319297483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9619676375715832879531655 14429514563573749319297483)
              ·
                refine ⟨21644271845360623978946225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14429514563573749319297483 21644271845360623978946225)
                ·
                  refine ⟨16233203884020467984209669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21644271845360623978946225 16233203884020467984209669)
                  ·
                    refine ⟨3043725728253837747039313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16233203884020467984209669 3043725728253837747039313)
                    ·
                      refine ⟨2282794296190378310279485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043725728253837747039313 2282794296190378310279485)
                      ·
                        rfl

theorem cell23_4445726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4445726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445726 prefixEnd_4445726 := by exact prefixLift 4445726
  have htrace : WordTrace (prefixWord ++ tailWord_4445726) baseStart_4445726 baseEnd_4445726 := by
    simpa [prefixWord, tailWord_4445726, baseEnd_4445726] using wordTrace_append hprefix tailTrace_4445726
  have hstable : (prefixWord ++ tailWord_4445726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445726).length < 2 ^ (prefixWord ++ tailWord_4445726).sum := by decide
  have hdescent : baseEnd_4445726 < baseStart_4445726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445728 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_4445728 : Nat := 118140960795 + 4445728 * 2 ^ 59
def prefixEnd_4445728 : Nat := 4983230072969 + 3 ^ 40 * 4445728 * 2
def baseEnd_4445728 : Nat := 760931774383895767484825

theorem tailTrace_4445728 : CollatzResearch.WordTrace tailWord_4445728 prefixEnd_4445728 760931774383895767484825 := by
  unfold tailWord_4445728
  simp only [CollatzResearch.WordTrace]
  refine ⟨81074510618947100369472919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108099347491929467159297225 81074510618947100369472919)
  ·
    refine ⟨121611765928420650554209379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81074510618947100369472919 121611765928420650554209379)
    ·
      refine ⟨182417648892630975831314069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121611765928420650554209379 182417648892630975831314069)
      ·
        refine ⟨8550827291842076992092847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 182417648892630975831314069 8550827291842076992092847)
        ·
          refine ⟨12826240937763115488139271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8550827291842076992092847 12826240937763115488139271)
          ·
            refine ⟨19239361406644673232208907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12826240937763115488139271 19239361406644673232208907)
            ·
              refine ⟨28859042109967009848313361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19239361406644673232208907 28859042109967009848313361)
              ·
                refine ⟨21644281582475257386235021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28859042109967009848313361 21644281582475257386235021)
                ·
                  refine ⟨8116605593428221519838133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21644281582475257386235021 8116605593428221519838133)
                  ·
                    refine ⟨760931774383895767484825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8116605593428221519838133 760931774383895767484825)
                    ·
                      rfl

theorem cell23_4445728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_4445728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445728 prefixEnd_4445728 := by exact prefixLift 4445728
  have htrace : WordTrace (prefixWord ++ tailWord_4445728) baseStart_4445728 baseEnd_4445728 := by
    simpa [prefixWord, tailWord_4445728, baseEnd_4445728] using wordTrace_append hprefix tailTrace_4445728
  have hstable : (prefixWord ++ tailWord_4445728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445728).length < 2 ^ (prefixWord ++ tailWord_4445728).sum := by decide
  have hdescent : baseEnd_4445728 < baseStart_4445728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445742 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4445742 : Nat := 118140960795 + 4445742 * 2 ^ 59
def prefixEnd_4445742 : Nat := 4983230072969 + 3 ^ 40 * 4445742 * 2
def baseEnd_4445742 : Nat := 2282802511880850247679411

theorem tailTrace_4445742 : CollatzResearch.WordTrace tailWord_4445742 prefixEnd_4445742 2282802511880850247679411 := by
  unfold tailWord_4445742
  simp only [CollatzResearch.WordTrace]
  refine ⟨20268691482480435141244435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108099687906562320753303653 20268691482480435141244435)
  ·
    refine ⟨30403037223720652711866653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20268691482480435141244435 30403037223720652711866653)
    ·
      refine ⟨11401138958895244766949995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30403037223720652711866653 11401138958895244766949995)
      ·
        refine ⟨17101708438342867150424993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11401138958895244766949995 17101708438342867150424993)
        ·
          refine ⟨12826281328757150362818745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17101708438342867150424993 12826281328757150362818745)
          ·
            refine ⟨9619710996567862772114059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12826281328757150362818745 9619710996567862772114059)
            ·
              refine ⟨14429566494851794158171089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9619710996567862772114059 14429566494851794158171089)
              ·
                refine ⟨10822174871138845618628317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14429566494851794158171089 10822174871138845618628317)
                ·
                  refine ⟨4058315576677067106985619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10822174871138845618628317 4058315576677067106985619)
                  ·
                    refine ⟨6087473365015600660478429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058315576677067106985619 6087473365015600660478429)
                    ·
                      refine ⟨2282802511880850247679411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087473365015600660478429 2282802511880850247679411)
                      ·
                        rfl

theorem cell23_4445742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4445742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445742 prefixEnd_4445742 := by exact prefixLift 4445742
  have htrace : WordTrace (prefixWord ++ tailWord_4445742) baseStart_4445742 baseEnd_4445742 := by
    simpa [prefixWord, tailWord_4445742, baseEnd_4445742] using wordTrace_append hprefix tailTrace_4445742
  have hstable : (prefixWord ++ tailWord_4445742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445742).length < 2 ^ (prefixWord ++ tailWord_4445742).sum := by decide
  have hdescent : baseEnd_4445742 < baseStart_4445742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445752 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 2, 3, 2]
def baseStart_4445752 : Nat := 118140960795 + 4445752 * 2 ^ 59
def prefixEnd_4445752 : Nat := 4983230072969 + 3 ^ 40 * 4445752 * 2
def baseEnd_4445752 : Nat := 2282807646687395208554365

theorem tailTrace_4445752 : CollatzResearch.WordTrace tailWord_4445752 prefixEnd_4445752 2282807646687395208554365 := by
  unfold tailWord_4445752
  simp only [CollatzResearch.WordTrace]
  refine ⟨81074948294903626418909755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108099931059871501891879673 81074948294903626418909755)
  ·
    refine ⟨121612422442355439628364633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81074948294903626418909755 121612422442355439628364633)
    ·
      refine ⟨91209316831766579721273475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121612422442355439628364633 91209316831766579721273475)
      ·
        refine ⟨136813975247649869581910213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91209316831766579721273475 136813975247649869581910213)
        ·
          refine ⟨25652620358934350546608165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136813975247649869581910213 25652620358934350546608165)
          ·
            refine ⟨4809866317300190727489031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25652620358934350546608165 4809866317300190727489031)
            ·
              refine ⟨7214799475950286091233547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809866317300190727489031 7214799475950286091233547)
              ·
                refine ⟨10822199213925429136850321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7214799475950286091233547 10822199213925429136850321)
                ·
                  refine ⟨8116649410444071852637741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10822199213925429136850321 8116649410444071852637741)
                  ·
                    refine ⟨3043743528916526944739153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8116649410444071852637741 3043743528916526944739153)
                    ·
                      refine ⟨2282807646687395208554365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043743528916526944739153 2282807646687395208554365)
                      ·
                        rfl

theorem cell23_4445752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_4445752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445752 prefixEnd_4445752 := by exact prefixLift 4445752
  have htrace : WordTrace (prefixWord ++ tailWord_4445752) baseStart_4445752 baseEnd_4445752 := by
    simpa [prefixWord, tailWord_4445752, baseEnd_4445752] using wordTrace_append hprefix tailTrace_4445752
  have hstable : (prefixWord ++ tailWord_4445752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445752).length < 2 ^ (prefixWord ++ tailWord_4445752).sum := by decide
  have hdescent : baseEnd_4445752 < baseStart_4445752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445765 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 5, 2, 2]
def baseStart_4445765 : Nat := 118140960795 + 4445765 * 2 ^ 59
def prefixEnd_4445765 : Nat := 4983230072969 + 3 ^ 40 * 4445765 * 2
def baseEnd_4445765 : Nat := 2282814321935903657691805

theorem tailTrace_4445765 : CollatzResearch.WordTrace tailWord_4445765 prefixEnd_4445765 2282814321935903657691805 := by
  unfold tailWord_4445765
  simp only [CollatzResearch.WordTrace]
  refine ⟨162150370738760156058042749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108100247159173437372028499 162150370738760156058042749)
  ·
    refine ⟨60806389027035058521766031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162150370738760156058042749 60806389027035058521766031)
    ·
      refine ⟨91209583540552587782649047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60806389027035058521766031 91209583540552587782649047)
      ·
        refine ⟨136814375310828881673973571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91209583540552587782649047 136814375310828881673973571)
        ·
          refine ⟨205221562966243322510960357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136814375310828881673973571 205221562966243322510960357)
          ·
            refine ⟨38479043056170622970805067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205221562966243322510960357 38479043056170622970805067)
            ·
              refine ⟨57718564584255934456207601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38479043056170622970805067 57718564584255934456207601)
              ·
                refine ⟨43288923438191950842155701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57718564584255934456207601 43288923438191950842155701)
                ·
                  refine ⟨4058336572330495391452097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43288923438191950842155701 4058336572330495391452097)
                  ·
                    refine ⟨3043752429247871543589073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058336572330495391452097 3043752429247871543589073)
                    ·
                      refine ⟨2282814321935903657691805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043752429247871543589073 2282814321935903657691805)
                      ·
                        rfl

theorem cell23_4445765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_4445765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445765 prefixEnd_4445765 := by exact prefixLift 4445765
  have htrace : WordTrace (prefixWord ++ tailWord_4445765) baseStart_4445765 baseEnd_4445765 := by
    simpa [prefixWord, tailWord_4445765, baseEnd_4445765] using wordTrace_append hprefix tailTrace_4445765
  have hstable : (prefixWord ++ tailWord_4445765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445765).length < 2 ^ (prefixWord ++ tailWord_4445765).sum := by decide
  have hdescent : baseEnd_4445765 < baseStart_4445765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445781 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4445781 : Nat := 118140960795 + 4445781 * 2 ^ 59
def prefixEnd_4445781 : Nat := 4983230072969 + 3 ^ 40 * 4445781 * 2
def baseEnd_4445781 : Nat := 2282822537626375595091731

theorem tailTrace_4445781 : CollatzResearch.WordTrace tailWord_4445781 prefixEnd_4445781 2282822537626375595091731 := by
  unfold tailWord_4445781
  simp only [CollatzResearch.WordTrace]
  refine ⟨162150954306702190790625197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108100636204468127193750131 162150954306702190790625197)
  ·
    refine ⟨60806607865013321546484449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162150954306702190790625197 60806607865013321546484449)
    ·
      refine ⟨45604955898759991159863337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60806607865013321546484449 45604955898759991159863337)
      ·
        refine ⟨34203716924069993369897503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45604955898759991159863337 34203716924069993369897503)
        ·
          refine ⟨51305575386104990054846255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34203716924069993369897503 51305575386104990054846255)
          ·
            refine ⟨76958363079157485082269383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51305575386104990054846255 76958363079157485082269383)
            ·
              refine ⟨115437544618736227623404075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76958363079157485082269383 115437544618736227623404075)
              ·
                refine ⟨173156316928104341435106113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115437544618736227623404075 173156316928104341435106113)
                ·
                  refine ⟨129867237696078256076329585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173156316928104341435106113 129867237696078256076329585)
                  ·
                    refine ⟨97400428272058692057247189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129867237696078256076329585 97400428272058692057247189)
                    ·
                      refine ⟨2282822537626375595091731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97400428272058692057247189 2282822537626375595091731)
                      ·
                        rfl

theorem cell23_4445781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4445781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445781 prefixEnd_4445781 := by exact prefixLift 4445781
  have htrace : WordTrace (prefixWord ++ tailWord_4445781) baseStart_4445781 baseEnd_4445781 := by
    simpa [prefixWord, tailWord_4445781, baseEnd_4445781] using wordTrace_append hprefix tailTrace_4445781
  have hstable : (prefixWord ++ tailWord_4445781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445781).length < 2 ^ (prefixWord ++ tailWord_4445781).sum := by decide
  have hdescent : baseEnd_4445781 < baseStart_4445781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445795 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 4]
def baseStart_4445795 : Nat := 118140960795 + 4445795 * 2 ^ 59
def prefixEnd_4445795 : Nat := 4983230072969 + 3 ^ 40 * 4445795 * 2
def baseEnd_4445795 : Nat := 2282829726355538540316667

theorem tailTrace_4445795 : CollatzResearch.WordTrace tailWord_4445795 prefixEnd_4445795 2282829726355538540316667 := by
  unfold tailWord_4445795
  simp only [CollatzResearch.WordTrace]
  refine ⟨162151464928651471181634839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108100976619100980787756559 162151464928651471181634839)
  ·
    refine ⟨243227197392977206772452259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162151464928651471181634839 243227197392977206772452259)
    ·
      refine ⟨364840796089465810158678389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243227197392977206772452259 364840796089465810158678389)
      ·
        refine ⟨34203824633387419702376099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 364840796089465810158678389 34203824633387419702376099)
        ·
          refine ⟨51305736950081129553564149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34203824633387419702376099 51305736950081129553564149)
          ·
            refine ⟨4809912839070105895646639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51305736950081129553564149 4809912839070105895646639)
            ·
              refine ⟨7214869258605158843469959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809912839070105895646639 7214869258605158843469959)
              ·
                refine ⟨10822303887907738265204939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7214869258605158843469959 10822303887907738265204939)
                ·
                  refine ⟨16233455831861607397807409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10822303887907738265204939 16233455831861607397807409)
                  ·
                    refine ⟨12175091873896205548355557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16233455831861607397807409 12175091873896205548355557)
                    ·
                      refine ⟨2282829726355538540316667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12175091873896205548355557 2282829726355538540316667)
                      ·
                        rfl

theorem cell23_4445795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_4445795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445795 prefixEnd_4445795 := by exact prefixLift 4445795
  have htrace : WordTrace (prefixWord ++ tailWord_4445795) baseStart_4445795 baseEnd_4445795 := by
    simpa [prefixWord, tailWord_4445795, baseEnd_4445795] using wordTrace_append hprefix tailTrace_4445795
  have hstable : (prefixWord ++ tailWord_4445795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445795).length < 2 ^ (prefixWord ++ tailWord_4445795).sum := by decide
  have hdescent : baseEnd_4445795 < baseStart_4445795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445801 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_4445801 : Nat := 118140960795 + 4445801 * 2 ^ 59
def prefixEnd_4445801 : Nat := 4983230072969 + 3 ^ 40 * 4445801 * 2
def baseEnd_4445801 : Nat := 760944269079821838947213

theorem tailTrace_4445801 : CollatzResearch.WordTrace tailWord_4445801 prefixEnd_4445801 760944269079821838947213 := by
  unfold tailWord_4445801
  simp only [CollatzResearch.WordTrace]
  refine ⟨162151683766629734206353257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108101122511086489470902171 162151683766629734206353257)
  ·
    refine ⟨121613762824972300654764943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162151683766629734206353257 121613762824972300654764943)
    ·
      refine ⟨182420644237458450982147415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121613762824972300654764943 182420644237458450982147415)
      ·
        refine ⟨273630966356187676473221123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182420644237458450982147415 273630966356187676473221123)
        ·
          refine ⟨410446449534281514709831685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273630966356187676473221123 410446449534281514709831685)
          ·
            refine ⟨76958709287677784008093441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 410446449534281514709831685 76958709287677784008093441)
            ·
              refine ⟨57719031965758338006070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76958709287677784008093441 57719031965758338006070081)
              ·
                refine ⟨43289273974318753504552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57719031965758338006070081 43289273974318753504552561)
                ·
                  refine ⟨32466955480739065128414421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43289273974318753504552561 32466955480739065128414421)
                  ·
                    refine ⟨760944269079821838947213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32466955480739065128414421 760944269079821838947213)
                    ·
                      rfl

theorem cell23_4445801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_4445801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445801 prefixEnd_4445801 := by exact prefixLift 4445801
  have htrace : WordTrace (prefixWord ++ tailWord_4445801) baseStart_4445801 baseEnd_4445801 := by
    simpa [prefixWord, tailWord_4445801, baseEnd_4445801] using wordTrace_append hprefix tailTrace_4445801
  have hstable : (prefixWord ++ tailWord_4445801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445801).length < 2 ^ (prefixWord ++ tailWord_4445801).sum := by decide
  have hdescent : baseEnd_4445801 < baseStart_4445801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445802 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_4445802 : Nat := 118140960795 + 4445802 * 2 ^ 59
def prefixEnd_4445802 : Nat := 4983230072969 + 3 ^ 40 * 4445802 * 2
def baseEnd_4445802 : Nat := 2282833320720120012929135

theorem tailTrace_4445802 : CollatzResearch.WordTrace tailWord_4445802 prefixEnd_4445802 2282833320720120012929135 := by
  unfold tailWord_4445802
  simp only [CollatzResearch.WordTrace]
  refine ⟨40537930059906527844284915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108101146826417407584759773 40537930059906527844284915)
  ·
    refine ⟨60806895089859791766427373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40537930059906527844284915 60806895089859791766427373)
    ·
      refine ⟨22802585658697421912410265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60806895089859791766427373 22802585658697421912410265)
      ·
        refine ⟨17101939244023066434307699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22802585658697421912410265 17101939244023066434307699)
        ·
          refine ⟨25652908866034599651461549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17101939244023066434307699 25652908866034599651461549)
          ·
            refine ⟨9619840824762974869298081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25652908866034599651461549 9619840824762974869298081)
            ·
              refine ⟨7214880618572231151973561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9619840824762974869298081 7214880618572231151973561)
              ·
                refine ⟨5411160463929173363980171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7214880618572231151973561 5411160463929173363980171)
                ·
                  refine ⟨8116740695893760045970257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411160463929173363980171 8116740695893760045970257)
                  ·
                    refine ⟨6087555521920320034477693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8116740695893760045970257 6087555521920320034477693)
                    ·
                      refine ⟨2282833320720120012929135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087555521920320034477693 2282833320720120012929135)
                      ·
                        rfl

theorem cell23_4445802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_4445802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445802 prefixEnd_4445802 := by exact prefixLift 4445802
  have htrace : WordTrace (prefixWord ++ tailWord_4445802) baseStart_4445802 baseEnd_4445802 := by
    simpa [prefixWord, tailWord_4445802, baseEnd_4445802] using wordTrace_append hprefix tailTrace_4445802
  have hstable : (prefixWord ++ tailWord_4445802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445802).length < 2 ^ (prefixWord ++ tailWord_4445802).sum := by decide
  have hdescent : baseEnd_4445802 < baseStart_4445802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445895 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 5]
def baseStart_4445895 : Nat := 118140960795 + 4445895 * 2 ^ 59
def prefixEnd_4445895 : Nat := 4983230072969 + 3 ^ 40 * 4445895 * 2
def baseEnd_4445895 : Nat := 253653452713443127674023

theorem tailTrace_4445895 : CollatzResearch.WordTrace tailWord_4445895 prefixEnd_4445895 253653452713443127674023 := by
  unfold tailWord_4445895
  simp only [CollatzResearch.WordTrace]
  refine ⟨162155112228289188260275139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108103408152192792173516759 162155112228289188260275139)
  ·
    refine ⟨243232668342433782390412709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162155112228289188260275139 243232668342433782390412709)
    ·
      refine ⟨45606125314206334198202383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243232668342433782390412709 45606125314206334198202383)
      ·
        refine ⟨68409187971309501297303575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45606125314206334198202383 68409187971309501297303575)
        ·
          refine ⟨102613781956964251945955363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68409187971309501297303575 102613781956964251945955363)
          ·
            refine ⟨153920672935446377918933045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102613781956964251945955363 153920672935446377918933045)
            ·
              refine ⟨14430063087698097929899973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153920672935446377918933045 14430063087698097929899973)
              ·
                refine ⟨2705636828943393361856245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14430063087698097929899973 2705636828943393361856245)
                ·
                  refine ⟨253653452713443127674023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2705636828943393361856245 253653452713443127674023)
                  ·
                    rfl

theorem cell23_4445895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 5].length) (baseStart_4445895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445895 prefixEnd_4445895 := by exact prefixLift 4445895
  have htrace : WordTrace (prefixWord ++ tailWord_4445895) baseStart_4445895 baseEnd_4445895 := by
    simpa [prefixWord, tailWord_4445895, baseEnd_4445895] using wordTrace_append hprefix tailTrace_4445895
  have hstable : (prefixWord ++ tailWord_4445895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445895).length < 2 ^ (prefixWord ++ tailWord_4445895).sum := by decide
  have hdescent : baseEnd_4445895 < baseStart_4445895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445905 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_4445905 : Nat := 118140960795 + 4445905 * 2 ^ 59
def prefixEnd_4445905 : Nat := 4983230072969 + 3 ^ 40 * 4445905 * 2
def baseEnd_4445905 : Nat := 2282886209227533109941161

theorem tailTrace_4445905 : CollatzResearch.WordTrace tailWord_4445905 prefixEnd_4445905 2282886209227533109941161 := by
  unfold tailWord_4445905
  simp only [CollatzResearch.WordTrace]
  refine ⟨162155476958252959968139169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108103651305501973312092779 162155476958252959968139169)
  ·
    refine ⟨121616607718689719976104377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162155476958252959968139169 121616607718689719976104377)
    ·
      refine ⟨91212455789017289982078283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121616607718689719976104377 91212455789017289982078283)
      ·
        refine ⟨136818683683525934973117425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91212455789017289982078283 136818683683525934973117425)
        ·
          refine ⟨102614012762644451229838069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136818683683525934973117425 102614012762644451229838069)
          ·
            refine ⟨9620063696497917302797319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102614012762644451229838069 9620063696497917302797319)
            ·
              refine ⟨14430095544746875954195979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9620063696497917302797319 14430095544746875954195979)
              ·
                refine ⟨21645143317120313931293969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14430095544746875954195979 21645143317120313931293969)
                ·
                  refine ⟨16233857487840235448470477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21645143317120313931293969 16233857487840235448470477)
                  ·
                    refine ⟨6087696557940088293176429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16233857487840235448470477 6087696557940088293176429)
                    ·
                      refine ⟨2282886209227533109941161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087696557940088293176429 2282886209227533109941161)
                      ·
                        rfl

theorem cell23_4445905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_4445905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445905 prefixEnd_4445905 := by exact prefixLift 4445905
  have htrace : WordTrace (prefixWord ++ tailWord_4445905) baseStart_4445905 baseEnd_4445905 := by
    simpa [prefixWord, tailWord_4445905, baseEnd_4445905] using wordTrace_append hprefix tailTrace_4445905
  have hstable : (prefixWord ++ tailWord_4445905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445905).length < 2 ^ (prefixWord ++ tailWord_4445905).sum := by decide
  have hdescent : baseEnd_4445905 < baseStart_4445905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445940 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4445940 : Nat := 118140960795 + 4445940 * 2 ^ 59
def prefixEnd_4445940 : Nat := 4983230072969 + 3 ^ 40 * 4445940 * 2
def baseEnd_4445940 : Nat := 2282904181050440473003501

theorem tailTrace_4445940 : CollatzResearch.WordTrace tailWord_4445940 prefixEnd_4445940 2282904181050440473003501 := by
  unfold tailWord_4445940
  simp only [CollatzResearch.WordTrace]
  refine ⟨81078376756563080472831637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108104502342084107297108849 81078376756563080472831637)
  ·
    refine ⟨3800548910463894397163983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81078376756563080472831637 3800548910463894397163983)
    ·
      refine ⟨5700823365695841595745975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3800548910463894397163983 5700823365695841595745975)
      ·
        refine ⟨8551235048543762393618963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5700823365695841595745975 8551235048543762393618963)
        ·
          refine ⟨12826852572815643590428445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8551235048543762393618963 12826852572815643590428445)
          ·
            refine ⟨4810069714805866346410667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12826852572815643590428445 4810069714805866346410667)
            ·
              refine ⟨7215104572208799519616001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810069714805866346410667 7215104572208799519616001)
              ·
                refine ⟨5411328429156599639712001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7215104572208799519616001 5411328429156599639712001)
                ·
                  refine ⟨4058496321867449729784001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5411328429156599639712001 4058496321867449729784001)
                  ·
                    refine ⟨3043872241400587297338001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058496321867449729784001 3043872241400587297338001)
                    ·
                      refine ⟨2282904181050440473003501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043872241400587297338001 2282904181050440473003501)
                      ·
                        rfl

theorem cell23_4445940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4445940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445940 prefixEnd_4445940 := by exact prefixLift 4445940
  have htrace : WordTrace (prefixWord ++ tailWord_4445940) baseStart_4445940 baseEnd_4445940 := by
    simpa [prefixWord, tailWord_4445940, baseEnd_4445940] using wordTrace_append hprefix tailTrace_4445940
  have hstable : (prefixWord ++ tailWord_4445940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445940).length < 2 ^ (prefixWord ++ tailWord_4445940).sum := by decide
  have hdescent : baseEnd_4445940 < baseStart_4445940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445955 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 3, 4]
def baseStart_4445955 : Nat := 118140960795 + 4445955 * 2 ^ 59
def prefixEnd_4445955 : Nat := 4983230072969 + 3 ^ 40 * 4445955 * 2
def baseEnd_4445955 : Nat := 760970627753419304771977

theorem tailTrace_4445955 : CollatzResearch.WordTrace tailWord_4445955 prefixEnd_4445955 760970627753419304771977 := by
  unfold tailWord_4445955
  simp only [CollatzResearch.WordTrace]
  refine ⟨162157300608071818507459319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108104867072047879004972879 162157300608071818507459319)
  ·
    refine ⟨243235950912107727761188979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162157300608071818507459319 243235950912107727761188979)
    ·
      refine ⟨364853926368161591641783469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243235950912107727761188979 364853926368161591641783469)
      ·
        refine ⟨136820222388060596865668801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 364853926368161591641783469 136820222388060596865668801)
        ·
          refine ⟨102615166791045447649251601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136820222388060596865668801 102615166791045447649251601)
          ·
            refine ⟨76961375093284085736938701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102615166791045447649251601 76961375093284085736938701)
            ·
              refine ⟨28860515659981532151352013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76961375093284085736938701 28860515659981532151352013)
              ·
                refine ⟨10822693372493074556757005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28860515659981532151352013 10822693372493074556757005)
                ·
                  refine ⟨4058510014684902958783877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10822693372493074556757005 4058510014684902958783877)
                  ·
                    refine ⟨760970627753419304771977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058510014684902958783877 760970627753419304771977)
                    ·
                      rfl

theorem cell23_4445955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 4].length) (baseStart_4445955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445955 prefixEnd_4445955 := by exact prefixLift 4445955
  have htrace : WordTrace (prefixWord ++ tailWord_4445955) baseStart_4445955 baseEnd_4445955 := by
    simpa [prefixWord, tailWord_4445955, baseEnd_4445955] using wordTrace_append hprefix tailTrace_4445955
  have hstable : (prefixWord ++ tailWord_4445955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445955).length < 2 ^ (prefixWord ++ tailWord_4445955).sum := by decide
  have hdescent : baseEnd_4445955 < baseStart_4445955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445962 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_4445962 : Nat := 118140960795 + 4445962 * 2 ^ 59
def prefixEnd_4445962 : Nat := 4983230072969 + 3 ^ 40 * 4445962 * 2
def baseEnd_4445962 : Nat := 2282915477624839386928399

theorem tailTrace_4445962 : CollatzResearch.WordTrace tailWord_4445962 prefixEnd_4445962 2282915477624839386928399 := by
  unfold tailWord_4445962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40539388979761614675741035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108105037279364305801976093 40539388979761614675741035)
  ·
    refine ⟨60809083469642422013611553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40539388979761614675741035 60809083469642422013611553)
    ·
      refine ⟨45606812602231816510208665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60809083469642422013611553 45606812602231816510208665)
      ·
        refine ⟨34205109451673862382656499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45606812602231816510208665 34205109451673862382656499)
        ·
          refine ⟨51307664177510793573984749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34205109451673862382656499 51307664177510793573984749)
          ·
            refine ⟨19240374066566547590244281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51307664177510793573984749 19240374066566547590244281)
            ·
              refine ⟨14430280549924910692683211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19240374066566547590244281 14430280549924910692683211)
              ·
                refine ⟨21645420824887366039024817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14430280549924910692683211 21645420824887366039024817)
                ·
                  refine ⟨16234065618665524529268613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21645420824887366039024817 16234065618665524529268613)
                  ·
                    refine ⟨3043887303499785849237865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16234065618665524529268613 3043887303499785849237865)
                    ·
                      refine ⟨2282915477624839386928399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043887303499785849237865 2282915477624839386928399)
                      ·
                        rfl

theorem cell23_4445962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_4445962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445962 prefixEnd_4445962 := by exact prefixLift 4445962
  have htrace : WordTrace (prefixWord ++ tailWord_4445962) baseStart_4445962 baseEnd_4445962 := by
    simpa [prefixWord, tailWord_4445962, baseEnd_4445962] using wordTrace_append hprefix tailTrace_4445962
  have hstable : (prefixWord ++ tailWord_4445962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445962).length < 2 ^ (prefixWord ++ tailWord_4445962).sum := by decide
  have hdescent : baseEnd_4445962 < baseStart_4445962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445989 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_4445989 : Nat := 118140960795 + 4445989 * 2 ^ 59
def prefixEnd_4445989 : Nat := 4983230072969 + 3 ^ 40 * 4445989 * 2
def baseEnd_4445989 : Nat := 760976447200836927096925

theorem tailTrace_4445989 : CollatzResearch.WordTrace tailWord_4445989 prefixEnd_4445989 760976447200836927096925 := by
  unfold tailWord_4445989
  simp only [CollatzResearch.WordTrace]
  refine ⟨162158540689948642314197021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108105693793299094876131347 162158540689948642314197021)
  ·
    refine ⟨60809452758730740867823883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162158540689948642314197021 60809452758730740867823883)
    ·
      refine ⟨91214179138096111301735825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60809452758730740867823883 91214179138096111301735825)
      ·
        refine ⟨68410634353572083476301869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91214179138096111301735825 68410634353572083476301869)
        ·
          refine ⟨25653987882589531303613201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68410634353572083476301869 25653987882589531303613201)
          ·
            refine ⟨19240490911942148477709901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25653987882589531303613201 19240490911942148477709901)
            ·
              refine ⟨7215184091978305679141213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19240490911942148477709901 7215184091978305679141213)
              ·
                refine ⟨2705694034491864629677955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7215184091978305679141213 2705694034491864629677955)
                ·
                  refine ⟨4058541051737796944516933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705694034491864629677955 4058541051737796944516933)
                  ·
                    refine ⟨760976447200836927096925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058541051737796944516933 760976447200836927096925)
                    ·
                      rfl

theorem cell23_4445989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_4445989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4445989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4445989 prefixEnd_4445989 := by exact prefixLift 4445989
  have htrace : WordTrace (prefixWord ++ tailWord_4445989) baseStart_4445989 baseEnd_4445989 := by
    simpa [prefixWord, tailWord_4445989, baseEnd_4445989] using wordTrace_append hprefix tailTrace_4445989
  have hstable : (prefixWord ++ tailWord_4445989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445989).length < 2 ^ (prefixWord ++ tailWord_4445989).sum := by decide
  have hdescent : baseEnd_4445989 < baseStart_4445989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446006 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4446006 : Nat := 118140960795 + 4446006 * 2 ^ 59
def prefixEnd_4446006 : Nat := 4983230072969 + 3 ^ 40 * 4446006 * 2
def baseEnd_4446006 : Nat := 760979356924545738259399

theorem tailTrace_4446006 : CollatzResearch.WordTrace tailWord_4446006 prefixEnd_4446006 760979356924545738259399 := by
  unfold tailWord_4446006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10134947545680440888597867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108106107153924702811710581 10134947545680440888597867)
  ·
    refine ⟨15202421318520661332896801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10134947545680440888597867 15202421318520661332896801)
    ·
      refine ⟨11401815988890495999672601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15202421318520661332896801 11401815988890495999672601)
      ·
        refine ⟨8551361991667871999754451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11401815988890495999672601 8551361991667871999754451)
        ·
          refine ⟨12827042987501807999631677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8551361991667871999754451 12827042987501807999631677)
          ·
            refine ⟨4810141120313177999861879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12827042987501807999631677 4810141120313177999861879)
            ·
              refine ⟨7215211680469766999792819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810141120313177999861879 7215211680469766999792819)
              ·
                refine ⟨10822817520704650499689229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7215211680469766999792819 10822817520704650499689229)
                ·
                  refine ⟨4058556570264243937383461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10822817520704650499689229 4058556570264243937383461)
                  ·
                    refine ⟨760979356924545738259399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058556570264243937383461 760979356924545738259399)
                    ·
                      rfl

theorem cell23_4446006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4446006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446006 prefixEnd_4446006 := by exact prefixLift 4446006
  have htrace : WordTrace (prefixWord ++ tailWord_4446006) baseStart_4446006 baseEnd_4446006 := by
    simpa [prefixWord, tailWord_4446006, baseEnd_4446006] using wordTrace_append hprefix tailTrace_4446006
  have hstable : (prefixWord ++ tailWord_4446006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446006).length < 2 ^ (prefixWord ++ tailWord_4446006).sum := by decide
  have hdescent : baseEnd_4446006 < baseStart_4446006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446065 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_4446065 : Nat := 118140960795 + 4446065 * 2 ^ 59
def prefixEnd_4446065 : Nat := 4983230072969 + 3 ^ 40 * 4446065 * 2
def baseEnd_4446065 : Nat := 2282968366132252483940425

theorem tailTrace_4446065 : CollatzResearch.WordTrace tailWord_4446065 prefixEnd_4446065 2282968366132252483940425 := by
  unfold tailWord_4446065
  simp only [CollatzResearch.WordTrace]
  refine ⟨162161312637673307293963649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108107541758448871529309099 162161312637673307293963649)
  ·
    refine ⟨121620984478254980470472737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162161312637673307293963649 121620984478254980470472737)
    ·
      refine ⟨91215738358691235352854553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121620984478254980470472737 91215738358691235352854553)
      ·
        refine ⟨68411803769018426514640915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91215738358691235352854553 68411803769018426514640915)
        ·
          refine ⟨102617705653527639771961373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68411803769018426514640915 102617705653527639771961373)
          ·
            refine ⟨38481639620072864914485515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102617705653527639771961373 38481639620072864914485515)
            ·
              refine ⟨57722459430109297371728273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38481639620072864914485515 57722459430109297371728273)
              ·
                refine ⟨43291844572581973028796205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57722459430109297371728273 43291844572581973028796205)
                ·
                  refine ⟨16234441714718239885798577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43291844572581973028796205 16234441714718239885798577)
                  ·
                    refine ⟨12175831286038679914348933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16234441714718239885798577 12175831286038679914348933)
                    ·
                      refine ⟨2282968366132252483940425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12175831286038679914348933 2282968366132252483940425)
                      ·
                        rfl

theorem cell23_4446065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_4446065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446065 prefixEnd_4446065 := by exact prefixLift 4446065
  have htrace : WordTrace (prefixWord ++ tailWord_4446065) baseStart_4446065 baseEnd_4446065 := by
    simpa [prefixWord, tailWord_4446065, baseEnd_4446065] using wordTrace_append hprefix tailTrace_4446065
  have hstable : (prefixWord ++ tailWord_4446065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446065).length < 2 ^ (prefixWord ++ tailWord_4446065).sum := by decide
  have hdescent : baseEnd_4446065 < baseStart_4446065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446103 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 1, 2, 2]
def baseStart_4446103 : Nat := 118140960795 + 4446103 * 2 ^ 59
def prefixEnd_4446103 : Nat := 4983230072969 + 3 ^ 40 * 4446103 * 2
def baseEnd_4446103 : Nat := 2282987878397123335265251

theorem tailTrace_4446103 : CollatzResearch.WordTrace tailWord_4446103 prefixEnd_4446103 2282987878397123335265251 := by
  unfold tailWord_4446103
  simp only [CollatzResearch.WordTrace]
  refine ⟨162162698611535639783846963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108108465741023759855897975 162162698611535639783846963)
  ·
    refine ⟨243244047917303459675770445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162162698611535639783846963 243244047917303459675770445)
    ·
      refine ⟨91216517968988797378413917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243244047917303459675770445 91216517968988797378413917)
      ·
        refine ⟨34206194238370799016905219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91216517968988797378413917 34206194238370799016905219)
        ·
          refine ⟨51309291357556198525357829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34206194238370799016905219 51309291357556198525357829)
          ·
            refine ⟨9620492129541787223504593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51309291357556198525357829 9620492129541787223504593)
            ·
              refine ⟨7215369097156340417628445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9620492129541787223504593 7215369097156340417628445)
              ·
                refine ⟨2705763411433627656610667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7215369097156340417628445 2705763411433627656610667)
                ·
                  refine ⟨4058645117150441484916001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705763411433627656610667 4058645117150441484916001)
                  ·
                    refine ⟨3043983837862831113687001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058645117150441484916001 3043983837862831113687001)
                    ·
                      refine ⟨2282987878397123335265251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043983837862831113687001 2282987878397123335265251)
                      ·
                        rfl

theorem cell23_4446103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_4446103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446103 prefixEnd_4446103 := by exact prefixLift 4446103
  have htrace : WordTrace (prefixWord ++ tailWord_4446103) baseStart_4446103 baseEnd_4446103 := by
    simpa [prefixWord, tailWord_4446103, baseEnd_4446103] using wordTrace_append hprefix tailTrace_4446103
  have hstable : (prefixWord ++ tailWord_4446103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446103).length < 2 ^ (prefixWord ++ tailWord_4446103).sum := by decide
  have hdescent : baseEnd_4446103 < baseStart_4446103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446106 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3]
def baseStart_4446106 : Nat := 118140960795 + 4446106 * 2 ^ 59
def prefixEnd_4446106 : Nat := 4983230072969 + 3 ^ 40 * 4446106 * 2
def baseEnd_4446106 : Nat := 2282989418839086823527737

theorem tailTrace_4446106 : CollatzResearch.WordTrace tailWord_4446106 prefixEnd_4446106 2282989418839086823527737 := by
  unfold tailWord_4446106
  simp only [CollatzResearch.WordTrace]
  refine ⟨40540702007631192824051543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108108538687016514197470781 40540702007631192824051543)
  ·
    refine ⟨60811053011446789236077315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40540702007631192824051543 60811053011446789236077315)
    ·
      refine ⟨91216579517170183854115973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60811053011446789236077315 91216579517170183854115973)
      ·
        refine ⟨17103108659469409472646745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91216579517170183854115973 17103108659469409472646745)
        ·
          refine ⟨12827331494602057104485059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17103108659469409472646745 12827331494602057104485059)
          ·
            refine ⟨19240997241903085656727589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12827331494602057104485059 19240997241903085656727589)
            ·
              refine ⟨3607686982856828560636423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19240997241903085656727589 3607686982856828560636423)
              ·
                refine ⟨5411530474285242840954635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607686982856828560636423 5411530474285242840954635)
                ·
                  refine ⟨8117295711427864261431953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411530474285242840954635 8117295711427864261431953)
                  ·
                    refine ⟨6087971783570898196073965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8117295711427864261431953 6087971783570898196073965)
                    ·
                      refine ⟨2282989418839086823527737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6087971783570898196073965 2282989418839086823527737)
                      ·
                        rfl

theorem cell23_4446106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_4446106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446106 prefixEnd_4446106 := by exact prefixLift 4446106
  have htrace : WordTrace (prefixWord ++ tailWord_4446106) baseStart_4446106 baseEnd_4446106 := by
    simpa [prefixWord, tailWord_4446106, baseEnd_4446106] using wordTrace_append hprefix tailTrace_4446106
  have hstable : (prefixWord ++ tailWord_4446106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446106).length < 2 ^ (prefixWord ++ tailWord_4446106).sum := by decide
  have hdescent : baseEnd_4446106 < baseStart_4446106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446113 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 2, 4]
def baseStart_4446113 : Nat := 118140960795 + 4446113 * 2 ^ 59
def prefixEnd_4446113 : Nat := 4983230072969 + 3 ^ 40 * 4446113 * 2
def baseEnd_4446113 : Nat := 760997671067889432046735

theorem tailTrace_4446113 : CollatzResearch.WordTrace tailWord_4446113 prefixEnd_4446113 760997671067889432046735 := by
  unfold tailWord_4446113
  simp only [CollatzResearch.WordTrace]
  refine ⟨162163063341499411491710993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108108708894332940994473995 162163063341499411491710993)
  ·
    refine ⟨121622297506124558618783245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162163063341499411491710993 121622297506124558618783245)
    ·
      refine ⟨45608361564796709482043717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121622297506124558618783245 45608361564796709482043717)
      ·
        refine ⟨8551567793399383027883197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45608361564796709482043717 8551567793399383027883197)
        ·
          refine ⟨3206837922524768635456199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8551567793399383027883197 3206837922524768635456199)
          ·
            refine ⟨4810256883787152953184299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206837922524768635456199 4810256883787152953184299)
            ·
              refine ⟨7215385325680729429776449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810256883787152953184299 7215385325680729429776449)
              ·
                refine ⟨5411538994260547072332337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7215385325680729429776449 5411538994260547072332337)
                ·
                  refine ⟨4058654245695410304249253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5411538994260547072332337 4058654245695410304249253)
                  ·
                    refine ⟨760997671067889432046735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058654245695410304249253 760997671067889432046735)
                    ·
                      rfl

theorem cell23_4446113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_4446113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446113 prefixEnd_4446113 := by exact prefixLift 4446113
  have htrace : WordTrace (prefixWord ++ tailWord_4446113) baseStart_4446113 baseEnd_4446113 := by
    simpa [prefixWord, tailWord_4446113, baseEnd_4446113] using wordTrace_append hprefix tailTrace_4446113
  have hstable : (prefixWord ++ tailWord_4446113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446113).length < 2 ^ (prefixWord ++ tailWord_4446113).sum := by decide
  have hdescent : baseEnd_4446113 < baseStart_4446113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446120 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4446120 : Nat := 118140960795 + 4446120 * 2 ^ 59
def prefixEnd_4446120 : Nat := 4983230072969 + 3 ^ 40 * 4446120 * 2
def baseEnd_4446120 : Nat := 2282996607568249768752673

theorem tailTrace_4446120 : CollatzResearch.WordTrace tailWord_4446120 prefixEnd_4446120 2282996607568249768752673 := by
  unfold tailWord_4446120
  simp only [CollatzResearch.WordTrace]
  refine ⟨81081659326237025843607907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108108879101649367791477209 81081659326237025843607907)
  ·
    refine ⟨121622488989355538765411861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81081659326237025843607907 121622488989355538765411861)
    ·
      refine ⟨5701054171376040879628681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121622488989355538765411861 5701054171376040879628681)
      ·
        refine ⟨4275790628532030659721511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5701054171376040879628681 4275790628532030659721511)
        ·
          refine ⟨6413685942798045989582267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275790628532030659721511 6413685942798045989582267)
          ·
            refine ⟨9620528914197068984373401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413685942798045989582267 9620528914197068984373401)
            ·
              refine ⟨7215396685647801738280051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9620528914197068984373401 7215396685647801738280051)
              ·
                refine ⟨10823095028471702607420077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7215396685647801738280051 10823095028471702607420077)
                ·
                  refine ⟨4058660635676888477782529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10823095028471702607420077 4058660635676888477782529)
                  ·
                    refine ⟨3043995476757666358336897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058660635676888477782529 3043995476757666358336897)
                    ·
                      refine ⟨2282996607568249768752673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3043995476757666358336897 2282996607568249768752673)
                      ·
                        rfl

theorem cell23_4446120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4446120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446120 prefixEnd_4446120 := by exact prefixLift 4446120
  have htrace : WordTrace (prefixWord ++ tailWord_4446120) baseStart_4446120 baseEnd_4446120 := by
    simpa [prefixWord, tailWord_4446120, baseEnd_4446120] using wordTrace_append hprefix tailTrace_4446120
  have hstable : (prefixWord ++ tailWord_4446120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446120).length < 2 ^ (prefixWord ++ tailWord_4446120).sum := by decide
  have hdescent : baseEnd_4446120 < baseStart_4446120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446136 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 2, 1, 3]
def baseStart_4446136 : Nat := 118140960795 + 4446136 * 2 ^ 59
def prefixEnd_4446136 : Nat := 4983230072969 + 3 ^ 40 * 4446136 * 2
def baseEnd_4446136 : Nat := 2283004823258721706152599

theorem tailTrace_4446136 : CollatzResearch.WordTrace tailWord_4446136 prefixEnd_4446136 2283004823258721706152599 := by
  unfold tailWord_4446136
  simp only [CollatzResearch.WordTrace]
  refine ⟨81081951110208043209899131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108109268146944057613198841 81081951110208043209899131)
  ·
    refine ⟨121622926665312064814848697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81081951110208043209899131 121622926665312064814848697)
    ·
      refine ⟨91217194998984048611136523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121622926665312064814848697 91217194998984048611136523)
      ·
        refine ⟨136825792498476072916704785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91217194998984048611136523 136825792498476072916704785)
        ·
          refine ⟨102619344373857054687528589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136825792498476072916704785 102619344373857054687528589)
          ·
            refine ⟨38482254140196395507823221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102619344373857054687528589 38482254140196395507823221)
            ·
              refine ⟨3607711325643412078858427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38482254140196395507823221 3607711325643412078858427)
              ·
                refine ⟨5411566988465118118287641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607711325643412078858427 5411566988465118118287641)
                ·
                  refine ⟨4058675241348838588715731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5411566988465118118287641 4058675241348838588715731)
                  ·
                    refine ⟨6088012862023257883073597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058675241348838588715731 6088012862023257883073597)
                    ·
                      refine ⟨2283004823258721706152599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088012862023257883073597 2283004823258721706152599)
                      ·
                        rfl

theorem cell23_4446136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_4446136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446136 prefixEnd_4446136 := by exact prefixLift 4446136
  have htrace : WordTrace (prefixWord ++ tailWord_4446136) baseStart_4446136 baseEnd_4446136 := by
    simpa [prefixWord, tailWord_4446136, baseEnd_4446136] using wordTrace_append hprefix tailTrace_4446136
  have hstable : (prefixWord ++ tailWord_4446136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446136).length < 2 ^ (prefixWord ++ tailWord_4446136).sum := by decide
  have hdescent : baseEnd_4446136 < baseStart_4446136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446159 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 6, 2, 2]
def baseStart_4446159 : Nat := 118140960795 + 4446159 * 2 ^ 59
def prefixEnd_4446159 : Nat := 4983230072969 + 3 ^ 40 * 4446159 * 2
def baseEnd_4446159 : Nat := 2283016633313775116164993

theorem tailTrace_4446159 : CollatzResearch.WordTrace tailWord_4446159 prefixEnd_4446159 2283016633313775116164993 := by
  unfold tailWord_4446159
  simp only [CollatzResearch.WordTrace]
  refine ⟨162164741099332761347885531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108109827399555174231923687 162164741099332761347885531)
  ·
    refine ⟨243247111648999142021828297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162164741099332761347885531 243247111648999142021828297)
    ·
      refine ⟨182435333736749356516371223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243247111648999142021828297 182435333736749356516371223)
      ·
        refine ⟨273653000605124034774556835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182435333736749356516371223 273653000605124034774556835)
        ·
          refine ⟨410479500907686052161835253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273653000605124034774556835 410479500907686052161835253)
          ·
            refine ⟨38482453210095567390172055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 410479500907686052161835253 38482453210095567390172055)
            ·
              refine ⟨57723679815143351085258083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38482453210095567390172055 57723679815143351085258083)
              ·
                refine ⟨86585519722715026627887125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57723679815143351085258083 86585519722715026627887125)
                ·
                  refine ⟨4058696237002266873182209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86585519722715026627887125 4058696237002266873182209)
                  ·
                    refine ⟨3044022177751700154886657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058696237002266873182209 3044022177751700154886657)
                    ·
                      refine ⟨2283016633313775116164993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044022177751700154886657 2283016633313775116164993)
                      ·
                        rfl

theorem cell23_4446159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 2, 2].length) (baseStart_4446159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446159 prefixEnd_4446159 := by exact prefixLift 4446159
  have htrace : WordTrace (prefixWord ++ tailWord_4446159) baseStart_4446159 baseEnd_4446159 := by
    simpa [prefixWord, tailWord_4446159, baseEnd_4446159] using wordTrace_append hprefix tailTrace_4446159
  have hstable : (prefixWord ++ tailWord_4446159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446159).length < 2 ^ (prefixWord ++ tailWord_4446159).sum := by decide
  have hdescent : baseEnd_4446159 < baseStart_4446159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446192 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_4446192 : Nat := 118140960795 + 4446192 * 2 ^ 59
def prefixEnd_4446192 : Nat := 4983230072969 + 3 ^ 40 * 4446192 * 2
def baseEnd_4446192 : Nat := 2283033578175373487052341

theorem tailTrace_4446192 : CollatzResearch.WordTrace tailWord_4446192 prefixEnd_4446192 2283033578175373487052341 := by
  unfold tailWord_4446192
  simp only [CollatzResearch.WordTrace]
  refine ⟨81082972354106603991918415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108110629805475471989224553 81082972354106603991918415)
  ·
    refine ⟨121624458531159905987877623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81082972354106603991918415 121624458531159905987877623)
    ·
      refine ⟨182436687796739858981816435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121624458531159905987877623 182436687796739858981816435)
      ·
        refine ⟨273655031695109788472724653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182436687796739858981816435 273655031695109788472724653)
        ·
          refine ⟨102620636885666170677271745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273655031695109788472724653 102620636885666170677271745)
          ·
            refine ⟨76965477664249628007953809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102620636885666170677271745 76965477664249628007953809)
            ·
              refine ⟨57724108248187221005965357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76965477664249628007953809 57724108248187221005965357)
              ·
                refine ⟨21646540593070207877237009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57724108248187221005965357 21646540593070207877237009)
                ·
                  refine ⟨16234905444802655907927757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21646540593070207877237009 16234905444802655907927757)
                  ·
                    refine ⟨6088089541800995965472909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16234905444802655907927757 6088089541800995965472909)
                    ·
                      refine ⟨2283033578175373487052341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088089541800995965472909 2283033578175373487052341)
                      ·
                        rfl

theorem cell23_4446192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_4446192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446192 prefixEnd_4446192 := by exact prefixLift 4446192
  have htrace : WordTrace (prefixWord ++ tailWord_4446192) baseStart_4446192 baseEnd_4446192 := by
    simpa [prefixWord, tailWord_4446192, baseEnd_4446192] using wordTrace_append hprefix tailTrace_4446192
  have hstable : (prefixWord ++ tailWord_4446192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446192).length < 2 ^ (prefixWord ++ tailWord_4446192).sum := by decide
  have hdescent : baseEnd_4446192 < baseStart_4446192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446193 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 2, 2, 2]
def baseStart_4446193 : Nat := 118140960795 + 4446193 * 2 ^ 59
def prefixEnd_4446193 : Nat := 4983230072969 + 3 ^ 40 * 4446193 * 2
def baseEnd_4446193 : Nat := 2283034091656027983139837

theorem tailTrace_4446193 : CollatzResearch.WordTrace tailWord_4446193 prefixEnd_4446193 2283034091656027983139837 := by
  unfold tailWord_4446193
  simp only [CollatzResearch.WordTrace]
  refine ⟨162165981181209585154623233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108110654120806390103082155 162165981181209585154623233)
  ·
    refine ⟨121624485885907188865967425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162165981181209585154623233 121624485885907188865967425)
    ·
      refine ⟨91218364414430391649475569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121624485885907188865967425 91218364414430391649475569)
      ·
        refine ⟨68413773310822793737106677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91218364414430391649475569 68413773310822793737106677)
        ·
          refine ⟨6413791247889636912853751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68413773310822793737106677 6413791247889636912853751)
          ·
            refine ⟨9620686871834455369280627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413791247889636912853751 9620686871834455369280627)
            ·
              refine ⟨14431030307751683053920941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9620686871834455369280627 14431030307751683053920941)
              ·
                refine ⟨5411636365406881145220353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14431030307751683053920941 5411636365406881145220353)
                ·
                  refine ⟨4058727274055160858915265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5411636365406881145220353 4058727274055160858915265)
                  ·
                    refine ⟨3044045455541370644186449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058727274055160858915265 3044045455541370644186449)
                    ·
                      refine ⟨2283034091656027983139837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044045455541370644186449 2283034091656027983139837)
                      ·
                        rfl

theorem cell23_4446193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_4446193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446193 prefixEnd_4446193 := by exact prefixLift 4446193
  have htrace : WordTrace (prefixWord ++ tailWord_4446193) baseStart_4446193 baseEnd_4446193 := by
    simpa [prefixWord, tailWord_4446193, baseEnd_4446193] using wordTrace_append hprefix tailTrace_4446193
  have hstable : (prefixWord ++ tailWord_4446193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446193).length < 2 ^ (prefixWord ++ tailWord_4446193).sum := by decide
  have hdescent : baseEnd_4446193 < baseStart_4446193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446195 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 3, 7]
def baseStart_4446195 : Nat := 118140960795 + 4446195 * 2 ^ 59
def prefixEnd_4446195 : Nat := 4983230072969 + 3 ^ 40 * 4446195 * 2
def baseEnd_4446195 : Nat := 761011706205778991771609

theorem tailTrace_4446195 : CollatzResearch.WordTrace tailWord_4446195 prefixEnd_4446195 761011706205778991771609 := by
  unfold tailWord_4446195
  simp only [CollatzResearch.WordTrace]
  refine ⟨162166054127202339496196039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108110702751468226330797359 162166054127202339496196039)
  ·
    refine ⟨243249081190803509244294059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162166054127202339496196039 243249081190803509244294059)
    ·
      refine ⟨364873621786205263866441089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243249081190803509244294059 364873621786205263866441089)
      ·
        refine ⟨273655216339653947899830817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364873621786205263866441089 273655216339653947899830817)
        ·
          refine ⟨205241412254740460924873113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273655216339653947899830817 205241412254740460924873113)
          ·
            refine ⟨153931059191055345693654835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205241412254740460924873113 153931059191055345693654835)
            ·
              refine ⟨230896588786583018540482253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153931059191055345693654835 230896588786583018540482253)
              ·
                refine ⟨86586220794968631952680845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230896588786583018540482253 86586220794968631952680845)
                ·
                  refine ⟨32469832798113236982255317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86586220794968631952680845 32469832798113236982255317)
                  ·
                    refine ⟨761011706205778991771609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32469832798113236982255317 761011706205778991771609)
                    ·
                      rfl

theorem cell23_4446195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_4446195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446195 prefixEnd_4446195 := by exact prefixLift 4446195
  have htrace : WordTrace (prefixWord ++ tailWord_4446195) baseStart_4446195 baseEnd_4446195 := by
    simpa [prefixWord, tailWord_4446195, baseEnd_4446195] using wordTrace_append hprefix tailTrace_4446195
  have hstable : (prefixWord ++ tailWord_4446195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446195).length < 2 ^ (prefixWord ++ tailWord_4446195).sum := by decide
  have hdescent : baseEnd_4446195 < baseStart_4446195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446222 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4446222 : Nat := 118140960795 + 4446222 * 2 ^ 59
def prefixEnd_4446222 : Nat := 4983230072969 + 3 ^ 40 * 4446222 * 2
def baseEnd_4446222 : Nat := 2283048982595008369677203

theorem tailTrace_4446222 : CollatzResearch.WordTrace tailWord_4446222 prefixEnd_4446222 2283048982595008369677203 := by
  unfold tailWord_4446222
  simp only [CollatzResearch.WordTrace]
  refine ⟨20270879862263065388428615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108111359265403015404952613 20270879862263065388428615)
  ·
    refine ⟨30406319793394598082642923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20270879862263065388428615 30406319793394598082642923)
    ·
      refine ⟨45609479690091897123964385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30406319793394598082642923 45609479690091897123964385)
      ·
        refine ⟨34207109767568922842973289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45609479690091897123964385 34207109767568922842973289)
        ·
          refine ⟨25655332325676692132229967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34207109767568922842973289 25655332325676692132229967)
          ·
            refine ⟨38482998488515038198344951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25655332325676692132229967 38482998488515038198344951)
            ·
              refine ⟨57724497732772557297517427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38482998488515038198344951 57724497732772557297517427)
              ·
                refine ⟨86586746599158835946276141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57724497732772557297517427 86586746599158835946276141)
                ·
                  refine ⟨32470029974684563479853553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86586746599158835946276141 32470029974684563479853553)
                  ·
                    refine ⟨24352522481013422609890165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32470029974684563479853553 24352522481013422609890165)
                    ·
                      refine ⟨2283048982595008369677203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24352522481013422609890165 2283048982595008369677203)
                      ·
                        rfl

theorem cell23_4446222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4446222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446222 prefixEnd_4446222 := by exact prefixLift 4446222
  have htrace : WordTrace (prefixWord ++ tailWord_4446222) baseStart_4446222 baseEnd_4446222 := by
    simpa [prefixWord, tailWord_4446222, baseEnd_4446222] using wordTrace_append hprefix tailTrace_4446222
  have hstable : (prefixWord ++ tailWord_4446222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446222).length < 2 ^ (prefixWord ++ tailWord_4446222).sum := by decide
  have hdescent : baseEnd_4446222 < baseStart_4446222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446269 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4446269 : Nat := 118140960795 + 4446269 * 2 ^ 59
def prefixEnd_4446269 : Nat := 4983230072969 + 3 ^ 40 * 4446269 * 2
def baseEnd_4446269 : Nat := 2283073116185769685789487

theorem tailTrace_4446269 : CollatzResearch.WordTrace tailWord_4446269 prefixEnd_4446269 2283073116185769685789487 := by
  unfold tailWord_4446269
  simp only [CollatzResearch.WordTrace]
  refine ⟨162168753128934250134389861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108112502085956166756259907 162168753128934250134389861)
  ·
    refine ⟨30406641211675171900198099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162168753128934250134389861 30406641211675171900198099)
    ·
      refine ⟨45609961817512757850297149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30406641211675171900198099 45609961817512757850297149)
      ·
        refine ⟨17103735681567284193861431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45609961817512757850297149 17103735681567284193861431)
        ·
          refine ⟨25655603522350926290792147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17103735681567284193861431 25655603522350926290792147)
          ·
            refine ⟨38483405283526389436188221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25655603522350926290792147 38483405283526389436188221)
            ·
              refine ⟨14431276981322396038570583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38483405283526389436188221 14431276981322396038570583)
              ·
                refine ⟨21646915471983594057855875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14431276981322396038570583 21646915471983594057855875)
                ·
                  refine ⟨32470373207975391086783813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21646915471983594057855875 32470373207975391086783813)
                  ·
                    refine ⟨6088194976495385828771965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32470373207975391086783813 6088194976495385828771965)
                    ·
                      refine ⟨2283073116185769685789487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088194976495385828771965 2283073116185769685789487)
                      ·
                        rfl

theorem cell23_4446269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4446269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446269 prefixEnd_4446269 := by exact prefixLift 4446269
  have htrace : WordTrace (prefixWord ++ tailWord_4446269) baseStart_4446269 baseEnd_4446269 := by
    simpa [prefixWord, tailWord_4446269, baseEnd_4446269] using wordTrace_append hprefix tailTrace_4446269
  have hstable : (prefixWord ++ tailWord_4446269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446269).length < 2 ^ (prefixWord ++ tailWord_4446269).sum := by decide
  have hdescent : baseEnd_4446269 < baseStart_4446269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446316 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_4446316 : Nat := 118140960795 + 4446316 * 2 ^ 59
def prefixEnd_4446316 : Nat := 4983230072969 + 3 ^ 40 * 4446316 * 2
def baseEnd_4446316 : Nat := 2283097249776531001901771

theorem tailTrace_4446316 : CollatzResearch.WordTrace tailWord_4446316 prefixEnd_4446316 2283097249776531001901771 := by
  unfold tailWord_4446316
  simp only [CollatzResearch.WordTrace]
  refine ⟨81085233679881988580675401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108113644906509318107567201 81085233679881988580675401)
  ·
    refine ⟨60813925259911491435506551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81085233679881988580675401 60813925259911491435506551)
    ·
      refine ⟨91220887889867237153259827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60813925259911491435506551 91220887889867237153259827)
      ·
        refine ⟨136831331834800855729889741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91220887889867237153259827 136831331834800855729889741)
        ·
          refine ⟨51311749438050320898708653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136831331834800855729889741 51311749438050320898708653)
          ·
            refine ⟨19241906039268870337015745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51311749438050320898708653 19241906039268870337015745)
            ·
              refine ⟨14431429529451652752761809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19241906039268870337015745 14431429529451652752761809)
              ·
                refine ⟨10823572147088739564571357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14431429529451652752761809 10823572147088739564571357)
                ·
                  refine ⟨4058839555158277336714259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10823572147088739564571357 4058839555158277336714259)
                  ·
                    refine ⟨6088259332737416005071389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058839555158277336714259 6088259332737416005071389)
                    ·
                      refine ⟨2283097249776531001901771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088259332737416005071389 2283097249776531001901771)
                      ·
                        rfl

theorem cell23_4446316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_4446316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446316 prefixEnd_4446316 := by exact prefixLift 4446316
  have htrace : WordTrace (prefixWord ++ tailWord_4446316) baseStart_4446316 baseEnd_4446316 := by
    simpa [prefixWord, tailWord_4446316, baseEnd_4446316] using wordTrace_append hprefix tailTrace_4446316
  have hstable : (prefixWord ++ tailWord_4446316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446316).length < 2 ^ (prefixWord ++ tailWord_4446316).sum := by decide
  have hdescent : baseEnd_4446316 < baseStart_4446316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446319 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 1, 5]
def baseStart_4446319 : Nat := 118140960795 + 4446319 * 2 ^ 59
def prefixEnd_4446319 : Nat := 4983230072969 + 3 ^ 40 * 4446319 * 2
def baseEnd_4446319 : Nat := 761032930072831496721419

theorem tailTrace_4446319 : CollatzResearch.WordTrace tailWord_4446319 prefixEnd_4446319 761032930072831496721419 := by
  unfold tailWord_4446319
  simp only [CollatzResearch.WordTrace]
  refine ⟨162170576778753108673710011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108113717852502072449140007 162170576778753108673710011)
  ·
    refine ⟨243255865168129663010565017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162170576778753108673710011 243255865168129663010565017)
    ·
      refine ⟨182441898876097247257923763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243255865168129663010565017 182441898876097247257923763)
      ·
        refine ⟨273662848314145870886885645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182441898876097247257923763 273662848314145870886885645)
        ·
          refine ⟨102623568117804701582582117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273662848314145870886885645 102623568117804701582582117)
          ·
            refine ⟨19241919022088381546734147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102623568117804701582582117 19241919022088381546734147)
            ·
              refine ⟨28862878533132572320101221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19241919022088381546734147 28862878533132572320101221)
              ·
                refine ⟨5411789724962357310018979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28862878533132572320101221 5411789724962357310018979)
                ·
                  refine ⟨8117684587443535965028469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411789724962357310018979 8117684587443535965028469)
                  ·
                    refine ⟨761032930072831496721419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8117684587443535965028469 761032930072831496721419)
                    ·
                      rfl

theorem cell23_4446319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_4446319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446319 prefixEnd_4446319 := by exact prefixLift 4446319
  have htrace : WordTrace (prefixWord ++ tailWord_4446319) baseStart_4446319 baseEnd_4446319 := by
    simpa [prefixWord, tailWord_4446319, baseEnd_4446319] using wordTrace_append hprefix tailTrace_4446319
  have hstable : (prefixWord ++ tailWord_4446319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446319).length < 2 ^ (prefixWord ++ tailWord_4446319).sum := by decide
  have hdescent : baseEnd_4446319 < baseStart_4446319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446350 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4446350 : Nat := 118140960795 + 4446350 * 2 ^ 59
def prefixEnd_4446350 : Nat := 4983230072969 + 3 ^ 40 * 4446350 * 2
def baseEnd_4446350 : Nat := 2283114708118783868876615

theorem tailTrace_4446350 : CollatzResearch.WordTrace tailWord_4446350 prefixEnd_4446350 2283114708118783868876615 := by
  unfold tailWord_4446350
  simp only [CollatzResearch.WordTrace]
  refine ⟨20271463430205100121011063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108114471627760533978725669 20271463430205100121011063)
  ·
    refine ⟨30407195145307650181516595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20271463430205100121011063 30407195145307650181516595)
    ·
      refine ⟨45610792717961475272274893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30407195145307650181516595 45610792717961475272274893)
      ·
        refine ⟨17104047269235553227103085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45610792717961475272274893 17104047269235553227103085)
        ·
          refine ⟨6414017725963332460163657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17104047269235553227103085 6414017725963332460163657)
          ·
            refine ⟨4810513294472499345122743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6414017725963332460163657 4810513294472499345122743)
            ·
              refine ⟨7215769941708749017684115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810513294472499345122743 7215769941708749017684115)
              ·
                refine ⟨10823654912563123526526173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7215769941708749017684115 10823654912563123526526173)
                ·
                  refine ⟨4058870592211171322447315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10823654912563123526526173 4058870592211171322447315)
                  ·
                    refine ⟨6088305888316756983670973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058870592211171322447315 6088305888316756983670973)
                    ·
                      refine ⟨2283114708118783868876615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088305888316756983670973 2283114708118783868876615)
                      ·
                        rfl

theorem cell23_4446350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4446350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446350 prefixEnd_4446350 := by exact prefixLift 4446350
  have htrace : WordTrace (prefixWord ++ tailWord_4446350) baseStart_4446350 baseEnd_4446350 := by
    simpa [prefixWord, tailWord_4446350, baseEnd_4446350] using wordTrace_append hprefix tailTrace_4446350
  have hstable : (prefixWord ++ tailWord_4446350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446350).length < 2 ^ (prefixWord ++ tailWord_4446350).sum := by decide
  have hdescent : baseEnd_4446350 < baseStart_4446350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446352 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_4446352 : Nat := 118140960795 + 4446352 * 2 ^ 59
def prefixEnd_4446352 : Nat := 4983230072969 + 3 ^ 40 * 4446352 * 2
def baseEnd_4446352 : Nat := 2283115735080092861051605

theorem tailTrace_4446352 : CollatzResearch.WordTrace tailWord_4446352 prefixEnd_4446352 2283115735080092861051605 := by
  unfold tailWord_4446352
  simp only [CollatzResearch.WordTrace]
  refine ⟨81085890193816777654830655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108114520258422370206440873 81085890193816777654830655)
  ·
    refine ⟨121628835290725166482245983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81085890193816777654830655 121628835290725166482245983)
    ·
      refine ⟨182443252936087749723368975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121628835290725166482245983 182443252936087749723368975)
      ·
        refine ⟨273664879404131624585053463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182443252936087749723368975 273664879404131624585053463)
        ·
          refine ⟨410497319106197436877580195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273664879404131624585053463 410497319106197436877580195)
          ·
            refine ⟨615745978659296155316370293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410497319106197436877580195 615745978659296155316370293)
            ·
              refine ⟨57726185499309014560909715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 615745978659296155316370293 57726185499309014560909715)
              ·
                refine ⟨86589278248963521841364573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57726185499309014560909715 86589278248963521841364573)
                ·
                  refine ⟨32470979343361320690511715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86589278248963521841364573 32470979343361320690511715)
                  ·
                    refine ⟨48706469015041981035767573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32470979343361320690511715 48706469015041981035767573)
                    ·
                      refine ⟨2283115735080092861051605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48706469015041981035767573 2283115735080092861051605)
                      ·
                        rfl

theorem cell23_4446352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_4446352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446352 prefixEnd_4446352 := by exact prefixLift 4446352
  have htrace : WordTrace (prefixWord ++ tailWord_4446352) baseStart_4446352 baseEnd_4446352 := by
    simpa [prefixWord, tailWord_4446352, baseEnd_4446352] using wordTrace_append hprefix tailTrace_4446352
  have hstable : (prefixWord ++ tailWord_4446352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446352).length < 2 ^ (prefixWord ++ tailWord_4446352).sum := by decide
  have hdescent : baseEnd_4446352 < baseStart_4446352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446369 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4446369 : Nat := 118140960795 + 4446369 * 2 ^ 59
def prefixEnd_4446369 : Nat := 4983230072969 + 3 ^ 40 * 4446369 * 2
def baseEnd_4446369 : Nat := 2283124464251219294539027

theorem tailTrace_4446369 : CollatzResearch.WordTrace tailWord_4446369 prefixEnd_4446369 2283124464251219294539027 := by
  unfold tailWord_4446369
  simp only [CollatzResearch.WordTrace]
  refine ⟨162172400428571967213030161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108114933619047978142020107 162172400428571967213030161)
  ·
    refine ⟨121629300321428975409772621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162172400428571967213030161 121629300321428975409772621)
    ·
      refine ⟨45610987620535865778664733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121629300321428975409772621 45610987620535865778664733)
      ·
        refine ⟨17104120357700949666999275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45610987620535865778664733 17104120357700949666999275)
        ·
          refine ⟨25656180536551424500498913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17104120357700949666999275 25656180536551424500498913)
          ·
            refine ⟨19242135402413568375374185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25656180536551424500498913 19242135402413568375374185)
            ·
              refine ⟨14431601551810176281530639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19242135402413568375374185 14431601551810176281530639)
              ·
                refine ⟨21647402327715264422295959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14431601551810176281530639 21647402327715264422295959)
                ·
                  refine ⟨32471103491572896633443939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21647402327715264422295959 32471103491572896633443939)
                  ·
                    refine ⟨48706655237359344950165909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32471103491572896633443939 48706655237359344950165909)
                    ·
                      refine ⟨2283124464251219294539027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48706655237359344950165909 2283124464251219294539027)
                      ·
                        rfl

theorem cell23_4446369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4446369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446369 prefixEnd_4446369 := by exact prefixLift 4446369
  have htrace : WordTrace (prefixWord ++ tailWord_4446369) baseStart_4446369 baseEnd_4446369 := by
    simpa [prefixWord, tailWord_4446369, baseEnd_4446369] using wordTrace_append hprefix tailTrace_4446369
  have hstable : (prefixWord ++ tailWord_4446369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446369).length < 2 ^ (prefixWord ++ tailWord_4446369).sum := by decide
  have hdescent : baseEnd_4446369 < baseStart_4446369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446393 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4446393 : Nat := 118140960795 + 4446393 * 2 ^ 59
def prefixEnd_4446393 : Nat := 4983230072969 + 3 ^ 40 * 4446393 * 2
def baseEnd_4446393 : Nat := 2283136787786927200638917

theorem tailTrace_4446393 : CollatzResearch.WordTrace tailWord_4446393 prefixEnd_4446393 2283136787786927200638917 := by
  unfold tailWord_4446393
  simp only [CollatzResearch.WordTrace]
  refine ⟨162173275780485019311903833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108115517186990012874602555 162173275780485019311903833)
  ·
    refine ⟨121629956835363764483927875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162173275780485019311903833 121629956835363764483927875)
    ·
      refine ⟨182444935253045646725891813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121629956835363764483927875 182444935253045646725891813)
      ·
        refine ⟨34208425359946058761104715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182444935253045646725891813 34208425359946058761104715)
        ·
          refine ⟨51312638039919088141657073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34208425359946058761104715 51312638039919088141657073)
          ·
            refine ⟨38484478529939316106242805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51312638039919088141657073 38484478529939316106242805)
            ·
              refine ⟨3607919862181810884960263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38484478529939316106242805 3607919862181810884960263)
              ·
                refine ⟨5411879793272716327440395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607919862181810884960263 5411879793272716327440395)
                ·
                  refine ⟨8117819689909074491160593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411879793272716327440395 8117819689909074491160593)
                  ·
                    refine ⟨6088364767431805868370445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8117819689909074491160593 6088364767431805868370445)
                    ·
                      refine ⟨2283136787786927200638917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088364767431805868370445 2283136787786927200638917)
                      ·
                        rfl

theorem cell23_4446393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4446393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446393 prefixEnd_4446393 := by exact prefixLift 4446393
  have htrace : WordTrace (prefixWord ++ tailWord_4446393) baseStart_4446393 baseEnd_4446393 := by
    simpa [prefixWord, tailWord_4446393, baseEnd_4446393] using wordTrace_append hprefix tailTrace_4446393
  have hstable : (prefixWord ++ tailWord_4446393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446393).length < 2 ^ (prefixWord ++ tailWord_4446393).sum := by decide
  have hdescent : baseEnd_4446393 < baseStart_4446393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446401 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4446401 : Nat := 118140960795 + 4446401 * 2 ^ 59
def prefixEnd_4446401 : Nat := 4983230072969 + 3 ^ 40 * 4446401 * 2
def baseEnd_4446401 : Nat := 2283140895632163169338881

theorem tailTrace_4446401 : CollatzResearch.WordTrace tailWord_4446401 prefixEnd_4446401 2283140895632163169338881 := by
  unfold tailWord_4446401
  simp only [CollatzResearch.WordTrace]
  refine ⟨162173567564456036678195057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108115711709637357785463371 162173567564456036678195057)
  ·
    refine ⟨121630175673342027508646293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162173567564456036678195057 121630175673342027508646293)
    ·
      refine ⟨5701414484687907539467795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121630175673342027508646293 5701414484687907539467795)
      ·
        refine ⟨8552121727031861309201693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701414484687907539467795 8552121727031861309201693)
        ·
          refine ⟨3207045647636947990950635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8552121727031861309201693 3207045647636947990950635)
          ·
            refine ⟨4810568471455421986425953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207045647636947990950635 4810568471455421986425953)
            ·
              refine ⟨3607926353591566489819465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810568471455421986425953 3607926353591566489819465)
              ·
                refine ⟨2705944765193674867364599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3607926353591566489819465 2705944765193674867364599)
                ·
                  refine ⟨4058917147790512301046899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705944765193674867364599 4058917147790512301046899)
                  ·
                    refine ⟨6088375721685768451570349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058917147790512301046899 6088375721685768451570349)
                    ·
                      refine ⟨2283140895632163169338881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088375721685768451570349 2283140895632163169338881)
                      ·
                        rfl

theorem cell23_4446401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4446401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446401 prefixEnd_4446401 := by exact prefixLift 4446401
  have htrace : WordTrace (prefixWord ++ tailWord_4446401) baseStart_4446401 baseEnd_4446401 := by
    simpa [prefixWord, tailWord_4446401, baseEnd_4446401] using wordTrace_append hprefix tailTrace_4446401
  have hstable : (prefixWord ++ tailWord_4446401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446401).length < 2 ^ (prefixWord ++ tailWord_4446401).sum := by decide
  have hdescent : baseEnd_4446401 < baseStart_4446401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446433 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_4446433 : Nat := 118140960795 + 4446433 * 2 ^ 59
def prefixEnd_4446433 : Nat := 4983230072969 + 3 ^ 40 * 4446433 * 2
def baseEnd_4446433 : Nat := 2283157327013107044138733

theorem tailTrace_4446433 : CollatzResearch.WordTrace tailWord_4446433 prefixEnd_4446433 2283157327013107044138733 := by
  unfold tailWord_4446433
  simp only [CollatzResearch.WordTrace]
  refine ⟨162174734700340106143359953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108116489800226737428906635 162174734700340106143359953)
  ·
    refine ⟨121631051025255079607519965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162174734700340106143359953 121631051025255079607519965)
    ·
      refine ⟨45611644134470654852819987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121631051025255079607519965 45611644134470654852819987)
      ·
        refine ⟨68417466201705982279229981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45611644134470654852819987 68417466201705982279229981)
        ·
          refine ⟨25656549825639743354711243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68417466201705982279229981 25656549825639743354711243)
          ·
            refine ⟨38484824738459615032066865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25656549825639743354711243 38484824738459615032066865)
            ·
              refine ⟨28863618553844711274050149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38484824738459615032066865 28863618553844711274050149)
              ·
                refine ⟨5411928478845883363884403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28863618553844711274050149 5411928478845883363884403)
                ·
                  refine ⟨8117892718268825045826605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411928478845883363884403 8117892718268825045826605)
                  ·
                    refine ⟨3044209769350809392184977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8117892718268825045826605 3044209769350809392184977)
                    ·
                      refine ⟨2283157327013107044138733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044209769350809392184977 2283157327013107044138733)
                      ·
                        rfl

theorem cell23_4446433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_4446433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446433 prefixEnd_4446433 := by exact prefixLift 4446433
  have htrace : WordTrace (prefixWord ++ tailWord_4446433) baseStart_4446433 baseEnd_4446433 := by
    simpa [prefixWord, tailWord_4446433, baseEnd_4446433] using wordTrace_append hprefix tailTrace_4446433
  have hstable : (prefixWord ++ tailWord_4446433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446433).length < 2 ^ (prefixWord ++ tailWord_4446433).sum := by decide
  have hdescent : baseEnd_4446433 < baseStart_4446433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446449 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_4446449 : Nat := 118140960795 + 4446449 * 2 ^ 59
def prefixEnd_4446449 : Nat := 4983230072969 + 3 ^ 40 * 4446449 * 2
def baseEnd_4446449 : Nat := 2283165542703578981538659

theorem tailTrace_4446449 : CollatzResearch.WordTrace tailWord_4446449 prefixEnd_4446449 2283165542703578981538659 := by
  unfold tailWord_4446449
  simp only [CollatzResearch.WordTrace]
  refine ⟨162175318268282140875942401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108116878845521427250628267 162175318268282140875942401)
  ·
    refine ⟨121631488701211605656956801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162175318268282140875942401 121631488701211605656956801)
    ·
      refine ⟨91223616525908704242717601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121631488701211605656956801 91223616525908704242717601)
      ·
        refine ⟨68417712394431528182038201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91223616525908704242717601 68417712394431528182038201)
        ·
          refine ⟨51313284295823646136528651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68417712394431528182038201 51313284295823646136528651)
          ·
            refine ⟨76969926443735469204792977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51313284295823646136528651 76969926443735469204792977)
            ·
              refine ⟨57727444832801601903594733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76969926443735469204792977 57727444832801601903594733)
              ·
                refine ⟨21647791812300600713848025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57727444832801601903594733 21647791812300600713848025)
                ·
                  refine ⟨16235843859225450535386019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21647791812300600713848025 16235843859225450535386019)
                  ·
                    refine ⟨24353765788838175803079029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16235843859225450535386019 24353765788838175803079029)
                    ·
                      refine ⟨2283165542703578981538659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24353765788838175803079029 2283165542703578981538659)
                      ·
                        rfl

theorem cell23_4446449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_4446449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446449 prefixEnd_4446449 := by exact prefixLift 4446449
  have htrace : WordTrace (prefixWord ++ tailWord_4446449) baseStart_4446449 baseEnd_4446449 := by
    simpa [prefixWord, tailWord_4446449, baseEnd_4446449] using wordTrace_append hprefix tailTrace_4446449
  have hstable : (prefixWord ++ tailWord_4446449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446449).length < 2 ^ (prefixWord ++ tailWord_4446449).sum := by decide
  have hdescent : baseEnd_4446449 < baseStart_4446449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446450 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4446450 : Nat := 118140960795 + 4446450 * 2 ^ 59
def prefixEnd_4446450 : Nat := 4983230072969 + 3 ^ 40 * 4446450 * 2
def baseEnd_4446450 : Nat := 2283166056184233477626155

theorem tailTrace_4446450 : CollatzResearch.WordTrace tailWord_4446450 prefixEnd_4446450 2283166056184233477626155 := by
  unfold tailWord_4446450
  simp only [CollatzResearch.WordTrace]
  refine ⟨40543838685319629511682201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108116903160852345364485869 40543838685319629511682201)
  ·
    refine ⟨30407879013989722133761651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40543838685319629511682201 30407879013989722133761651)
    ·
      refine ⟨45611818520984583200642477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30407879013989722133761651 45611818520984583200642477)
      ·
        refine ⟨17104431945369218700240929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45611818520984583200642477 17104431945369218700240929)
        ·
          refine ⟨12828323959026914025180697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17104431945369218700240929 12828323959026914025180697)
          ·
            refine ⟨9621242969270185518885523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12828323959026914025180697 9621242969270185518885523)
            ·
              refine ⟨14431864453905278278328285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9621242969270185518885523 14431864453905278278328285)
              ·
                refine ⟨5411949170214479354373107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14431864453905278278328285 5411949170214479354373107)
                ·
                  refine ⟨8117923755321719031559661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411949170214479354373107 8117923755321719031559661)
                  ·
                    refine ⟨3044221408245644636834873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8117923755321719031559661 3044221408245644636834873)
                    ·
                      refine ⟨2283166056184233477626155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044221408245644636834873 2283166056184233477626155)
                      ·
                        rfl

theorem cell23_4446450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4446450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446450 prefixEnd_4446450 := by exact prefixLift 4446450
  have htrace : WordTrace (prefixWord ++ tailWord_4446450) baseStart_4446450 baseEnd_4446450 := by
    simpa [prefixWord, tailWord_4446450, baseEnd_4446450] using wordTrace_append hprefix tailTrace_4446450
  have hstable : (prefixWord ++ tailWord_4446450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446450).length < 2 ^ (prefixWord ++ tailWord_4446450).sum := by decide
  have hdescent : baseEnd_4446450 < baseStart_4446450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446463 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 4, 2, 2]
def baseStart_4446463 : Nat := 118140960795 + 4446463 * 2 ^ 59
def prefixEnd_4446463 : Nat := 4983230072969 + 3 ^ 40 * 4446463 * 2
def baseEnd_4446463 : Nat := 2283172731432741926763595

theorem tailTrace_4446463 : CollatzResearch.WordTrace tailWord_4446463 prefixEnd_4446463 2283172731432741926763595 := by
  unfold tailWord_4446463
  simp only [CollatzResearch.WordTrace]
  refine ⟨162175828890231421266952043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108117219260154280844634695 162175828890231421266952043)
  ·
    refine ⟨243263743335347131900428065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162175828890231421266952043 243263743335347131900428065)
    ·
      refine ⟨182447807501510348925321049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243263743335347131900428065 182447807501510348925321049)
      ·
        refine ⟨136835855626132761693990787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182447807501510348925321049 136835855626132761693990787)
        ·
          refine ⟨205253783439199142540986181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136835855626132761693990787 205253783439199142540986181)
          ·
            refine ⟨38485084394849839226434909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205253783439199142540986181 38485084394849839226434909)
            ·
              refine ⟨14431906648068689709913091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38485084394849839226434909 14431906648068689709913091)
              ·
                refine ⟨21647859972103034564869637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14431906648068689709913091 21647859972103034564869637)
                ·
                  refine ⟨4058973744769318980913057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21647859972103034564869637 4058973744769318980913057)
                  ·
                    refine ⟨3044230308576989235684793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058973744769318980913057 3044230308576989235684793)
                    ·
                      refine ⟨2283172731432741926763595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044230308576989235684793 2283172731432741926763595)
                      ·
                        rfl

theorem cell23_4446463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_4446463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446463 prefixEnd_4446463 := by exact prefixLift 4446463
  have htrace : WordTrace (prefixWord ++ tailWord_4446463) baseStart_4446463 baseEnd_4446463 := by
    simpa [prefixWord, tailWord_4446463, baseEnd_4446463] using wordTrace_append hprefix tailTrace_4446463
  have hstable : (prefixWord ++ tailWord_4446463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446463).length < 2 ^ (prefixWord ++ tailWord_4446463).sum := by decide
  have hdescent : baseEnd_4446463 < baseStart_4446463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446499 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 1, 7]
def baseStart_4446499 : Nat := 118140960795 + 4446499 * 2 ^ 59
def prefixEnd_4446499 : Nat := 4983230072969 + 3 ^ 40 * 4446499 * 2
def baseEnd_4446499 : Nat := 761063738912101261971143

theorem tailTrace_4446499 : CollatzResearch.WordTrace tailWord_4446499 prefixEnd_4446499 761063738912101261971143 := by
  unfold tailWord_4446499
  simp only [CollatzResearch.WordTrace]
  refine ⟨162177141918100999415262551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108118094612067332943508367 162177141918100999415262551)
  ·
    refine ⟨243265712877151499122893827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162177141918100999415262551 243265712877151499122893827)
    ·
      refine ⟨364898569315727248684340741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243265712877151499122893827 364898569315727248684340741)
      ·
        refine ⟨68418481746698859128313889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 364898569315727248684340741 68418481746698859128313889)
        ·
          refine ⟨51313861310024144346235417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68418481746698859128313889 51313861310024144346235417)
          ·
            refine ⟨38485395982518108259676563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51313861310024144346235417 38485395982518108259676563)
            ·
              refine ⟨57728093973777162389514845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38485395982518108259676563 57728093973777162389514845)
              ·
                refine ⟨21648035240166435896068067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57728093973777162389514845 21648035240166435896068067)
                ·
                  refine ⟨32472052860249653844102101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21648035240166435896068067 32472052860249653844102101)
                  ·
                    refine ⟨761063738912101261971143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32472052860249653844102101 761063738912101261971143)
                    ·
                      rfl

theorem cell23_4446499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 7].length) (baseStart_4446499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446499 prefixEnd_4446499 := by exact prefixLift 4446499
  have htrace : WordTrace (prefixWord ++ tailWord_4446499) baseStart_4446499 baseEnd_4446499 := by
    simpa [prefixWord, tailWord_4446499, baseEnd_4446499] using wordTrace_append hprefix tailTrace_4446499
  have hstable : (prefixWord ++ tailWord_4446499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446499).length < 2 ^ (prefixWord ++ tailWord_4446499).sum := by decide
  have hdescent : baseEnd_4446499 < baseStart_4446499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446526 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4446526 : Nat := 118140960795 + 4446526 * 2 ^ 59
def prefixEnd_4446526 : Nat := 4983230072969 + 3 ^ 40 * 4446526 * 2
def baseEnd_4446526 : Nat := 2283205080713975180275805

theorem tailTrace_4446526 : CollatzResearch.WordTrace tailWord_4446526 prefixEnd_4446526 2283205080713975180275805 := by
  unfold tailWord_4446526
  simp only [CollatzResearch.WordTrace]
  refine ⟨20272265836125397878311929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108118751126002122017663621 20272265836125397878311929)
  ·
    refine ⟨15204199377094048408733947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20272265836125397878311929 15204199377094048408733947)
    ·
      refine ⟨22806299065641072613100921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15204199377094048408733947 22806299065641072613100921)
      ·
        refine ⟨17104724299230804459825691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22806299065641072613100921 17104724299230804459825691)
        ·
          refine ⟨25657086448846206689738537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17104724299230804459825691 25657086448846206689738537)
          ·
            refine ⟨19242814836634655017303903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25657086448846206689738537 19242814836634655017303903)
            ·
              refine ⟨28864222254951982525955855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19242814836634655017303903 28864222254951982525955855)
              ·
                refine ⟨43296333382427973788933783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28864222254951982525955855 43296333382427973788933783)
                ·
                  refine ⟨64944500073641960683400675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43296333382427973788933783 64944500073641960683400675)
                  ·
                    refine ⟨97416750110462941025101013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64944500073641960683400675 97416750110462941025101013)
                    ·
                      refine ⟨2283205080713975180275805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97416750110462941025101013 2283205080713975180275805)
                      ·
                        rfl

theorem cell23_4446526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4446526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446526 prefixEnd_4446526 := by exact prefixLift 4446526
  have htrace : WordTrace (prefixWord ++ tailWord_4446526) baseStart_4446526 baseEnd_4446526 := by
    simpa [prefixWord, tailWord_4446526, baseEnd_4446526] using wordTrace_append hprefix tailTrace_4446526
  have hstable : (prefixWord ++ tailWord_4446526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446526).length < 2 ^ (prefixWord ++ tailWord_4446526).sum := by decide
  have hdescent : baseEnd_4446526 < baseStart_4446526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446559 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 10]
def baseStart_4446559 : Nat := 118140960795 + 4446559 * 2 ^ 59
def prefixEnd_4446559 : Nat := 4983230072969 + 3 ^ 40 * 4446559 * 2
def baseEnd_4446559 : Nat := 253691336175063727907017

theorem tailTrace_4446559 : CollatzResearch.WordTrace tailWord_4446559 prefixEnd_4446559 253691336175063727907017 := by
  unfold tailWord_4446559
  simp only [CollatzResearch.WordTrace]
  refine ⟨162179330297883629662446731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108119553531922419774964487 162179330297883629662446731)
  ·
    refine ⟨243268995446825444493670097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162179330297883629662446731 243268995446825444493670097)
    ·
      refine ⟨182451746585119083370252573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243268995446825444493670097 182451746585119083370252573)
      ·
        refine ⟨68419404969419656263844715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182451746585119083370252573 68419404969419656263844715)
        ·
          refine ⟨102629107454129484395767073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68419404969419656263844715 102629107454129484395767073)
          ·
            refine ⟨76971830590597113296825305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102629107454129484395767073 76971830590597113296825305)
            ·
              refine ⟨57728872942947834972618979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76971830590597113296825305 57728872942947834972618979)
              ·
                refine ⟨86593309414421752458928469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57728872942947834972618979 86593309414421752458928469)
                ·
                  refine ⟨253691336175063727907017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 86593309414421752458928469 253691336175063727907017)
                  ·
                    rfl

theorem cell23_4446559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 10].length) (baseStart_4446559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446559 prefixEnd_4446559 := by exact prefixLift 4446559
  have htrace : WordTrace (prefixWord ++ tailWord_4446559) baseStart_4446559 baseEnd_4446559 := by
    simpa [prefixWord, tailWord_4446559, baseEnd_4446559] using wordTrace_append hprefix tailTrace_4446559
  have hstable : (prefixWord ++ tailWord_4446559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446559).length < 2 ^ (prefixWord ++ tailWord_4446559).sum := by decide
  have hdescent : baseEnd_4446559 < baseStart_4446559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446573 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4446573 : Nat := 118140960795 + 4446573 * 2 ^ 59
def prefixEnd_4446573 : Nat := 4983230072969 + 3 ^ 40 * 4446573 * 2
def baseEnd_4446573 : Nat := 2283229214304736496388089

theorem tailTrace_4446573 : CollatzResearch.WordTrace tailWord_4446573 prefixEnd_4446573 2283229214304736496388089 := by
  unfold tailWord_4446573
  simp only [CollatzResearch.WordTrace]
  refine ⟨162179840919832910053456373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108119893946555273368970915 162179840919832910053456373)
  ·
    refine ⟨15204360086234335317511535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162179840919832910053456373 15204360086234335317511535)
    ·
      refine ⟨22806540129351502976267303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15204360086234335317511535 22806540129351502976267303)
      ·
        refine ⟨34209810194027254464400955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22806540129351502976267303 34209810194027254464400955)
        ·
          refine ⟨51314715291040881696601433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34209810194027254464400955 51314715291040881696601433)
          ·
            refine ⟨38486036468280661272451075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51314715291040881696601433 38486036468280661272451075)
            ·
              refine ⟨57729054702420991908676613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38486036468280661272451075 57729054702420991908676613)
              ·
                refine ⟨10824197756703935982876865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57729054702420991908676613 10824197756703935982876865)
                ·
                  refine ⟨8118148317527951987157649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10824197756703935982876865 8118148317527951987157649)
                  ·
                    refine ⟨6088611238145963990368237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8118148317527951987157649 6088611238145963990368237)
                    ·
                      refine ⟨2283229214304736496388089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088611238145963990368237 2283229214304736496388089)
                      ·
                        rfl

theorem cell23_4446573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4446573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446573 prefixEnd_4446573 := by exact prefixLift 4446573
  have htrace : WordTrace (prefixWord ++ tailWord_4446573) baseStart_4446573 baseEnd_4446573 := by
    simpa [prefixWord, tailWord_4446573, baseEnd_4446573] using wordTrace_append hprefix tailTrace_4446573
  have hstable : (prefixWord ++ tailWord_4446573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446573).length < 2 ^ (prefixWord ++ tailWord_4446573).sum := by decide
  have hdescent : baseEnd_4446573 < baseStart_4446573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446576 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 6]
def baseStart_4446576 : Nat := 118140960795 + 4446576 * 2 ^ 59
def prefixEnd_4446576 : Nat := 4983230072969 + 3 ^ 40 * 4446576 * 2
def baseEnd_4446576 : Nat := 253692306082966664961175

theorem tailTrace_4446576 : CollatzResearch.WordTrace tailWord_4446576 prefixEnd_4446576 253692306082966664961175 := by
  unfold tailWord_4446576
  simp only [CollatzResearch.WordTrace]
  refine ⟨81089975169411020782907791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108119966892548027710543721 81089975169411020782907791)
  ·
    refine ⟨121634962754116531174361687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81089975169411020782907791 121634962754116531174361687)
    ·
      refine ⟨182452444131174796761542531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121634962754116531174361687 182452444131174796761542531)
      ·
        refine ⟨273678666196762195142313797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182452444131174796761542531 273678666196762195142313797)
        ·
          refine ⟨51314749911892911589183837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273678666196762195142313797 51314749911892911589183837)
          ·
            refine ⟨19243031216959841845943939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51314749911892911589183837 19243031216959841845943939)
            ·
              refine ⟨28864546825439762768915909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19243031216959841845943939 28864546825439762768915909)
              ·
                refine ⟨5412102529769955519171733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28864546825439762768915909 5412102529769955519171733)
                ·
                  refine ⟨253692306082966664961175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5412102529769955519171733 253692306082966664961175)
                  ·
                    rfl

theorem cell23_4446576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_4446576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446576 prefixEnd_4446576 := by exact prefixLift 4446576
  have htrace : WordTrace (prefixWord ++ tailWord_4446576) baseStart_4446576 baseEnd_4446576 := by
    simpa [prefixWord, tailWord_4446576, baseEnd_4446576] using wordTrace_append hprefix tailTrace_4446576
  have hstable : (prefixWord ++ tailWord_4446576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446576).length < 2 ^ (prefixWord ++ tailWord_4446576).sum := by decide
  have hdescent : baseEnd_4446576 < baseStart_4446576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446579 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_4446579 : Nat := 118140960795 + 4446579 * 2 ^ 59
def prefixEnd_4446579 : Nat := 4983230072969 + 3 ^ 40 * 4446579 * 2
def baseEnd_4446579 : Nat := 2283232295188663472913061

theorem tailTrace_4446579 : CollatzResearch.WordTrace tailWord_4446579 prefixEnd_4446579 2283232295188663472913061 := by
  unfold tailWord_4446579
  simp only [CollatzResearch.WordTrace]
  refine ⟨162180059757811173078174791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108120039838540782052116527 162180059757811173078174791)
  ·
    refine ⟨243270089636716759617262187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162180059757811173078174791 243270089636716759617262187)
    ·
      refine ⟨364905134455075139425893281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243270089636716759617262187 364905134455075139425893281)
      ·
        refine ⟨273678850841306354569419961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364905134455075139425893281 273678850841306354569419961)
        ·
          refine ⟨205259138130979765927064971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273678850841306354569419961 205259138130979765927064971)
          ·
            refine ⟨307888707196469648890597457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205259138130979765927064971 307888707196469648890597457)
            ·
              refine ⟨230916530397352236667948093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307888707196469648890597457 230916530397352236667948093)
              ·
                refine ⟨86593698899007088750480535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230916530397352236667948093 86593698899007088750480535)
                ·
                  refine ⟨129890548348510633125720803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86593698899007088750480535 129890548348510633125720803)
                  ·
                    refine ⟨194835822522765949688581205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129890548348510633125720803 194835822522765949688581205)
                    ·
                      refine ⟨2283232295188663472913061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194835822522765949688581205 2283232295188663472913061)
                      ·
                        rfl

theorem cell23_4446579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_4446579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446579 prefixEnd_4446579 := by exact prefixLift 4446579
  have htrace : WordTrace (prefixWord ++ tailWord_4446579) baseStart_4446579 baseEnd_4446579 := by
    simpa [prefixWord, tailWord_4446579, baseEnd_4446579] using wordTrace_append hprefix tailTrace_4446579
  have hstable : (prefixWord ++ tailWord_4446579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446579).length < 2 ^ (prefixWord ++ tailWord_4446579).sum := by decide
  have hdescent : baseEnd_4446579 < baseStart_4446579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446593 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 6]
def baseStart_4446593 : Nat := 118140960795 + 4446593 * 2 ^ 59
def prefixEnd_4446593 : Nat := 4983230072969 + 3 ^ 40 * 4446593 * 2
def baseEnd_4446593 : Nat := 253693275990869602015333

theorem tailTrace_4446593 : CollatzResearch.WordTrace tailWord_4446593 prefixEnd_4446593 253693275990869602015333 := by
  unfold tailWord_4446593
  simp only [CollatzResearch.WordTrace]
  refine ⟨162180570379760453469184433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108120380253173635646122955 162180570379760453469184433)
  ·
    refine ⟨121635427784820340101888325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162180570379760453469184433 121635427784820340101888325)
    ·
      refine ⟨22806642709653813769104061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121635427784820340101888325 22806642709653813769104061)
      ·
        refine ⟨8552491016120180163414023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22806642709653813769104061 8552491016120180163414023)
        ·
          refine ⟨12828736524180270245121035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552491016120180163414023 12828736524180270245121035)
          ·
            refine ⟨19243104786270405367681553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12828736524180270245121035 19243104786270405367681553)
            ·
              refine ⟨14432328589702804025761165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19243104786270405367681553 14432328589702804025761165)
              ·
                refine ⟨5412123221138551509660437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14432328589702804025761165 5412123221138551509660437)
                ·
                  refine ⟨253693275990869602015333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5412123221138551509660437 253693275990869602015333)
                  ·
                    rfl

theorem cell23_4446593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 6].length) (baseStart_4446593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446593 prefixEnd_4446593 := by exact prefixLift 4446593
  have htrace : WordTrace (prefixWord ++ tailWord_4446593) baseStart_4446593 baseEnd_4446593 := by
    simpa [prefixWord, tailWord_4446593, baseEnd_4446593] using wordTrace_append hprefix tailTrace_4446593
  have hstable : (prefixWord ++ tailWord_4446593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446593).length < 2 ^ (prefixWord ++ tailWord_4446593).sum := by decide
  have hdescent : baseEnd_4446593 < baseStart_4446593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446603 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 3]
def baseStart_4446603 : Nat := 118140960795 + 4446603 * 2 ^ 59
def prefixEnd_4446603 : Nat := 4983230072969 + 3 ^ 40 * 4446603 * 2
def baseEnd_4446603 : Nat := 2283244618724371379012951

theorem tailTrace_4446603 : CollatzResearch.WordTrace tailWord_4446603 prefixEnd_4446603 2283244618724371379012951 := by
  unfold tailWord_4446603
  simp only [CollatzResearch.WordTrace]
  refine ⟨162180935109724225177048463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108120623406482816784698975 162180935109724225177048463)
  ·
    refine ⟨243271402664586337765572695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162180935109724225177048463 243271402664586337765572695)
    ·
      refine ⟨364907103996879506648359043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243271402664586337765572695 364907103996879506648359043)
      ·
        refine ⟨547360655995319259972538565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364907103996879506648359043 547360655995319259972538565)
        ·
          refine ⟨102630122999122361244850981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 547360655995319259972538565 102630122999122361244850981)
          ·
            refine ⟨19243148062335442733409559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102630122999122361244850981 19243148062335442733409559)
            ·
              refine ⟨28864722093503164100114339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19243148062335442733409559 28864722093503164100114339)
              ·
                refine ⟨43297083140254746150171509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28864722093503164100114339 43297083140254746150171509)
                ·
                  refine ⟨4059101544398882451578579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43297083140254746150171509 4059101544398882451578579)
                  ·
                    refine ⟨6088652316598323677367869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4059101544398882451578579 6088652316598323677367869)
                    ·
                      refine ⟨2283244618724371379012951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088652316598323677367869 2283244618724371379012951)
                      ·
                        rfl

theorem cell23_4446603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 3].length) (baseStart_4446603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446603 prefixEnd_4446603 := by exact prefixLift 4446603
  have htrace : WordTrace (prefixWord ++ tailWord_4446603) baseStart_4446603 baseEnd_4446603 := by
    simpa [prefixWord, tailWord_4446603, baseEnd_4446603] using wordTrace_append hprefix tailTrace_4446603
  have hstable : (prefixWord ++ tailWord_4446603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446603).length < 2 ^ (prefixWord ++ tailWord_4446603).sum := by decide
  have hdescent : baseEnd_4446603 < baseStart_4446603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446623 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 1, 5]
def baseStart_4446623 : Nat := 118140960795 + 4446623 * 2 ^ 59
def prefixEnd_4446623 : Nat := 4983230072969 + 3 ^ 40 * 4446623 * 2
def baseEnd_4446623 : Nat := 761084962779153766920953

theorem tailTrace_4446623 : CollatzResearch.WordTrace tailWord_4446623 prefixEnd_4446623 761084962779153766920953 := by
  unfold tailWord_4446623
  simp only [CollatzResearch.WordTrace]
  refine ⟨162181664569651768592776523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108121109713101179061851015 162181664569651768592776523)
  ·
    refine ⟨243272496854477652889164785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162181664569651768592776523 243272496854477652889164785)
    ·
      refine ⟨182454372640858239666873589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243272496854477652889164785 182454372640858239666873589)
      ·
        refine ⟨17105097435080459968769399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182454372640858239666873589 17105097435080459968769399)
        ·
          refine ⟨25657646152620689953154099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17105097435080459968769399 25657646152620689953154099)
          ·
            refine ⟨38486469228931034929731149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25657646152620689953154099 38486469228931034929731149)
            ·
              refine ⟨14432425960849138098649181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38486469228931034929731149 14432425960849138098649181)
              ·
                refine ⟨5412159735318426786993443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14432425960849138098649181 5412159735318426786993443)
                ·
                  refine ⟨8118239602977640180490165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412159735318426786993443 8118239602977640180490165)
                  ·
                    refine ⟨761084962779153766920953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8118239602977640180490165 761084962779153766920953)
                    ·
                      rfl

theorem cell23_4446623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_4446623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446623 prefixEnd_4446623 := by exact prefixLift 4446623
  have htrace : WordTrace (prefixWord ++ tailWord_4446623) baseStart_4446623 baseEnd_4446623 := by
    simpa [prefixWord, tailWord_4446623, baseEnd_4446623] using wordTrace_append hprefix tailTrace_4446623
  have hstable : (prefixWord ++ tailWord_4446623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446623).length < 2 ^ (prefixWord ++ tailWord_4446623).sum := by decide
  have hdescent : baseEnd_4446623 < baseStart_4446623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446644 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 6]
def baseStart_4446644 : Nat := 118140960795 + 4446644 * 2 ^ 59
def prefixEnd_4446644 : Nat := 4983230072969 + 3 ^ 40 * 4446644 * 2
def baseEnd_4446644 : Nat := 253696185714578413177807

theorem tailTrace_4446644 : CollatzResearch.WordTrace tailWord_4446644 prefixEnd_4446644 253696185714578413177807 := by
  unfold tailWord_4446644
  simp only [CollatzResearch.WordTrace]
  refine ⟨81091215251287844589645493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108121620335050459452860657 81091215251287844589645493)
  ·
    refine ⟨7602301429808235430279265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81091215251287844589645493 7602301429808235430279265)
    ·
      refine ⟨5701726072356176572709449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7602301429808235430279265 5701726072356176572709449)
      ·
        refine ⟨4276294554267132429532087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5701726072356176572709449 4276294554267132429532087)
        ·
          refine ⟨6414441831400698644298131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276294554267132429532087 6414441831400698644298131)
          ·
            refine ⟨9621662747101047966447197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6414441831400698644298131 9621662747101047966447197)
            ·
              refine ⟨3608123530162892987417699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9621662747101047966447197 3608123530162892987417699)
              ·
                refine ⟨5412185295244339481126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608123530162892987417699 5412185295244339481126549)
                ·
                  refine ⟨253696185714578413177807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5412185295244339481126549 253696185714578413177807)
                  ·
                    rfl

theorem cell23_4446644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_4446644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446644 prefixEnd_4446644 := by exact prefixLift 4446644
  have htrace : WordTrace (prefixWord ++ tailWord_4446644) baseStart_4446644 baseEnd_4446644 := by
    simpa [prefixWord, tailWord_4446644, baseEnd_4446644] using wordTrace_append hprefix tailTrace_4446644
  have hstable : (prefixWord ++ tailWord_4446644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446644).length < 2 ^ (prefixWord ++ tailWord_4446644).sum := by decide
  have hdescent : baseEnd_4446644 < baseStart_4446644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446653 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_4446653 : Nat := 118140960795 + 4446653 * 2 ^ 59
def prefixEnd_4446653 : Nat := 4983230072969 + 3 ^ 40 * 4446653 * 2
def baseEnd_4446653 : Nat := 761090097585698727795907

theorem tailTrace_4446653 : CollatzResearch.WordTrace tailWord_4446653 prefixEnd_4446653 761090097585698727795907 := by
  unfold tailWord_4446653
  simp only [CollatzResearch.WordTrace]
  refine ⟨162182758759543083716368613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108121839173028722477579075 162182758759543083716368613)
  ·
    refine ⟨30409267267414328196819115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162182758759543083716368613 30409267267414328196819115)
    ·
      refine ⟨45613900901121492295228673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30409267267414328196819115 45613900901121492295228673)
      ·
        refine ⟨34210425675841119221421505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45613900901121492295228673 34210425675841119221421505)
        ·
          refine ⟨25657819256880839416066129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34210425675841119221421505 25657819256880839416066129)
          ·
            refine ⟨19243364442660629562049597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25657819256880839416066129 19243364442660629562049597)
            ·
              refine ⟨7216261665997736085768599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19243364442660629562049597 7216261665997736085768599)
              ·
                refine ⟨10824392498996604128652899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7216261665997736085768599 10824392498996604128652899)
                ·
                  refine ⟨16236588748494906192979349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10824392498996604128652899 16236588748494906192979349)
                  ·
                    refine ⟨761090097585698727795907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16236588748494906192979349 761090097585698727795907)
                    ·
                      rfl

theorem cell23_4446653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_4446653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446653 prefixEnd_4446653 := by exact prefixLift 4446653
  have htrace : WordTrace (prefixWord ++ tailWord_4446653) baseStart_4446653 baseEnd_4446653 := by
    simpa [prefixWord, tailWord_4446653, baseEnd_4446653] using wordTrace_append hprefix tailTrace_4446653
  have hstable : (prefixWord ++ tailWord_4446653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446653).length < 2 ^ (prefixWord ++ tailWord_4446653).sum := by decide
  have hdescent : baseEnd_4446653 < baseStart_4446653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446666 : List Nat := [3, 1, 2, 1, 2, 2, 3, 9]
def baseStart_4446666 : Nat := 118140960795 + 4446666 * 2 ^ 59
def prefixEnd_4446666 : Nat := 4983230072969 + 3 ^ 40 * 4446666 * 2
def baseEnd_4446666 : Nat := 84565813629837208612043

theorem tailTrace_4446666 : CollatzResearch.WordTrace tailWord_4446666 prefixEnd_4446666 84565813629837208612043 := by
  unfold tailWord_4446666
  simp only [CollatzResearch.WordTrace]
  refine ⟨40545808227123996734147963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108122155272330657957727901 40545808227123996734147963)
  ·
    refine ⟨60818712340685995101221945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40545808227123996734147963 60818712340685995101221945)
    ·
      refine ⟨45614034255514496325916459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60818712340685995101221945 45614034255514496325916459)
      ·
        refine ⟨68421051383271744488874689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45614034255514496325916459 68421051383271744488874689)
        ·
          refine ⟨51315788537453808366656017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68421051383271744488874689 51315788537453808366656017)
          ·
            refine ⟨38486841403090356274992013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51315788537453808366656017 38486841403090356274992013)
            ·
              refine ⟨14432565526158883603122005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38486841403090356274992013 14432565526158883603122005)
              ·
                refine ⟨84565813629837208612043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14432565526158883603122005 84565813629837208612043)
                ·
                  rfl

theorem cell23_4446666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_4446666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446666 prefixEnd_4446666 := by exact prefixLift 4446666
  have htrace : WordTrace (prefixWord ++ tailWord_4446666) baseStart_4446666 baseEnd_4446666 := by
    simpa [prefixWord, tailWord_4446666, baseEnd_4446666] using wordTrace_append hprefix tailTrace_4446666
  have hstable : (prefixWord ++ tailWord_4446666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446666).length < 2 ^ (prefixWord ++ tailWord_4446666).sum := by decide
  have hdescent : baseEnd_4446666 < baseStart_4446666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446703 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 7, 2]
def baseStart_4446703 : Nat := 118140960795 + 4446703 * 2 ^ 59
def prefixEnd_4446703 : Nat := 4983230072969 + 3 ^ 40 * 4446703 * 2
def baseEnd_4446703 : Nat := 2283295966789820987762491

theorem tailTrace_4446703 : CollatzResearch.WordTrace tailWord_4446703 prefixEnd_4446703 2283295966789820987762491 := by
  unfold tailWord_4446703
  simp only [CollatzResearch.WordTrace]
  refine ⟨162184582409361942255688763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108123054939574628170459175 162184582409361942255688763)
  ·
    refine ⟨243276873614042913383533145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162184582409361942255688763 243276873614042913383533145)
    ·
      refine ⟨182457655210532185037649859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243276873614042913383533145 182457655210532185037649859)
      ·
        refine ⟨273686482815798277556474789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182457655210532185037649859 273686482815798277556474789)
        ·
          refine ⟨51316215527962177041839023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273686482815798277556474789 51316215527962177041839023)
          ·
            refine ⟨76974323291943265562758535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51316215527962177041839023 76974323291943265562758535)
            ·
              refine ⟨115461484937914898344137803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76974323291943265562758535 115461484937914898344137803)
              ·
                refine ⟨173192227406872347516206705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115461484937914898344137803 173192227406872347516206705)
                ·
                  refine ⟨129894170555154260637155029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173192227406872347516206705 129894170555154260637155029)
                  ·
                    refine ⟨3044394622386427983683321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129894170555154260637155029 3044394622386427983683321)
                    ·
                      refine ⟨2283295966789820987762491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044394622386427983683321 2283295966789820987762491)
                      ·
                        rfl

theorem cell23_4446703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7, 2].length) (baseStart_4446703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446703 prefixEnd_4446703 := by exact prefixLift 4446703
  have htrace : WordTrace (prefixWord ++ tailWord_4446703) baseStart_4446703 baseEnd_4446703 := by
    simpa [prefixWord, tailWord_4446703, baseEnd_4446703] using wordTrace_append hprefix tailTrace_4446703
  have hstable : (prefixWord ++ tailWord_4446703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446703).length < 2 ^ (prefixWord ++ tailWord_4446703).sum := by decide
  have hdescent : baseEnd_4446703 < baseStart_4446703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
