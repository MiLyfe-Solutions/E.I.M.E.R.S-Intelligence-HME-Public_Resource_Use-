import V185TrunkScan23Chunk0586

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3471452 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 6]
def baseStart_3471452 : Nat := 118140960795 + 3471452 * 2 ^ 59
def prefixEnd_3471452 : Nat := 4983230072969 + 3 ^ 40 * 3471452 * 2
def baseEnd_3471452 : Nat := 198058160556873017976121

theorem tailTrace_3471452 : CollatzResearch.WordTrace tailWord_3471452 prefixEnd_3471452 198058160556873017976121 := by
  unfold tailWord_3471452
  simp only [CollatzResearch.WordTrace]
  refine ⟨63307128109764877822688305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84409504146353170430251073 63307128109764877822688305)
  ·
    refine ⟨47480346082323658367016229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63307128109764877822688305 47480346082323658367016229)
    ·
      refine ⟨8902564890435685943815543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47480346082323658367016229 8902564890435685943815543)
      ·
        refine ⟨13353847335653528915723315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8902564890435685943815543 13353847335653528915723315)
        ·
          refine ⟨20030771003480293373584973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13353847335653528915723315 20030771003480293373584973)
          ·
            refine ⟨7511539126305110015094365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20030771003480293373584973 7511539126305110015094365)
            ·
              refine ⟨2816827172364416255660387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7511539126305110015094365 2816827172364416255660387)
              ·
                refine ⟨4225240758546624383490581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816827172364416255660387 4225240758546624383490581)
                ·
                  refine ⟨198058160556873017976121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4225240758546624383490581 198058160556873017976121)
                  ·
                    rfl

theorem cell23_3471452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_3471452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471452 prefixEnd_3471452 := by exact prefixLift 3471452
  have htrace : WordTrace (prefixWord ++ tailWord_3471452) baseStart_3471452 baseEnd_3471452 := by
    simpa [prefixWord, tailWord_3471452, baseEnd_3471452] using wordTrace_append hprefix tailTrace_3471452
  have hstable : (prefixWord ++ tailWord_3471452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471452).length < 2 ^ (prefixWord ++ tailWord_3471452).sum := by decide
  have hdescent : baseEnd_3471452 < baseStart_3471452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471455 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 6, 3, 2]
def baseStart_3471455 : Nat := 118140960795 + 3471455 * 2 ^ 59
def prefixEnd_3471455 : Nat := 4983230072969 + 3 ^ 40 * 3471455 * 2
def baseEnd_3471455 : Nat := 1782524985453820650047575

theorem tailTrace_3471455 : CollatzResearch.WordTrace tailWord_3471455 prefixEnd_3471455 1782524985453820650047575 := by
  unfold tailWord_3471455
  simp only [CollatzResearch.WordTrace]
  refine ⟨126614365638518887157735819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84409577092345924771823879 126614365638518887157735819)
  ·
    refine ⟨189921548457778330736603729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126614365638518887157735819 189921548457778330736603729)
    ·
      refine ⟨142441161343333748052452797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189921548457778330736603729 142441161343333748052452797)
      ·
        refine ⟨53415435503750155519669799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142441161343333748052452797 53415435503750155519669799)
        ·
          refine ⟨80123153255625233279504699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53415435503750155519669799 80123153255625233279504699)
          ·
            refine ⟨120184729883437849919257049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80123153255625233279504699 120184729883437849919257049)
            ·
              refine ⟨90138547412578387439442787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120184729883437849919257049 90138547412578387439442787)
              ·
                refine ⟨135207821118867581159164181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90138547412578387439442787 135207821118867581159164181)
                ·
                  refine ⟨6337866614946917866835821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135207821118867581159164181 6337866614946917866835821)
                  ·
                    refine ⟨2376699980605094200063433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6337866614946917866835821 2376699980605094200063433)
                    ·
                      refine ⟨1782524985453820650047575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376699980605094200063433 1782524985453820650047575)
                      ·
                        rfl

theorem cell23_3471455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_3471455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471455 prefixEnd_3471455 := by exact prefixLift 3471455
  have htrace : WordTrace (prefixWord ++ tailWord_3471455) baseStart_3471455 baseEnd_3471455 := by
    simpa [prefixWord, tailWord_3471455, baseEnd_3471455] using wordTrace_append hprefix tailTrace_3471455
  have hstable : (prefixWord ++ tailWord_3471455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471455).length < 2 ^ (prefixWord ++ tailWord_3471455).sum := by decide
  have hdescent : baseEnd_3471455 < baseStart_3471455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471465 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 1, 5]
def baseStart_3471465 : Nat := 118140960795 + 3471465 * 2 ^ 59
def prefixEnd_3471465 : Nat := 4983230072969 + 3 ^ 40 * 3471465 * 2
def baseEnd_3471465 : Nat := 594176706753455203640843

theorem tailTrace_3471465 : CollatzResearch.WordTrace tailWord_3471465 prefixEnd_3471465 594176706753455203640843 := by
  unfold tailWord_3471465
  simp only [CollatzResearch.WordTrace]
  refine ⟨126614730368482658865599849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84409820245655105910399899 126614730368482658865599849)
  ·
    refine ⟨94961047776361994149199887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126614730368482658865599849 94961047776361994149199887)
    ·
      refine ⟨142441571664542991223799831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94961047776361994149199887 142441571664542991223799831)
      ·
        refine ⟨213662357496814486835699747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142441571664542991223799831 213662357496814486835699747)
        ·
          refine ⟨320493536245221730253549621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213662357496814486835699747 320493536245221730253549621)
          ·
            refine ⟨30046269022989537211270277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320493536245221730253549621 30046269022989537211270277)
            ·
              refine ⟨5633675441810538227113177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30046269022989537211270277 5633675441810538227113177)
              ·
                refine ⟨4225256581357903670334883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5633675441810538227113177 4225256581357903670334883)
                ·
                  refine ⟨6337884872036855505502325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225256581357903670334883 6337884872036855505502325)
                  ·
                    refine ⟨594176706753455203640843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6337884872036855505502325 594176706753455203640843)
                    ·
                      rfl

theorem cell23_3471465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_3471465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471465 prefixEnd_3471465 := by exact prefixLift 3471465
  have htrace : WordTrace (prefixWord ++ tailWord_3471465) baseStart_3471465 baseEnd_3471465 := by
    simpa [prefixWord, tailWord_3471465, baseEnd_3471465] using wordTrace_append hprefix tailTrace_3471465
  have hstable : (prefixWord ++ tailWord_3471465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471465).length < 2 ^ (prefixWord ++ tailWord_3471465).sum := by decide
  have hdescent : baseEnd_3471465 < baseStart_3471465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471479 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 1, 1, 3]
def baseStart_3471479 : Nat := 118140960795 + 3471479 * 2 ^ 59
def prefixEnd_3471479 : Nat := 4983230072969 + 3 ^ 40 * 3471479 * 2
def baseEnd_3471479 : Nat := 1782537308989528556147465

theorem tailTrace_3471479 : CollatzResearch.WordTrace tailWord_3471479 prefixEnd_3471479 1782537308989528556147465 := by
  unfold tailWord_3471479
  simp only [CollatzResearch.WordTrace]
  refine ⟨126615240990431939256609491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84410160660287959504406327 126615240990431939256609491)
  ·
    refine ⟨189922861485647908884914237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126615240990431939256609491 189922861485647908884914237)
    ·
      refine ⟨71221073057117965831842839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189922861485647908884914237 71221073057117965831842839)
      ·
        refine ⟨106831609585676948747764259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71221073057117965831842839 106831609585676948747764259)
        ·
          refine ⟨160247414378515423121646389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106831609585676948747764259 160247414378515423121646389)
          ·
            refine ⟨15023195097985820917654349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160247414378515423121646389 15023195097985820917654349)
            ·
              refine ⟨5633698161744682844120381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15023195097985820917654349 5633698161744682844120381)
              ·
                refine ⟨2112636810654256066545143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5633698161744682844120381 2112636810654256066545143)
                ·
                  refine ⟨3168955215981384099817715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112636810654256066545143 3168955215981384099817715)
                  ·
                    refine ⟨4753432823972076149726573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3168955215981384099817715 4753432823972076149726573)
                    ·
                      refine ⟨1782537308989528556147465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753432823972076149726573 1782537308989528556147465)
                      ·
                        rfl

theorem cell23_3471479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_3471479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471479 prefixEnd_3471479 := by exact prefixLift 3471479
  have htrace : WordTrace (prefixWord ++ tailWord_3471479) baseStart_3471479 baseEnd_3471479 := by
    simpa [prefixWord, tailWord_3471479, baseEnd_3471479] using wordTrace_append hprefix tailTrace_3471479
  have hstable : (prefixWord ++ tailWord_3471479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471479).length < 2 ^ (prefixWord ++ tailWord_3471479).sum := by decide
  have hdescent : baseEnd_3471479 < baseStart_3471479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471489 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_3471489 : Nat := 118140960795 + 3471489 * 2 ^ 59
def prefixEnd_3471489 : Nat := 4983230072969 + 3 ^ 40 * 3471489 * 2
def baseEnd_3471489 : Nat := 1782542443796073517022419

theorem tailTrace_3471489 : CollatzResearch.WordTrace tailWord_3471489 prefixEnd_3471489 1782542443796073517022419 := by
  unfold tailWord_3471489
  simp only [CollatzResearch.WordTrace]
  refine ⟨126615605720395710964473521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84410403813597140642982347 126615605720395710964473521)
  ·
    refine ⟨94961704290296783223355141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126615605720395710964473521 94961704290296783223355141)
    ·
      refine ⟨17805319554430646854379089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94961704290296783223355141 17805319554430646854379089)
      ·
        refine ⟨13353989665822985140784317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17805319554430646854379089 13353989665822985140784317)
        ·
          refine ⟨5007746124683619427794119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13353989665822985140784317 5007746124683619427794119)
          ·
            refine ⟨7511619187025429141691179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007746124683619427794119 7511619187025429141691179)
            ·
              refine ⟨11267428780538143712536769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511619187025429141691179 11267428780538143712536769)
              ·
                refine ⟨8450571585403607784402577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11267428780538143712536769 8450571585403607784402577)
                ·
                  refine ⟨6337928689052705838301933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8450571585403607784402577 6337928689052705838301933)
                  ·
                    refine ⟨2376723258394764689363225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6337928689052705838301933 2376723258394764689363225)
                    ·
                      refine ⟨1782542443796073517022419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376723258394764689363225 1782542443796073517022419)
                      ·
                        rfl

theorem cell23_3471489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_3471489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471489 prefixEnd_3471489 := by exact prefixLift 3471489
  have htrace : WordTrace (prefixWord ++ tailWord_3471489) baseStart_3471489 baseEnd_3471489 := by
    simpa [prefixWord, tailWord_3471489, baseEnd_3471489] using wordTrace_append hprefix tailTrace_3471489
  have hstable : (prefixWord ++ tailWord_3471489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471489).length < 2 ^ (prefixWord ++ tailWord_3471489).sum := by decide
  have hdescent : baseEnd_3471489 < baseStart_3471489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471495 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 4, 4]
def baseStart_3471495 : Nat := 118140960795 + 3471495 * 2 ^ 59
def prefixEnd_3471495 : Nat := 4983230072969 + 3 ^ 40 * 3471495 * 2
def baseEnd_3471495 : Nat := 594181841560000164515797

theorem tailTrace_3471495 : CollatzResearch.WordTrace tailWord_3471495 prefixEnd_3471495 594181841560000164515797 := by
  unfold tailWord_3471495
  simp only [CollatzResearch.WordTrace]
  refine ⟨126615824558373973989191939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84410549705582649326127959 126615824558373973989191939)
  ·
    refine ⟨189923736837560960983787909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126615824558373973989191939 189923736837560960983787909)
    ·
      refine ⟨35610700657042680184460233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189923736837560960983787909 35610700657042680184460233)
      ·
        refine ⟨26708025492782010138345175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35610700657042680184460233 26708025492782010138345175)
        ·
          refine ⟨40062038239173015207517763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26708025492782010138345175 40062038239173015207517763)
          ·
            refine ⟨60093057358759522811276645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40062038239173015207517763 60093057358759522811276645)
            ·
              refine ⟨11267448254767410527114371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60093057358759522811276645 11267448254767410527114371)
              ·
                refine ⟨16901172382151115790671557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11267448254767410527114371 16901172382151115790671557)
                ·
                  refine ⟨3168969821653334210750917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16901172382151115790671557 3168969821653334210750917)
                  ·
                    refine ⟨594181841560000164515797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3168969821653334210750917 594181841560000164515797)
                    ·
                      rfl

theorem cell23_3471495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3471495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471495 prefixEnd_3471495 := by exact prefixLift 3471495
  have htrace : WordTrace (prefixWord ++ tailWord_3471495) baseStart_3471495 baseEnd_3471495 := by
    simpa [prefixWord, tailWord_3471495, baseEnd_3471495] using wordTrace_append hprefix tailTrace_3471495
  have hstable : (prefixWord ++ tailWord_3471495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471495).length < 2 ^ (prefixWord ++ tailWord_3471495).sum := by decide
  have hdescent : baseEnd_3471495 < baseStart_3471495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471519 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3471519 : Nat := 118140960795 + 3471519 * 2 ^ 59
def prefixEnd_3471519 : Nat := 4983230072969 + 3 ^ 40 * 3471519 * 2
def baseEnd_3471519 : Nat := 1782557848215708399647281

theorem tailTrace_3471519 : CollatzResearch.WordTrace tailWord_3471519 prefixEnd_3471519 1782557848215708399647281 := by
  unfold tailWord_3471519
  simp only [CollatzResearch.WordTrace]
  refine ⟨126616699910287026088065611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84411133273524684058710407 126616699910287026088065611)
  ·
    refine ⟨189925049865430539132098417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126616699910287026088065611 189925049865430539132098417)
    ·
      refine ⟨142443787399072904349073813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189925049865430539132098417 142443787399072904349073813)
      ·
        refine ⟨6677052534331542391362835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142443787399072904349073813 6677052534331542391362835)
        ·
          refine ⟨10015578801497313587044253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677052534331542391362835 10015578801497313587044253)
          ·
            refine ⟨3755842050561492595141595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10015578801497313587044253 3755842050561492595141595)
            ·
              refine ⟨5633763075842238892712393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755842050561492595141595 5633763075842238892712393)
              ·
                refine ⟨4225322306881679169534295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5633763075842238892712393 4225322306881679169534295)
                ·
                  refine ⟨6337983460322518754301443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225322306881679169534295 6337983460322518754301443)
                  ·
                    refine ⟨9506975190483778131452165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6337983460322518754301443 9506975190483778131452165)
                    ·
                      refine ⟨1782557848215708399647281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9506975190483778131452165 1782557848215708399647281)
                      ·
                        rfl

theorem cell23_3471519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3471519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471519 prefixEnd_3471519 := by exact prefixLift 3471519
  have htrace : WordTrace (prefixWord ++ tailWord_3471519) baseStart_3471519 baseEnd_3471519 := by
    simpa [prefixWord, tailWord_3471519, baseEnd_3471519] using wordTrace_append hprefix tailTrace_3471519
  have hstable : (prefixWord ++ tailWord_3471519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471519).length < 2 ^ (prefixWord ++ tailWord_3471519).sum := by decide
  have hdescent : baseEnd_3471519 < baseStart_3471519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471562 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_3471562 : Nat := 118140960795 + 3471562 * 2 ^ 59
def prefixEnd_3471562 : Nat := 4983230072969 + 3 ^ 40 * 3471562 * 2
def baseEnd_3471562 : Nat := 1782579927883851731409583

theorem tailTrace_3471562 : CollatzResearch.WordTrace tailWord_3471562 prefixEnd_3471562 1782579927883851731409583 := by
  unfold tailWord_3471562
  simp only [CollatzResearch.WordTrace]
  refine ⟨31654567062282811107970235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84412178832754162954587293 31654567062282811107970235)
  ·
    refine ⟨47481850593424216661955353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31654567062282811107970235 47481850593424216661955353)
    ·
      refine ⟨35611387945068162496466515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47481850593424216661955353 35611387945068162496466515)
      ·
        refine ⟨53417081917602243744699773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35611387945068162496466515 53417081917602243744699773)
        ·
          refine ⟨20031405719100841404262415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53417081917602243744699773 20031405719100841404262415)
          ·
            refine ⟨30047108578651262106393623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20031405719100841404262415 30047108578651262106393623)
            ·
              refine ⟨45070662867976893159590435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30047108578651262106393623 45070662867976893159590435)
              ·
                refine ⟨67605994301965339739385653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45070662867976893159590435 67605994301965339739385653)
                ·
                  refine ⟨6338061965809250600567405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67605994301965339739385653 6338061965809250600567405)
                  ·
                    refine ⟨2376773237178468975212777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6338061965809250600567405 2376773237178468975212777)
                    ·
                      refine ⟨1782579927883851731409583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376773237178468975212777 1782579927883851731409583)
                      ·
                        rfl

theorem cell23_3471562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_3471562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471562 prefixEnd_3471562 := by exact prefixLift 3471562
  have htrace : WordTrace (prefixWord ++ tailWord_3471562) baseStart_3471562 baseEnd_3471562 := by
    simpa [prefixWord, tailWord_3471562, baseEnd_3471562] using wordTrace_append hprefix tailTrace_3471562
  have hstable : (prefixWord ++ tailWord_3471562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471562).length < 2 ^ (prefixWord ++ tailWord_3471562).sum := by decide
  have hdescent : baseEnd_3471562 < baseStart_3471562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471609 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 2, 2, 2]
def baseStart_3471609 : Nat := 118140960795 + 3471609 * 2 ^ 59
def prefixEnd_3471609 : Nat := 4983230072969 + 3 ^ 40 * 3471609 * 2
def baseEnd_3471609 : Nat := 1782604061474613047521867

theorem tailTrace_3471609 : CollatzResearch.WordTrace tailWord_3471609 prefixEnd_3471609 1782604061474613047521867 := by
  unfold tailWord_3471609
  simp only [CollatzResearch.WordTrace]
  refine ⟨126619982479960971458841881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84413321653307314305894587 126619982479960971458841881)
  ·
    refine ⟨94964986859970728594131411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126619982479960971458841881 94964986859970728594131411)
    ·
      refine ⟨142447480289956092891197117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94964986859970728594131411 142447480289956092891197117)
      ·
        refine ⟨53417805108733534834198919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142447480289956092891197117 53417805108733534834198919)
        ·
          refine ⟨80126707663100302251298379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53417805108733534834198919 80126707663100302251298379)
          ·
            refine ⟨120190061494650453376947569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80126707663100302251298379 120190061494650453376947569)
            ·
              refine ⟨90142546120987840032710677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120190061494650453376947569 90142546120987840032710677)
              ·
                refine ⟨4225431849421305001533313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90142546120987840032710677 4225431849421305001533313)
                ·
                  refine ⟨3169073887065978751149985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225431849421305001533313 3169073887065978751149985)
                  ·
                    refine ⟨2376805415299484063362489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3169073887065978751149985 2376805415299484063362489)
                    ·
                      refine ⟨1782604061474613047521867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376805415299484063362489 1782604061474613047521867)
                      ·
                        rfl

theorem cell23_3471609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_3471609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471609 prefixEnd_3471609 := by exact prefixLift 3471609
  have htrace : WordTrace (prefixWord ++ tailWord_3471609) baseStart_3471609 baseEnd_3471609 := by
    simpa [prefixWord, tailWord_3471609, baseEnd_3471609] using wordTrace_append hprefix tailTrace_3471609
  have hstable : (prefixWord ++ tailWord_3471609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471609).length < 2 ^ (prefixWord ++ tailWord_3471609).sum := by decide
  have hdescent : baseEnd_3471609 < baseStart_3471609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471615 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 7]
def baseStart_3471615 : Nat := 118140960795 + 3471615 * 2 ^ 59
def prefixEnd_3471615 : Nat := 4983230072969 + 3 ^ 40 * 3471615 * 2
def baseEnd_3471615 : Nat := 198067460262060002671871

theorem tailTrace_3471615 : CollatzResearch.WordTrace tailWord_3471615 prefixEnd_3471615 198067460262060002671871 := by
  unfold tailWord_3471615
  simp only [CollatzResearch.WordTrace]
  refine ⟨126620201317939234483560299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84413467545292822989040199 126620201317939234483560299)
  ·
    refine ⟨189930301976908851725340449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126620201317939234483560299 189930301976908851725340449)
    ·
      refine ⟨142447726482681638794005337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189930301976908851725340449 142447726482681638794005337)
      ·
        refine ⟨106835794862011229095504003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142447726482681638794005337 106835794862011229095504003)
        ·
          refine ⟨160253692293016843643256005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106835794862011229095504003 160253692293016843643256005)
          ·
            refine ⟨30047567304940658183110501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160253692293016843643256005 30047567304940658183110501)
            ·
              refine ⟨5633918869676373409333219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30047567304940658183110501 5633918869676373409333219)
              ·
                refine ⟨8450878304514560113999829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633918869676373409333219 8450878304514560113999829)
                ·
                  refine ⟨198067460262060002671871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8450878304514560113999829 198067460262060002671871)
                  ·
                    rfl

theorem cell23_3471615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 7].length) (baseStart_3471615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471615 prefixEnd_3471615 := by exact prefixLift 3471615
  have htrace : WordTrace (prefixWord ++ tailWord_3471615) baseStart_3471615 baseEnd_3471615 := by
    simpa [prefixWord, tailWord_3471615, baseEnd_3471615] using wordTrace_append hprefix tailTrace_3471615
  have hstable : (prefixWord ++ tailWord_3471615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471615).length < 2 ^ (prefixWord ++ tailWord_3471615).sum := by decide
  have hdescent : baseEnd_3471615 < baseStart_3471615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471666 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_3471666 : Nat := 118140960795 + 3471666 * 2 ^ 59
def prefixEnd_3471666 : Nat := 4983230072969 + 3 ^ 40 * 3471666 * 2
def baseEnd_3471666 : Nat := 198070369985768813834345

theorem tailTrace_3471666 : CollatzResearch.WordTrace tailWord_3471666 prefixEnd_3471666 198070369985768813834345 := by
  unfold tailWord_3471666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31655515360188617548416713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84414707627169646795777901 31655515360188617548416713)
  ·
    refine ⟨23741636520141463161312535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31655515360188617548416713 23741636520141463161312535)
    ·
      refine ⟨35612454780212194741968803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23741636520141463161312535 35612454780212194741968803)
      ·
        refine ⟨53418682170318292112953205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35612454780212194741968803 53418682170318292112953205)
        ·
          refine ⟨5008001453467339885589363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53418682170318292112953205 5008001453467339885589363)
          ·
            refine ⟨7512002180201009828384045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008001453467339885589363 7512002180201009828384045)
            ·
              refine ⟨2817000817575378685644017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7512002180201009828384045 2817000817575378685644017)
              ·
                refine ⟨2112750613181534014233013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817000817575378685644017 2112750613181534014233013)
                ·
                  refine ⟨198070369985768813834345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112750613181534014233013 198070369985768813834345)
                  ·
                    rfl

theorem cell23_3471666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_3471666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471666 prefixEnd_3471666 := by exact prefixLift 3471666
  have htrace : WordTrace (prefixWord ++ tailWord_3471666) baseStart_3471666 baseEnd_3471666 := by
    simpa [prefixWord, tailWord_3471666, baseEnd_3471666] using wordTrace_append hprefix tailTrace_3471666
  have hstable : (prefixWord ++ tailWord_3471666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471666).length < 2 ^ (prefixWord ++ tailWord_3471666).sum := by decide
  have hdescent : baseEnd_3471666 < baseStart_3471666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471692 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_3471692 : Nat := 118140960795 + 3471692 * 2 ^ 59
def prefixEnd_3471692 : Nat := 4983230072969 + 3 ^ 40 * 3471692 * 2
def baseEnd_3471692 : Nat := 594215560122978740927995

theorem tailTrace_3471692 : CollatzResearch.WordTrace tailWord_3471692 prefixEnd_3471692 594215560122978740927995 := by
  unfold tailWord_3471692
  simp only [CollatzResearch.WordTrace]
  refine ⟨63311504869330138317056665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84415339825773517756075553 63311504869330138317056665)
  ·
    refine ⟨47483628651997603737792499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63311504869330138317056665 47483628651997603737792499)
    ·
      refine ⟨71225442977996405606688749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47483628651997603737792499 71225442977996405606688749)
      ·
        refine ⟨26709541116748652102508281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71225442977996405606688749 26709541116748652102508281)
        ·
          refine ⟨20032155837561489076881211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26709541116748652102508281 20032155837561489076881211)
          ·
            refine ⟨30048233756342233615321817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20032155837561489076881211 30048233756342233615321817)
            ·
              refine ⟨22536175317256675211491363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30048233756342233615321817 22536175317256675211491363)
              ·
                refine ⟨33804262975885012817237045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22536175317256675211491363 33804262975885012817237045)
                ·
                  refine ⟨3169149653989219951615973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33804262975885012817237045 3169149653989219951615973)
                  ·
                    refine ⟨594215560122978740927995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169149653989219951615973 594215560122978740927995)
                    ·
                      rfl

theorem cell23_3471692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_3471692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471692 prefixEnd_3471692 := by exact prefixLift 3471692
  have htrace : WordTrace (prefixWord ++ tailWord_3471692) baseStart_3471692 baseEnd_3471692 := by
    simpa [prefixWord, tailWord_3471692, baseEnd_3471692] using wordTrace_append hprefix tailTrace_3471692
  have hstable : (prefixWord ++ tailWord_3471692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471692).length < 2 ^ (prefixWord ++ tailWord_3471692).sum := by decide
  have hdescent : baseEnd_3471692 < baseStart_3471692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471719 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3471719 : Nat := 118140960795 + 3471719 * 2 ^ 59
def prefixEnd_3471719 : Nat := 4983230072969 + 3 ^ 40 * 3471719 * 2
def baseEnd_3471719 : Nat := 1782660544346607617146361

theorem tailTrace_3471719 : CollatzResearch.WordTrace tailWord_3471719 prefixEnd_3471719 1782660544346607617146361 := by
  unfold tailWord_3471719
  simp only [CollatzResearch.WordTrace]
  refine ⟨126623994509562460245346211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84415996339708306830230807 126623994509562460245346211)
  ·
    refine ⟨189935991764343690368019317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126623994509562460245346211 189935991764343690368019317)
    ·
      refine ⟨17806499227907220972001811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189935991764343690368019317 17806499227907220972001811)
      ·
        refine ⟨26709748841860831458002717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17806499227907220972001811 26709748841860831458002717)
        ·
          refine ⟨10016155815697811796751019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26709748841860831458002717 10016155815697811796751019)
          ·
            refine ⟨15024233723546717695126529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016155815697811796751019 15024233723546717695126529)
            ·
              refine ⟨11268175292660038271344897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15024233723546717695126529 11268175292660038271344897)
              ·
                refine ⟨8451131469495028703508673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11268175292660038271344897 8451131469495028703508673)
                ·
                  refine ⟨6338348602121271527631505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451131469495028703508673 6338348602121271527631505)
                  ·
                    refine ⟨4753761451590953645723629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6338348602121271527631505 4753761451590953645723629)
                    ·
                      refine ⟨1782660544346607617146361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753761451590953645723629 1782660544346607617146361)
                      ·
                        rfl

theorem cell23_3471719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3471719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471719 prefixEnd_3471719 := by exact prefixLift 3471719
  have htrace : WordTrace (prefixWord ++ tailWord_3471719) baseStart_3471719 baseEnd_3471719 := by
    simpa [prefixWord, tailWord_3471719, baseEnd_3471719] using wordTrace_append hprefix tailTrace_3471719
  have hstable : (prefixWord ++ tailWord_3471719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471719).length < 2 ^ (prefixWord ++ tailWord_3471719).sum := by decide
  have hdescent : baseEnd_3471719 < baseStart_3471719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471752 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_3471752 : Nat := 118140960795 + 3471752 * 2 ^ 59
def prefixEnd_3471752 : Nat := 4983230072969 + 3 ^ 40 * 3471752 * 2
def baseEnd_3471752 : Nat := 594225829736068662677903

theorem tailTrace_3471752 : CollatzResearch.WordTrace tailWord_3471752 prefixEnd_3471752 594225829736068662677903 := by
  unfold tailWord_3471752
  simp only [CollatzResearch.WordTrace]
  refine ⟨63312599059221453440648755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84416798745628604587531673 63312599059221453440648755)
  ·
    refine ⟨94968898588832180160973133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63312599059221453440648755 94968898588832180160973133)
    ·
      refine ⟨35613336970812067560364925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94968898588832180160973133 35613336970812067560364925)
      ·
        refine ⟨13355001364054525335136847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35613336970812067560364925 13355001364054525335136847)
        ·
          refine ⟨20032502046081788002705271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13355001364054525335136847 20032502046081788002705271)
          ·
            refine ⟨30048753069122682004057907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20032502046081788002705271 30048753069122682004057907)
            ·
              refine ⟨45073129603684023006086861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30048753069122682004057907 45073129603684023006086861)
              ·
                refine ⟨16902423601381508627282573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45073129603684023006086861 16902423601381508627282573)
                ·
                  refine ⟨6338408850518065735230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16902423601381508627282573 6338408850518065735230965)
                  ·
                    refine ⟨594225829736068662677903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6338408850518065735230965 594225829736068662677903)
                    ·
                      rfl

theorem cell23_3471752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_3471752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471752 prefixEnd_3471752 := by exact prefixLift 3471752
  have htrace : WordTrace (prefixWord ++ tailWord_3471752) baseStart_3471752 baseEnd_3471752 := by
    simpa [prefixWord, tailWord_3471752, baseEnd_3471752] using wordTrace_append hprefix tailTrace_3471752
  have hstable : (prefixWord ++ tailWord_3471752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471752).length < 2 ^ (prefixWord ++ tailWord_3471752).sum := by decide
  have hdescent : baseEnd_3471752 < baseStart_3471752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471783 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_3471783 : Nat := 118140960795 + 3471783 * 2 ^ 59
def prefixEnd_3471783 : Nat := 4983230072969 + 3 ^ 40 * 3471783 * 2
def baseEnd_3471783 : Nat := 1782693407108495366746067

theorem tailTrace_3471783 : CollatzResearch.WordTrace tailWord_3471783 prefixEnd_3471783 1782693407108495366746067 := by
  unfold tailWord_3471783
  simp only [CollatzResearch.WordTrace]
  refine ⟨126626328781330599175676003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84417552520887066117117335 126626328781330599175676003)
  ·
    refine ⟨189939493171995898763514005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126626328781330599175676003 189939493171995898763514005)
    ·
      refine ⟨8903413742437307754539719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189939493171995898763514005 8903413742437307754539719)
      ·
        refine ⟨13355120613655961631809579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903413742437307754539719 13355120613655961631809579)
        ·
          refine ⟨20032680920483942447714369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13355120613655961631809579 20032680920483942447714369)
          ·
            refine ⟨15024510690362956835785777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20032680920483942447714369 15024510690362956835785777)
            ·
              refine ⟨11268383017772217626839333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15024510690362956835785777 11268383017772217626839333)
              ·
                refine ⟨2112821815832290805032375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11268383017772217626839333 2112821815832290805032375)
                ·
                  refine ⟨3169232723748436207548563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112821815832290805032375 3169232723748436207548563)
                  ·
                    refine ⟨4753849085622654311322845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3169232723748436207548563 4753849085622654311322845)
                    ·
                      refine ⟨1782693407108495366746067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753849085622654311322845 1782693407108495366746067)
                      ·
                        rfl

theorem cell23_3471783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_3471783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471783 prefixEnd_3471783 := by exact prefixLift 3471783
  have htrace : WordTrace (prefixWord ++ tailWord_3471783) baseStart_3471783 baseEnd_3471783 := by
    simpa [prefixWord, tailWord_3471783, baseEnd_3471783] using wordTrace_append hprefix tailTrace_3471783
  have hstable : (prefixWord ++ tailWord_3471783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471783).length < 2 ^ (prefixWord ++ tailWord_3471783).sum := by decide
  have hdescent : baseEnd_3471783 < baseStart_3471783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471799 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 1, 6]
def baseStart_3471799 : Nat := 118140960795 + 3471799 * 2 ^ 59
def prefixEnd_3471799 : Nat := 4983230072969 + 3 ^ 40 * 3471799 * 2
def baseEnd_3471799 : Nat := 594233874266322434715331

theorem tailTrace_3471799 : CollatzResearch.WordTrace tailWord_3471799 prefixEnd_3471799 594233874266322434715331 := by
  unfold tailWord_3471799
  simp only [CollatzResearch.WordTrace]
  refine ⟨126626912349272633908258451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84417941566181755938838967 126626912349272633908258451)
  ·
    refine ⟨189940368523908950862387677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126626912349272633908258451 189940368523908950862387677)
    ·
      refine ⟨71227638196465856573395379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189940368523908950862387677 71227638196465856573395379)
      ·
        refine ⟨106841457294698784860093069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71227638196465856573395379 106841457294698784860093069)
        ·
          refine ⟨40065546485512044322534901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106841457294698784860093069 40065546485512044322534901)
          ·
            refine ⟨3756144983016754155237647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40065546485512044322534901 3756144983016754155237647)
            ·
              refine ⟨5634217474525131232856471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756144983016754155237647 5634217474525131232856471)
              ·
                refine ⟨8451326211787696849284707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5634217474525131232856471 8451326211787696849284707)
                ·
                  refine ⟨12676989317681545273927061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8451326211787696849284707 12676989317681545273927061)
                  ·
                    refine ⟨594233874266322434715331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12676989317681545273927061 594233874266322434715331)
                    ·
                      rfl

theorem cell23_3471799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_3471799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471799 prefixEnd_3471799 := by exact prefixLift 3471799
  have htrace : WordTrace (prefixWord ++ tailWord_3471799) baseStart_3471799 baseEnd_3471799 := by
    simpa [prefixWord, tailWord_3471799, baseEnd_3471799] using wordTrace_append hprefix tailTrace_3471799
  have hstable : (prefixWord ++ tailWord_3471799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471799).length < 2 ^ (prefixWord ++ tailWord_3471799).sum := by decide
  have hdescent : baseEnd_3471799 < baseStart_3471799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471840 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 1, 2, 2]
def baseStart_3471840 : Nat := 118140960795 + 3471840 * 2 ^ 59
def prefixEnd_3471840 : Nat := 4983230072969 + 3 ^ 40 * 3471840 * 2
def baseEnd_3471840 : Nat := 1782722675505801643733305

theorem tailTrace_3471840 : CollatzResearch.WordTrace tailWord_3471840 prefixEnd_3471840 1782722675505801643733305 := by
  unfold tailWord_3471840
  simp only [CollatzResearch.WordTrace]
  refine ⟨63314203871062048955250487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84418938494749398607000649 63314203871062048955250487)
  ·
    refine ⟨94971305806593073432875731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63314203871062048955250487 94971305806593073432875731)
    ·
      refine ⟨142456958709889610149313597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94971305806593073432875731 142456958709889610149313597)
      ·
        refine ⟨53421359516208603805992599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142456958709889610149313597 53421359516208603805992599)
        ·
          refine ⟨80132039274312905708988899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53421359516208603805992599 80132039274312905708988899)
          ·
            refine ⟨120198058911469358563483349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80132039274312905708988899 120198058911469358563483349)
            ·
              refine ⟨2817142005737563091331641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 120198058911469358563483349 2817142005737563091331641)
              ·
                refine ⟨2112856504303172318498731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817142005737563091331641 2112856504303172318498731)
                ·
                  refine ⟨3169284756454758477748097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112856504303172318498731 3169284756454758477748097)
                  ·
                    refine ⟨2376963567341068858311073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3169284756454758477748097 2376963567341068858311073)
                    ·
                      refine ⟨1782722675505801643733305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376963567341068858311073 1782722675505801643733305)
                      ·
                        rfl

theorem cell23_3471840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_3471840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471840 prefixEnd_3471840 := by exact prefixLift 3471840
  have htrace : WordTrace (prefixWord ++ tailWord_3471840) baseStart_3471840 baseEnd_3471840 := by
    simpa [prefixWord, tailWord_3471840, baseEnd_3471840] using wordTrace_append hprefix tailTrace_3471840
  have hstable : (prefixWord ++ tailWord_3471840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471840).length < 2 ^ (prefixWord ++ tailWord_3471840).sum := by decide
  have hdescent : baseEnd_3471840 < baseStart_3471840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471856 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 2, 1, 3]
def baseStart_3471856 : Nat := 118140960795 + 3471856 * 2 ^ 59
def prefixEnd_3471856 : Nat := 4983230072969 + 3 ^ 40 * 3471856 * 2
def baseEnd_3471856 : Nat := 1782730891196273581133231

theorem tailTrace_3471856 : CollatzResearch.WordTrace tailWord_3471856 prefixEnd_3471856 1782730891196273581133231 := by
  unfold tailWord_3471856
  simp only [CollatzResearch.WordTrace]
  refine ⟨63314495655033066321541711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84419327540044088428722281 63314495655033066321541711)
  ·
    refine ⟨94971743482549599482312567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63314495655033066321541711 94971743482549599482312567)
    ·
      refine ⟨142457615223824399223468851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94971743482549599482312567 142457615223824399223468851)
      ·
        refine ⟨213686422835736598835203277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142457615223824399223468851 213686422835736598835203277)
        ·
          refine ⟨80132408563401224563201229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213686422835736598835203277 80132408563401224563201229)
          ·
            refine ⟨30049653211275459211200461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80132408563401224563201229 30049653211275459211200461)
            ·
              refine ⟨11268619954228297204200173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30049653211275459211200461 11268619954228297204200173)
              ·
                refine ⟨4225732482835611451575065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11268619954228297204200173 4225732482835611451575065)
                ·
                  refine ⟨3169299362126708588681299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225732482835611451575065 3169299362126708588681299)
                  ·
                    refine ⟨4753949043190062883021949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3169299362126708588681299 4753949043190062883021949)
                    ·
                      refine ⟨1782730891196273581133231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753949043190062883021949 1782730891196273581133231)
                      ·
                        rfl

theorem cell23_3471856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_3471856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471856 prefixEnd_3471856 := by exact prefixLift 3471856
  have htrace : WordTrace (prefixWord ++ tailWord_3471856) baseStart_3471856 baseEnd_3471856 := by
    simpa [prefixWord, tailWord_3471856, baseEnd_3471856] using wordTrace_append hprefix tailTrace_3471856
  have hstable : (prefixWord ++ tailWord_3471856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471856).length < 2 ^ (prefixWord ++ tailWord_3471856).sum := by decide
  have hdescent : baseEnd_3471856 < baseStart_3471856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471866 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2]
def baseStart_3471866 : Nat := 118140960795 + 3471866 * 2 ^ 59
def prefixEnd_3471866 : Nat := 4983230072969 + 3 ^ 40 * 3471866 * 2
def baseEnd_3471866 : Nat := 1782736026002818542008185

theorem tailTrace_3471866 : CollatzResearch.WordTrace tailWord_3471866 prefixEnd_3471866 1782736026002818542008185 := by
  unfold tailWord_3471866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31657339010007476087736863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84419570693353269567298301 31657339010007476087736863)
  ·
    refine ⟨47486008515011214131605295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31657339010007476087736863 47486008515011214131605295)
    ·
      refine ⟨71229012772516821197407943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47486008515011214131605295 71229012772516821197407943)
      ·
        refine ⟨106843519158775231796111915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71229012772516821197407943 106843519158775231796111915)
        ·
          refine ⟨160265278738162847694167873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106843519158775231796111915 160265278738162847694167873)
          ·
            refine ⟨120198959053622135770625905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160265278738162847694167873 120198959053622135770625905)
            ·
              refine ⟨90149219290216601827969429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120198959053622135770625905 90149219290216601827969429)
              ·
                refine ⟨4225744654228903210686067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90149219290216601827969429 4225744654228903210686067)
                ·
                  refine ⟨6338616981343354816029101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225744654228903210686067 6338616981343354816029101)
                  ·
                    refine ⟨2376981368003758056010913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6338616981343354816029101 2376981368003758056010913)
                    ·
                      refine ⟨1782736026002818542008185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376981368003758056010913 1782736026002818542008185)
                      ·
                        rfl

theorem cell23_3471866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_3471866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471866 prefixEnd_3471866 := by exact prefixLift 3471866
  have htrace : WordTrace (prefixWord ++ tailWord_3471866) baseStart_3471866 baseEnd_3471866 := by
    simpa [prefixWord, tailWord_3471866, baseEnd_3471866] using wordTrace_append hprefix tailTrace_3471866
  have hstable : (prefixWord ++ tailWord_3471866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471866).length < 2 ^ (prefixWord ++ tailWord_3471866).sum := by decide
  have hdescent : baseEnd_3471866 < baseStart_3471866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471929 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3471929 : Nat := 118140960795 + 3471929 * 2 ^ 59
def prefixEnd_3471929 : Nat := 4983230072969 + 3 ^ 40 * 3471929 * 2
def baseEnd_3471929 : Nat := 1782768375284051795520395

theorem tailTrace_3471929 : CollatzResearch.WordTrace tailWord_3471929 prefixEnd_3471929 1782768375284051795520395 := by
  unfold tailWord_3471929
  simp only [CollatzResearch.WordTrace]
  refine ⟨126631653838801666110490841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84421102559201110740327227 126631653838801666110490841)
  ·
    refine ⟨94973740379101249582868131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126631653838801666110490841 94973740379101249582868131)
    ·
      refine ⟨142460610568651874374302197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94973740379101249582868131 142460610568651874374302197)
      ·
        refine ⟨13355682240811113222590831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142460610568651874374302197 13355682240811113222590831)
        ·
          refine ⟨20033523361216669833886247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13355682240811113222590831 20033523361216669833886247)
          ·
            refine ⟨30050285041825004750829371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20033523361216669833886247 30050285041825004750829371)
            ·
              refine ⟨45075427562737507126244057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30050285041825004750829371 45075427562737507126244057)
              ·
                refine ⟨33806570672053130344683043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45075427562737507126244057 33806570672053130344683043)
                ·
                  refine ⟨50709856008079695517024565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33806570672053130344683043 50709856008079695517024565)
                  ·
                    refine ⟨4754049000757471454721053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50709856008079695517024565 4754049000757471454721053)
                    ·
                      refine ⟨1782768375284051795520395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4754049000757471454721053 1782768375284051795520395)
                      ·
                        rfl

theorem cell23_3471929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3471929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471929 prefixEnd_3471929 := by exact prefixLift 3471929
  have htrace : WordTrace (prefixWord ++ tailWord_3471929) baseStart_3471929 baseEnd_3471929 := by
    simpa [prefixWord, tailWord_3471929, baseEnd_3471929] using wordTrace_append hprefix tailTrace_3471929
  have hstable : (prefixWord ++ tailWord_3471929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471929).length < 2 ^ (prefixWord ++ tailWord_3471929).sum := by decide
  have hdescent : baseEnd_3471929 < baseStart_3471929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471934 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3471934 : Nat := 118140960795 + 3471934 * 2 ^ 59
def prefixEnd_3471934 : Nat := 4983230072969 + 3 ^ 40 * 3471934 * 2
def baseEnd_3471934 : Nat := 1782770942687324275957873

theorem tailTrace_3471934 : CollatzResearch.WordTrace tailWord_3471934 prefixEnd_3471934 1782770942687324275957873 := by
  unfold tailWord_3471934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15828979525472943995552857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84421224135855701309615237 15828979525472943995552857)
  ·
    refine ⟨11871734644104707996664643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15828979525472943995552857 11871734644104707996664643)
    ·
      refine ⟨17807601966157061994996965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11871734644104707996664643 17807601966157061994996965)
      ·
        refine ⟨3338925368654449124061931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17807601966157061994996965 3338925368654449124061931)
        ·
          refine ⟨5008388052981673686092897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338925368654449124061931 5008388052981673686092897)
          ·
            refine ⟨3756291039736255264569673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5008388052981673686092897 3756291039736255264569673)
            ·
              refine ⟨2817218279802191448427255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756291039736255264569673 2817218279802191448427255)
              ·
                refine ⟨4225827419703287172640883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817218279802191448427255 4225827419703287172640883)
                ·
                  refine ⟨6338741129554930758961325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225827419703287172640883 6338741129554930758961325)
                  ·
                    refine ⟨2377027923583099034610497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6338741129554930758961325 2377027923583099034610497)
                    ·
                      refine ⟨1782770942687324275957873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377027923583099034610497 1782770942687324275957873)
                      ·
                        rfl

theorem cell23_3471934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3471934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471934 prefixEnd_3471934 := by exact prefixLift 3471934
  have htrace : WordTrace (prefixWord ++ tailWord_3471934) baseStart_3471934 baseEnd_3471934 := by
    simpa [prefixWord, tailWord_3471934, baseEnd_3471934] using wordTrace_append hprefix tailTrace_3471934
  have hstable : (prefixWord ++ tailWord_3471934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471934).length < 2 ^ (prefixWord ++ tailWord_3471934).sum := by decide
  have hdescent : baseEnd_3471934 < baseStart_3471934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471969 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3471969 : Nat := 118140960795 + 3471969 * 2 ^ 59
def prefixEnd_3471969 : Nat := 4983230072969 + 3 ^ 40 * 3471969 * 2
def baseEnd_3471969 : Nat := 1782788914510231639020211

theorem tailTrace_3471969 : CollatzResearch.WordTrace tailWord_3471969 prefixEnd_3471969 1782788914510231639020211 := by
  unfold tailWord_3471969
  simp only [CollatzResearch.WordTrace]
  refine ⟨126633112758656752941946961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84422075172437835294631307 126633112758656752941946961)
  ·
    refine ⟨94974834568992564706460221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126633112758656752941946961 94974834568992564706460221)
    ·
      refine ⟨35615562963372211764922583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94974834568992564706460221 35615562963372211764922583)
      ·
        refine ⟨53423344445058317647383875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35615562963372211764922583 53423344445058317647383875)
        ·
          refine ⟨80135016667587476471075813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53423344445058317647383875 80135016667587476471075813)
          ·
            refine ⟨15025315625172651838326715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80135016667587476471075813 15025315625172651838326715)
            ·
              refine ⟨22537973437758977757490073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15025315625172651838326715 22537973437758977757490073)
              ·
                refine ⟨16903480078319233318117555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22537973437758977757490073 16903480078319233318117555)
                ·
                  refine ⟨25355220117478849977176333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16903480078319233318117555 25355220117478849977176333)
                  ·
                    refine ⟨9508207544054568741441125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25355220117478849977176333 9508207544054568741441125)
                    ·
                      refine ⟨1782788914510231639020211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9508207544054568741441125 1782788914510231639020211)
                      ·
                        rfl

theorem cell23_3471969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3471969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471969 prefixEnd_3471969 := by exact prefixLift 3471969
  have htrace : WordTrace (prefixWord ++ tailWord_3471969) baseStart_3471969 baseEnd_3471969 := by
    simpa [prefixWord, tailWord_3471969, baseEnd_3471969] using wordTrace_append hprefix tailTrace_3471969
  have hstable : (prefixWord ++ tailWord_3471969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471969).length < 2 ^ (prefixWord ++ tailWord_3471969).sum := by decide
  have hdescent : baseEnd_3471969 < baseStart_3471969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471979 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 5, 4]
def baseStart_3471979 : Nat := 118140960795 + 3471979 * 2 ^ 59
def prefixEnd_3471979 : Nat := 4983230072969 + 3 ^ 40 * 3471979 * 2
def baseEnd_3471979 : Nat := 594264683105592199965055

theorem tailTrace_3471979 : CollatzResearch.WordTrace tailWord_3471979 prefixEnd_3471979 594264683105592199965055 := by
  unfold tailWord_3471979
  simp only [CollatzResearch.WordTrace]
  refine ⟨126633477488620524649810991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84422318325747016433207327 126633477488620524649810991)
  ·
    refine ⟨189950216232930786974716487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126633477488620524649810991 189950216232930786974716487)
    ·
      refine ⟨284925324349396180462074731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189950216232930786974716487 284925324349396180462074731)
      ·
        refine ⟨427387986524094270693112097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284925324349396180462074731 427387986524094270693112097)
        ·
          refine ⟨320540989893070703019834073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427387986524094270693112097 320540989893070703019834073)
          ·
            refine ⟨240405742419803027264875555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320540989893070703019834073 240405742419803027264875555)
            ·
              refine ⟨360608613629704540897313333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240405742419803027264875555 360608613629704540897313333)
              ·
                refine ⟨33807057527784800709123125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 360608613629704540897313333 33807057527784800709123125)
                ·
                  refine ⟨3169411643229825066480293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33807057527784800709123125 3169411643229825066480293)
                  ·
                    refine ⟨594264683105592199965055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169411643229825066480293 594264683105592199965055)
                    ·
                      rfl

theorem cell23_3471979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 4].length) (baseStart_3471979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471979 prefixEnd_3471979 := by exact prefixLift 3471979
  have htrace : WordTrace (prefixWord ++ tailWord_3471979) baseStart_3471979 baseEnd_3471979 := by
    simpa [prefixWord, tailWord_3471979, baseEnd_3471979] using wordTrace_append hprefix tailTrace_3471979
  have hstable : (prefixWord ++ tailWord_3471979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471979).length < 2 ^ (prefixWord ++ tailWord_3471979).sum := by decide
  have hdescent : baseEnd_3471979 < baseStart_3471979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472009 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 6]
def baseStart_3472009 : Nat := 118140960795 + 3472009 * 2 ^ 59
def prefixEnd_3472009 : Nat := 4983230072969 + 3 ^ 40 * 3472009 * 2
def baseEnd_3472009 : Nat := 198089939304045720280003

theorem tailTrace_3472009 : CollatzResearch.WordTrace tailWord_3472009 prefixEnd_3472009 198089939304045720280003 := by
  unfold tailWord_3472009
  simp only [CollatzResearch.WordTrace]
  refine ⟨126634571678511839773403081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84423047785674559848935387 126634571678511839773403081)
  ·
    refine ⟨94975928758883879830052311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126634571678511839773403081 94975928758883879830052311)
    ·
      refine ⟨142463893138325819745078467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94975928758883879830052311 142463893138325819745078467)
      ·
        refine ⟨213695839707488729617617701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142463893138325819745078467 213695839707488729617617701)
        ·
          refine ⟨40067969945154136803303319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213695839707488729617617701 40067969945154136803303319)
          ·
            refine ⟨60101954917731205204954979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40067969945154136803303319 60101954917731205204954979)
            ·
              refine ⟨90152932376596807807432469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60101954917731205204954979 90152932376596807807432469)
              ·
                refine ⟨4225918705152975365973397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90152932376596807807432469 4225918705152975365973397)
                ·
                  refine ⟨198089939304045720280003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4225918705152975365973397 198089939304045720280003)
                  ·
                    rfl

theorem cell23_3472009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_3472009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472009 prefixEnd_3472009 := by exact prefixLift 3472009
  have htrace : WordTrace (prefixWord ++ tailWord_3472009) baseStart_3472009 baseEnd_3472009 := by
    simpa [prefixWord, tailWord_3472009, baseEnd_3472009] using wordTrace_append hprefix tailTrace_3472009
  have hstable : (prefixWord ++ tailWord_3472009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472009).length < 2 ^ (prefixWord ++ tailWord_3472009).sum := by decide
  have hdescent : baseEnd_3472009 < baseStart_3472009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472029 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3472029 : Nat := 118140960795 + 3472029 * 2 ^ 59
def prefixEnd_3472029 : Nat := 4983230072969 + 3 ^ 40 * 3472029 * 2
def baseEnd_3472029 : Nat := 1782819723349501404269935

theorem tailTrace_3472029 : CollatzResearch.WordTrace tailWord_3472029 prefixEnd_3472029 1782819723349501404269935 := by
  unfold tailWord_3472029
  simp only [CollatzResearch.WordTrace]
  refine ⟨126635301138439383189131141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84423534092292922126087427 126635301138439383189131141)
  ·
    refine ⟨23744118963457384347962089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126635301138439383189131141 23744118963457384347962089)
    ·
      refine ⟨17808089222593038260971567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23744118963457384347962089 17808089222593038260971567)
      ·
        refine ⟨26712133833889557391457351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17808089222593038260971567 26712133833889557391457351)
        ·
          refine ⟨40068200750834336087186027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26712133833889557391457351 40068200750834336087186027)
          ·
            refine ⟨60102301126251504130779041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40068200750834336087186027 60102301126251504130779041)
            ·
              refine ⟨45076725844688628098084281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60102301126251504130779041 45076725844688628098084281)
              ·
                refine ⟨33807544383516471073563211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45076725844688628098084281 33807544383516471073563211)
                ·
                  refine ⟨50711316575274706610344817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33807544383516471073563211 50711316575274706610344817)
                  ·
                    refine ⟨38033487431456029957758613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50711316575274706610344817 38033487431456029957758613)
                    ·
                      refine ⟨1782819723349501404269935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38033487431456029957758613 1782819723349501404269935)
                      ·
                        rfl

theorem cell23_3472029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3472029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472029 prefixEnd_3472029 := by exact prefixLift 3472029
  have htrace : WordTrace (prefixWord ++ tailWord_3472029) baseStart_3472029 baseEnd_3472029 := by
    simpa [prefixWord, tailWord_3472029, baseEnd_3472029] using wordTrace_append hprefix tailTrace_3472029
  have hstable : (prefixWord ++ tailWord_3472029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472029).length < 2 ^ (prefixWord ++ tailWord_3472029).sum := by decide
  have hdescent : baseEnd_3472029 < baseStart_3472029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472063 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 2, 3, 2]
def baseStart_3472063 : Nat := 118140960795 + 3472063 * 2 ^ 59
def prefixEnd_3472063 : Nat := 4983230072969 + 3 ^ 40 * 3472063 * 2
def baseEnd_3472063 : Nat := 1782837181691754271244779

theorem tailTrace_3472063 : CollatzResearch.WordTrace tailWord_3472063 prefixEnd_3472063 1782837181691754271244779 := by
  unfold tailWord_3472063
  simp only [CollatzResearch.WordTrace]
  refine ⟨126636541220316206995868843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84424360813544137997245895 126636541220316206995868843)
  ·
    refine ⟨189954811830474310493803265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126636541220316206995868843 189954811830474310493803265)
    ·
      refine ⟨142466108872855732870352449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189954811830474310493803265 142466108872855732870352449)
      ·
        refine ⟨106849581654641799652764337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142466108872855732870352449 106849581654641799652764337)
        ·
          refine ⟨80137186240981349739573253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106849581654641799652764337 80137186240981349739573253)
          ·
            refine ⟨15025722420184003076169985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80137186240981349739573253 15025722420184003076169985)
            ·
              refine ⟨11269291815138002307127489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15025722420184003076169985 11269291815138002307127489)
              ·
                refine ⟨8451968861353501730345617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11269291815138002307127489 8451968861353501730345617)
                ·
                  refine ⟨6338976646015126297759213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451968861353501730345617 6338976646015126297759213)
                  ·
                    refine ⟨2377116242255672361659705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6338976646015126297759213 2377116242255672361659705)
                    ·
                      refine ⟨1782837181691754271244779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377116242255672361659705 1782837181691754271244779)
                      ·
                        rfl

theorem cell23_3472063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_3472063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472063 prefixEnd_3472063 := by exact prefixLift 3472063
  have htrace : WordTrace (prefixWord ++ tailWord_3472063) baseStart_3472063 baseEnd_3472063 := by
    simpa [prefixWord, tailWord_3472063, baseEnd_3472063] using wordTrace_append hprefix tailTrace_3472063
  have hstable : (prefixWord ++ tailWord_3472063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472063).length < 2 ^ (prefixWord ++ tailWord_3472063).sum := by decide
  have hdescent : baseEnd_3472063 < baseStart_3472063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472110 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_3472110 : Nat := 118140960795 + 3472110 * 2 ^ 59
def prefixEnd_3472110 : Nat := 4983230072969 + 3 ^ 40 * 3472110 * 2
def baseEnd_3472110 : Nat := 1782861315282515587357063

theorem tailTrace_3472110 : CollatzResearch.WordTrace tailWord_3472110 prefixEnd_3472110 1782861315282515587357063 := by
  unfold tailWord_3472110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15829781931393241752853723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84425503634097289348553189 15829781931393241752853723)
  ·
    refine ⟨23744672897089862629280585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15829781931393241752853723 23744672897089862629280585)
    ·
      refine ⟨17808504672817396971960439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23744672897089862629280585 17808504672817396971960439)
      ·
        refine ⟨26712757009226095457940659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17808504672817396971960439 26712757009226095457940659)
        ·
          refine ⟨40069135513839143186910989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26712757009226095457940659 40069135513839143186910989)
          ·
            refine ⟨15025925817689678695091621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40069135513839143186910989 15025925817689678695091621)
            ·
              refine ⟨2817361090816814755329679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15025925817689678695091621 2817361090816814755329679)
              ·
                refine ⟨4226041636225222132994519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817361090816814755329679 4226041636225222132994519)
                ·
                  refine ⟨6339062454337833199491779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4226041636225222132994519 6339062454337833199491779)
                  ·
                    refine ⟨9508593681506749799237669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6339062454337833199491779 9508593681506749799237669)
                    ·
                      refine ⟨1782861315282515587357063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9508593681506749799237669 1782861315282515587357063)
                      ·
                        rfl

theorem cell23_3472110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_3472110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472110 prefixEnd_3472110 := by exact prefixLift 3472110
  have htrace : WordTrace (prefixWord ++ tailWord_3472110) baseStart_3472110 baseEnd_3472110 := by
    simpa [prefixWord, tailWord_3472110, baseEnd_3472110] using wordTrace_append hprefix tailTrace_3472110
  have hstable : (prefixWord ++ tailWord_3472110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472110).length < 2 ^ (prefixWord ++ tailWord_3472110).sum := by decide
  have hdescent : baseEnd_3472110 < baseStart_3472110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472113 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_3472113 : Nat := 118140960795 + 3472113 * 2 ^ 59
def prefixEnd_3472113 : Nat := 4983230072969 + 3 ^ 40 * 3472113 * 2
def baseEnd_3472113 : Nat := 1782862855724479075619549

theorem tailTrace_3472113 : CollatzResearch.WordTrace tailWord_3472113 prefixEnd_3472113 1782862855724479075619549 := by
  unfold tailWord_3472113
  simp only [CollatzResearch.WordTrace]
  refine ⟨126638364870135065535188993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84425576580090043690125995 126638364870135065535188993)
  ·
    refine ⟨94978773652601299151391745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126638364870135065535188993 94978773652601299151391745)
    ·
      refine ⟨71234080239450974363543809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94978773652601299151391745 71234080239450974363543809)
      ·
        refine ⟨53425560179588230772657857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71234080239450974363543809 53425560179588230772657857)
        ·
          refine ⟨40069170134691173079493393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53425560179588230772657857 40069170134691173079493393)
          ·
            refine ⟨30051877601018379809620045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40069170134691173079493393 30051877601018379809620045)
            ·
              refine ⟨11269454100381892428607517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30051877601018379809620045 11269454100381892428607517)
              ·
                refine ⟨4226045287643209660727819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11269454100381892428607517 4226045287643209660727819)
                ·
                  refine ⟨6339067931464814491091729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4226045287643209660727819 6339067931464814491091729)
                  ·
                    refine ⟨4754300948598610868318797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6339067931464814491091729 4754300948598610868318797)
                    ·
                      refine ⟨1782862855724479075619549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4754300948598610868318797 1782862855724479075619549)
                      ·
                        rfl

theorem cell23_3472113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_3472113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472113 prefixEnd_3472113 := by exact prefixLift 3472113
  have htrace : WordTrace (prefixWord ++ tailWord_3472113) baseStart_3472113 baseEnd_3472113 := by
    simpa [prefixWord, tailWord_3472113, baseEnd_3472113] using wordTrace_append hprefix tailTrace_3472113
  have hstable : (prefixWord ++ tailWord_3472113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472113).length < 2 ^ (prefixWord ++ tailWord_3472113).sum := by decide
  have hdescent : baseEnd_3472113 < baseStart_3472113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472119 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_3472119 : Nat := 118140960795 + 3472119 * 2 ^ 59
def prefixEnd_3472119 : Nat := 4983230072969 + 3 ^ 40 * 3472119 * 2
def baseEnd_3472119 : Nat := 1782865936608406052144521

theorem tailTrace_3472119 : CollatzResearch.WordTrace tailWord_3472119 prefixEnd_3472119 1782865936608406052144521 := by
  unfold tailWord_3472119
  simp only [CollatzResearch.WordTrace]
  refine ⟨126638583708113328559907411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84425722472075552373271607 126638583708113328559907411)
  ·
    refine ⟨189957875562169992839861117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126638583708113328559907411 189957875562169992839861117)
    ·
      refine ⟨71234203335813747314947919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189957875562169992839861117 71234203335813747314947919)
      ·
        refine ⟨106851305003720620972421879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71234203335813747314947919 106851305003720620972421879)
        ·
          refine ⟨160276957505580931458632819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106851305003720620972421879 160276957505580931458632819)
          ·
            refine ⟨240415436258371397187949229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160276957505580931458632819 240415436258371397187949229)
            ·
              refine ⟨90155788596889273945480961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240415436258371397187949229 90155788596889273945480961)
              ·
                refine ⟨67616841447666955459110721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90155788596889273945480961 67616841447666955459110721)
                ·
                  refine ⟨50712631085750216594333041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67616841447666955459110721 50712631085750216594333041)
                  ·
                    refine ⟨38034473314312662445749781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50712631085750216594333041 38034473314312662445749781)
                    ·
                      refine ⟨1782865936608406052144521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38034473314312662445749781 1782865936608406052144521)
                      ·
                        rfl

theorem cell23_3472119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_3472119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472119 prefixEnd_3472119 := by exact prefixLift 3472119
  have htrace : WordTrace (prefixWord ++ tailWord_3472119) baseStart_3472119 baseEnd_3472119 := by
    simpa [prefixWord, tailWord_3472119, baseEnd_3472119] using wordTrace_append hprefix tailTrace_3472119
  have hstable : (prefixWord ++ tailWord_3472119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472119).length < 2 ^ (prefixWord ++ tailWord_3472119).sum := by decide
  have hdescent : baseEnd_3472119 < baseStart_3472119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472156 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3472156 : Nat := 118140960795 + 3472156 * 2 ^ 59
def prefixEnd_3472156 : Nat := 4983230072969 + 3 ^ 40 * 3472156 * 2
def baseEnd_3472156 : Nat := 1782884935392622407381851

theorem tailTrace_3472156 : CollatzResearch.WordTrace tailWord_3472156 prefixEnd_3472156 1782884935392622407381851 := by
  unfold tailWord_3472156
  simp only [CollatzResearch.WordTrace]
  refine ⟨63319966604489641939502161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84426622139319522586002881 63319966604489641939502161)
  ·
    refine ⟨47489974953367231454626621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63319966604489641939502161 47489974953367231454626621)
    ·
      refine ⟨17808740607512711795484983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47489974953367231454626621 17808740607512711795484983)
      ·
        refine ⟨26713110911269067693227475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17808740607512711795484983 26713110911269067693227475)
        ·
          refine ⟨40069666366903601539841213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26713110911269067693227475 40069666366903601539841213)
          ·
            refine ⟨15026124887588850577440455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40069666366903601539841213 15026124887588850577440455)
            ·
              refine ⟨22539187331383275866160683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15026124887588850577440455 22539187331383275866160683)
              ·
                refine ⟨33808780997074913799241025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22539187331383275866160683 33808780997074913799241025)
                ·
                  refine ⟨25356585747806185349430769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33808780997074913799241025 25356585747806185349430769)
                  ·
                    refine ⟨19017439310854639012073077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25356585747806185349430769 19017439310854639012073077)
                    ·
                      refine ⟨1782884935392622407381851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19017439310854639012073077 1782884935392622407381851)
                      ·
                        rfl

theorem cell23_3472156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3472156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472156 prefixEnd_3472156 := by exact prefixLift 3472156
  have htrace : WordTrace (prefixWord ++ tailWord_3472156) baseStart_3472156 baseEnd_3472156 := by
    simpa [prefixWord, tailWord_3472156, baseEnd_3472156] using wordTrace_append hprefix tailTrace_3472156
  have hstable : (prefixWord ++ tailWord_3472156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472156).length < 2 ^ (prefixWord ++ tailWord_3472156).sum := by decide
  have hdescent : baseEnd_3472156 < baseStart_3472156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472206 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_3472206 : Nat := 118140960795 + 3472206 * 2 ^ 59
def prefixEnd_3472206 : Nat := 4983230072969 + 3 ^ 40 * 3472206 * 2
def baseEnd_3472206 : Nat := 198101178825038579084069

theorem tailTrace_3472206 : CollatzResearch.WordTrace tailWord_3472206 prefixEnd_3472206 198101178825038579084069 := by
  unfold tailWord_3472206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830219607349767802290559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84427837905865428278882981 15830219607349767802290559)
  ·
    refine ⟨23745329411024651703435839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15830219607349767802290559 23745329411024651703435839)
    ·
      refine ⟨35617994116536977555153759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23745329411024651703435839 35617994116536977555153759)
      ·
        refine ⟨53426991174805466332730639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35617994116536977555153759 53426991174805466332730639)
        ·
          refine ⟨80140486762208199499095959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53426991174805466332730639 80140486762208199499095959)
          ·
            refine ⟨120210730143312299248643939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80140486762208199499095959 120210730143312299248643939)
            ·
              refine ⟨180316095214968448872965909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120210730143312299248643939 180316095214968448872965909)
              ·
                refine ⟨8452316963201646040920277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180316095214968448872965909 8452316963201646040920277)
                ·
                  refine ⟨198101178825038579084069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8452316963201646040920277 198101178825038579084069)
                  ·
                    rfl

theorem cell23_3472206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_3472206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472206 prefixEnd_3472206 := by exact prefixLift 3472206
  have htrace : WordTrace (prefixWord ++ tailWord_3472206) baseStart_3472206 baseEnd_3472206 := by
    simpa [prefixWord, tailWord_3472206, baseEnd_3472206] using wordTrace_append hprefix tailTrace_3472206
  have hstable : (prefixWord ++ tailWord_3472206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472206).length < 2 ^ (prefixWord ++ tailWord_3472206).sum := by decide
  have hdescent : baseEnd_3472206 < baseStart_3472206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472223 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 5]
def baseStart_3472223 : Nat := 118140960795 + 3472223 * 2 ^ 59
def prefixEnd_3472223 : Nat := 4983230072969 + 3 ^ 40 * 3472223 * 2
def baseEnd_3472223 : Nat := 198102148732941516138227

theorem tailTrace_3472223 : CollatzResearch.WordTrace tailWord_3472223 prefixEnd_3472223 198102148732941516138227 := by
  unfold tailWord_3472223
  simp only [CollatzResearch.WordTrace]
  refine ⟨126642376899736554321693323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84428251266491036214462215 126642376899736554321693323)
  ·
    refine ⟨189963565349604831482539985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126642376899736554321693323 189963565349604831482539985)
    ·
      refine ⟨142472674012203623611904989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189963565349604831482539985 142472674012203623611904989)
      ·
        refine ⟨53427252754576358854464371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142472674012203623611904989 53427252754576358854464371)
        ·
          refine ⟨80140879131864538281696557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53427252754576358854464371 80140879131864538281696557)
          ·
            refine ⟨30052829674449201855636209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80140879131864538281696557 30052829674449201855636209)
            ·
              refine ⟨22539622255836901391727157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30052829674449201855636209 22539622255836901391727157)
              ·
                refine ⟨2113089586484709505474421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22539622255836901391727157 2113089586484709505474421)
                ·
                  refine ⟨198102148732941516138227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113089586484709505474421 198102148732941516138227)
                  ·
                    rfl

theorem cell23_3472223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 5].length) (baseStart_3472223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472223 prefixEnd_3472223 := by exact prefixLift 3472223
  have htrace : WordTrace (prefixWord ++ tailWord_3472223) baseStart_3472223 baseEnd_3472223 := by
    simpa [prefixWord, tailWord_3472223, baseEnd_3472223] using wordTrace_append hprefix tailTrace_3472223
  have hstable : (prefixWord ++ tailWord_3472223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472223).length < 2 ^ (prefixWord ++ tailWord_3472223).sum := by decide
  have hdescent : baseEnd_3472223 < baseStart_3472223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472240 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 5]
def baseStart_3472240 : Nat := 118140960795 + 3472240 * 2 ^ 59
def prefixEnd_3472240 : Nat := 4983230072969 + 3 ^ 40 * 3472240 * 2
def baseEnd_3472240 : Nat := 198103118640844453192385

theorem tailTrace_3472240 : CollatzResearch.WordTrace tailWord_3472240 prefixEnd_3472240 198103118640844453192385 := by
  unfold tailWord_3472240
  simp only [CollatzResearch.WordTrace]
  refine ⟨63321498470337483112531087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84428664627116644150041449 63321498470337483112531087)
  ·
    refine ⟨94982247705506224668796631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63321498470337483112531087 94982247705506224668796631)
    ·
      refine ⟨142473371558259337003194947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94982247705506224668796631 142473371558259337003194947)
      ·
        refine ⟨213710057337389005504792421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142473371558259337003194947 213710057337389005504792421)
        ·
          refine ⟨40070635750760438532148579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213710057337389005504792421 40070635750760438532148579)
          ·
            refine ⟨60105953626140657798222869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40070635750760438532148579 60105953626140657798222869)
            ·
              refine ⟨2817466576225343334291697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60105953626140657798222869 2817466576225343334291697)
              ·
                refine ⟨2113099932169007500718773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817466576225343334291697 2113099932169007500718773)
                ·
                  refine ⟨198103118640844453192385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113099932169007500718773 198103118640844453192385)
                  ·
                    rfl

theorem cell23_3472240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 5].length) (baseStart_3472240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472240 prefixEnd_3472240 := by exact prefixLift 3472240
  have htrace : WordTrace (prefixWord ++ tailWord_3472240) baseStart_3472240 baseEnd_3472240 := by
    simpa [prefixWord, tailWord_3472240, baseEnd_3472240] using wordTrace_append hprefix tailTrace_3472240
  have hstable : (prefixWord ++ tailWord_3472240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472240).length < 2 ^ (prefixWord ++ tailWord_3472240).sum := by decide
  have hdescent : baseEnd_3472240 < baseStart_3472240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472243 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 2, 5, 2]
def baseStart_3472243 : Nat := 118140960795 + 3472243 * 2 ^ 59
def prefixEnd_3472243 : Nat := 4983230072969 + 3 ^ 40 * 3472243 * 2
def baseEnd_3472243 : Nat := 1782929608209563566993951

theorem tailTrace_3472243 : CollatzResearch.WordTrace tailWord_3472243 prefixEnd_3472243 1782929608209563566993951 := by
  unfold tailWord_3472243
  simp only [CollatzResearch.WordTrace]
  refine ⟨126643106359664097737421383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84428737573109398491614255 126643106359664097737421383)
  ·
    refine ⟨189964659539496146606132075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126643106359664097737421383 189964659539496146606132075)
    ·
      refine ⟨284946989309244219909198113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189964659539496146606132075 284946989309244219909198113)
      ·
        refine ⟨213710241981933164931898585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284946989309244219909198113 213710241981933164931898585)
        ·
          refine ⟨160282681486449873698923939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213710241981933164931898585 160282681486449873698923939)
          ·
            refine ⟨240424022229674810548385909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160282681486449873698923939 240424022229674810548385909)
            ·
              refine ⟨22539752084032013488911179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240424022229674810548385909 22539752084032013488911179)
              ·
                refine ⟨33809628126048020233366769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22539752084032013488911179 33809628126048020233366769)
                ·
                  refine ⟨25357221094536015175025077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33809628126048020233366769 25357221094536015175025077)
                  ·
                    refine ⟨2377239477612751422658601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25357221094536015175025077 2377239477612751422658601)
                    ·
                      refine ⟨1782929608209563566993951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377239477612751422658601 1782929608209563566993951)
                      ·
                        rfl

theorem cell23_3472243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5, 2].length) (baseStart_3472243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472243 prefixEnd_3472243 := by exact prefixLift 3472243
  have htrace : WordTrace (prefixWord ++ tailWord_3472243) baseStart_3472243 baseEnd_3472243 := by
    simpa [prefixWord, tailWord_3472243, baseEnd_3472243] using wordTrace_append hprefix tailTrace_3472243
  have hstable : (prefixWord ++ tailWord_3472243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472243).length < 2 ^ (prefixWord ++ tailWord_3472243).sum := by decide
  have hdescent : baseEnd_3472243 < baseStart_3472243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472273 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 6, 2]
def baseStart_3472273 : Nat := 118140960795 + 3472273 * 2 ^ 59
def prefixEnd_3472273 : Nat := 4983230072969 + 3 ^ 40 * 3472273 * 2
def baseEnd_3472273 : Nat := 1782945012629198449618813

theorem tailTrace_3472273 : CollatzResearch.WordTrace tailWord_3472273 prefixEnd_3472273 1782945012629198449618813 := by
  unfold tailWord_3472273
  simp only [CollatzResearch.WordTrace]
  refine ⟨126644200549555412861013473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84429467033036941907342315 126644200549555412861013473)
  ·
    refine ⟨94983150412166559645760105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126644200549555412861013473 94983150412166559645760105)
    ·
      refine ⟨71237362809124919734320079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94983150412166559645760105 71237362809124919734320079)
      ·
        refine ⟨106856044213687379601480119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71237362809124919734320079 106856044213687379601480119)
        ·
          refine ⟨160284066320531069402220179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106856044213687379601480119 160284066320531069402220179)
          ·
            refine ⟨240426099480796604103330269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160284066320531069402220179 240426099480796604103330269)
            ·
              refine ⟨90159787305298726538748851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240426099480796604103330269 90159787305298726538748851)
              ·
                refine ⟨135239680957948089808123277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90159787305298726538748851 135239680957948089808123277)
                ·
                  refine ⟨50714880359230533678046229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135239680957948089808123277 50714880359230533678046229)
                  ·
                    refine ⟨2377260016838931266158417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50714880359230533678046229 2377260016838931266158417)
                    ·
                      refine ⟨1782945012629198449618813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377260016838931266158417 1782945012629198449618813)
                      ·
                        rfl

theorem cell23_3472273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_3472273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472273 prefixEnd_3472273 := by exact prefixLift 3472273
  have htrace : WordTrace (prefixWord ++ tailWord_3472273) baseStart_3472273 baseEnd_3472273 := by
    simpa [prefixWord, tailWord_3472273, baseEnd_3472273] using wordTrace_append hprefix tailTrace_3472273
  have hstable : (prefixWord ++ tailWord_3472273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472273).length < 2 ^ (prefixWord ++ tailWord_3472273).sum := by decide
  have hdescent : baseEnd_3472273 < baseStart_3472273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472334 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_3472334 : Nat := 118140960795 + 3472334 * 2 ^ 59
def prefixEnd_3472334 : Nat := 4983230072969 + 3 ^ 40 * 3472334 * 2
def baseEnd_3472334 : Nat := 594325444983040903652011

theorem tailTrace_3472334 : CollatzResearch.WordTrace tailWord_3472334 prefixEnd_3472334 594325444983040903652011 := by
  unfold tailWord_3472334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830803175291802534873007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84430950268222946852656037 15830803175291802534873007)
  ·
    refine ⟨23746204762937703802309511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15830803175291802534873007 23746204762937703802309511)
    ·
      refine ⟨35619307144406555703464267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23746204762937703802309511 35619307144406555703464267)
      ·
        refine ⟨53428960716609833555196401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35619307144406555703464267 53428960716609833555196401)
        ·
          refine ⟨40071720537457375166397301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53428960716609833555196401 40071720537457375166397301)
          ·
            refine ⟨3756723800386628921849747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40071720537457375166397301 3756723800386628921849747)
            ·
              refine ⟨5635085700579943382774621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756723800386628921849747 5635085700579943382774621)
              ·
                refine ⟨2113157137717478768540483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5635085700579943382774621 2113157137717478768540483)
                ·
                  refine ⟨3169735706576218152810725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113157137717478768540483 3169735706576218152810725)
                  ·
                    refine ⟨594325444983040903652011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169735706576218152810725 594325444983040903652011)
                    ·
                      rfl

theorem cell23_3472334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_3472334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472334 prefixEnd_3472334 := by exact prefixLift 3472334
  have htrace : WordTrace (prefixWord ++ tailWord_3472334) baseStart_3472334 baseEnd_3472334 := by
    simpa [prefixWord, tailWord_3472334, baseEnd_3472334] using wordTrace_append hprefix tailTrace_3472334
  have hstable : (prefixWord ++ tailWord_3472334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472334).length < 2 ^ (prefixWord ++ tailWord_3472334).sum := by decide
  have hdescent : baseEnd_3472334 < baseStart_3472334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472380 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3472380 : Nat := 118140960795 + 3472380 * 2 ^ 59
def prefixEnd_3472380 : Nat := 4983230072969 + 3 ^ 40 * 3472380 * 2
def baseEnd_3472380 : Nat := 1782999955059229530980821

theorem tailTrace_3472380 : CollatzResearch.WordTrace tailWord_3472380 prefixEnd_3472380 1782999955059229530980821 := by
  unfold tailWord_3472380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63324051580083885067579297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84432068773445180090105729 63324051580083885067579297)
  ·
    refine ⟨47493038685062913800684473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63324051580083885067579297 47493038685062913800684473)
    ·
      refine ⟨35619779013797185350513355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47493038685062913800684473 35619779013797185350513355)
      ·
        refine ⟨53429668520695778025770033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35619779013797185350513355 53429668520695778025770033)
        ·
          refine ⟨40072251390521833519327525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53429668520695778025770033 40072251390521833519327525)
          ·
            refine ⟨7513547135722843784873911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40072251390521833519327525 7513547135722843784873911)
            ·
              refine ⟨11270320703584265677310867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7513547135722843784873911 11270320703584265677310867)
              ·
                refine ⟨16905481055376398515966301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11270320703584265677310867 16905481055376398515966301)
                ·
                  refine ⟨6339555395766149443487363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16905481055376398515966301 6339555395766149443487363)
                  ·
                    refine ⟨9509333093649224165231045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6339555395766149443487363 9509333093649224165231045)
                    ·
                      refine ⟨1782999955059229530980821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9509333093649224165231045 1782999955059229530980821)
                      ·
                        rfl

theorem cell23_3472380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3472380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472380 prefixEnd_3472380 := by exact prefixLift 3472380
  have htrace : WordTrace (prefixWord ++ tailWord_3472380) baseStart_3472380 baseEnd_3472380 := by
    simpa [prefixWord, tailWord_3472380, baseEnd_3472380] using wordTrace_append hprefix tailTrace_3472380
  have hstable : (prefixWord ++ tailWord_3472380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472380).length < 2 ^ (prefixWord ++ tailWord_3472380).sum := by decide
  have hdescent : baseEnd_3472380 < baseStart_3472380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472402 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3472402 : Nat := 118140960795 + 3472402 * 2 ^ 59
def prefixEnd_3472402 : Nat := 4983230072969 + 3 ^ 40 * 3472402 * 2
def baseEnd_3472402 : Nat := 594337083877876148301907

theorem tailTrace_3472402 : CollatzResearch.WordTrace tailWord_3472402 prefixEnd_3472402 594337083877876148301907 := by
  unfold tailWord_3472402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31662226391522016973114865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84432603710725378594972973 31662226391522016973114865)
  ·
    refine ⟨23746669793641512729836149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31662226391522016973114865 23746669793641512729836149)
    ·
      refine ⟨2226250293153891818422139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23746669793641512729836149 2226250293153891818422139)
      ·
        refine ⟨3339375439730837727633209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226250293153891818422139 3339375439730837727633209)
        ·
          refine ⟨2504531579798128295724907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3339375439730837727633209 2504531579798128295724907)
          ·
            refine ⟨3756797369697192443587361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504531579798128295724907 3756797369697192443587361)
            ·
              refine ⟨2817598027272894332690521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756797369697192443587361 2817598027272894332690521)
              ·
                refine ⟨2113198520454670749517891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817598027272894332690521 2113198520454670749517891)
                ·
                  refine ⟨3169797780682006124276837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113198520454670749517891 3169797780682006124276837)
                  ·
                    refine ⟨594337083877876148301907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169797780682006124276837 594337083877876148301907)
                    ·
                      rfl

theorem cell23_3472402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3472402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472402 prefixEnd_3472402 := by exact prefixLift 3472402
  have htrace : WordTrace (prefixWord ++ tailWord_3472402) baseStart_3472402 baseEnd_3472402 := by
    simpa [prefixWord, tailWord_3472402, baseEnd_3472402] using wordTrace_append hprefix tailTrace_3472402
  have hstable : (prefixWord ++ tailWord_3472402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472402).length < 2 ^ (prefixWord ++ tailWord_3472402).sum := by decide
  have hdescent : baseEnd_3472402 < baseStart_3472402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472407 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 2, 4]
def baseStart_3472407 : Nat := 118140960795 + 3472407 * 2 ^ 59
def prefixEnd_3472407 : Nat := 4983230072969 + 3 ^ 40 * 3472407 * 2
def baseEnd_3472407 : Nat := 594337939678966975114399

theorem tailTrace_3472407 : CollatzResearch.WordTrace tailWord_3472407 prefixEnd_3472407 594337939678966975114399 := by
  unfold tailWord_3472407
  simp only [CollatzResearch.WordTrace]
  refine ⟨126649087931069953746391475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84432725287379969164260983 126649087931069953746391475)
  ·
    refine ⟨189973631896604930619587213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126649087931069953746391475 189973631896604930619587213)
    ·
      refine ⟨71240111961226848982345205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189973631896604930619587213 71240111961226848982345205)
      ·
        refine ⟨6678760496365017092094863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71240111961226848982345205 6678760496365017092094863)
        ·
          refine ⟨10018140744547525638142295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6678760496365017092094863 10018140744547525638142295)
          ·
            refine ⟨15027211116821288457213443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018140744547525638142295 15027211116821288457213443)
            ·
              refine ⟨22540816675231932685820165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15027211116821288457213443 22540816675231932685820165)
              ·
                refine ⟨4226403126605987378591281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22540816675231932685820165 4226403126605987378591281)
                ·
                  refine ⟨3169802344954490533943461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4226403126605987378591281 3169802344954490533943461)
                  ·
                    refine ⟨594337939678966975114399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169802344954490533943461 594337939678966975114399)
                    ·
                      rfl

theorem cell23_3472407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_3472407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472407 prefixEnd_3472407 := by exact prefixLift 3472407
  have htrace : WordTrace (prefixWord ++ tailWord_3472407) baseStart_3472407 baseEnd_3472407 := by
    simpa [prefixWord, tailWord_3472407, baseEnd_3472407] using wordTrace_append hprefix tailTrace_3472407
  have hstable : (prefixWord ++ tailWord_3472407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472407).length < 2 ^ (prefixWord ++ tailWord_3472407).sum := by decide
  have hdescent : baseEnd_3472407 < baseStart_3472407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472420 : List Nat := [2, 3, 1, 4, 1, 1, 3, 8]
def baseStart_3472420 : Nat := 118140960795 + 3472420 * 2 ^ 59
def prefixEnd_3472420 : Nat := 4983230072969 + 3 ^ 40 * 3472420 * 2
def baseEnd_3472420 : Nat := 66037796084644791647431

theorem tailTrace_3472420 : CollatzResearch.WordTrace tailWord_3472420 prefixEnd_3472420 66037796084644791647431 := by
  unfold tailWord_3472420
  simp only [CollatzResearch.WordTrace]
  refine ⟨63324781040011428483307357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84433041386681904644409809 63324781040011428483307357)
  ·
    refine ⟨23746792890004285681240259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63324781040011428483307357 23746792890004285681240259)
    ·
      refine ⟨35620189335006428521860389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23746792890004285681240259 35620189335006428521860389)
      ·
        refine ⟨6678785500313705347848823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35620189335006428521860389 6678785500313705347848823)
        ·
          refine ⟨10018178250470558021773235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6678785500313705347848823 10018178250470558021773235)
          ·
            refine ⟨15027267375705837032659853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018178250470558021773235 15027267375705837032659853)
            ·
              refine ⟨5635225265889688887247445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15027267375705837032659853 5635225265889688887247445)
              ·
                refine ⟨66037796084644791647431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5635225265889688887247445 66037796084644791647431)
                ·
                  rfl

theorem cell23_3472420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 8].length) (baseStart_3472420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472420 prefixEnd_3472420 := by exact prefixLift 3472420
  have htrace : WordTrace (prefixWord ++ tailWord_3472420) baseStart_3472420 baseEnd_3472420 := by
    simpa [prefixWord, tailWord_3472420, baseEnd_3472420] using wordTrace_append hprefix tailTrace_3472420
  have hstable : (prefixWord ++ tailWord_3472420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472420).length < 2 ^ (prefixWord ++ tailWord_3472420).sum := by decide
  have hdescent : baseEnd_3472420 < baseStart_3472420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472433 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3472433 : Nat := 118140960795 + 3472433 * 2 ^ 59
def prefixEnd_3472433 : Nat := 4983230072969 + 3 ^ 40 * 3472433 * 2
def baseEnd_3472433 : Nat := 594342389844639274539359

theorem tailTrace_3472433 : CollatzResearch.WordTrace tailWord_3472433 prefixEnd_3472433 594342389844639274539359 := by
  unfold tailWord_3472433
  simp only [CollatzResearch.WordTrace]
  refine ⟨126650036228975760186837953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84433357485983840124558635 126650036228975760186837953)
  ·
    refine ⟨94987527171731820140128465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126650036228975760186837953 94987527171731820140128465)
    ·
      refine ⟨71240645378798865105096349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94987527171731820140128465 71240645378798865105096349)
      ·
        refine ⟨26715242017049574414411131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71240645378798865105096349 26715242017049574414411131)
        ·
          refine ⟨40072863025574361621616697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26715242017049574414411131 40072863025574361621616697)
          ·
            refine ⟨30054647269180771216212523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40072863025574361621616697 30054647269180771216212523)
            ·
              refine ⟨45081970903771156824318785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30054647269180771216212523 45081970903771156824318785)
              ·
                refine ⟨33811478177828367618239089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45081970903771156824318785 33811478177828367618239089)
                ·
                  refine ⟨25358608633371275713679317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33811478177828367618239089 25358608633371275713679317)
                  ·
                    refine ⟨594342389844639274539359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25358608633371275713679317 594342389844639274539359)
                    ·
                      rfl

theorem cell23_3472433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3472433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472433 prefixEnd_3472433 := by exact prefixLift 3472433
  have htrace : WordTrace (prefixWord ++ tailWord_3472433) baseStart_3472433 baseEnd_3472433 := by
    simpa [prefixWord, tailWord_3472433, baseEnd_3472433] using wordTrace_append hprefix tailTrace_3472433
  have hstable : (prefixWord ++ tailWord_3472433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472433).length < 2 ^ (prefixWord ++ tailWord_3472433).sum := by decide
  have hdescent : baseEnd_3472433 < baseStart_3472433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472473 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3472473 : Nat := 118140960795 + 3472473 * 2 ^ 59
def prefixEnd_3472473 : Nat := 4983230072969 + 3 ^ 40 * 3472473 * 2
def baseEnd_3472473 : Nat := 1783047708760097667117893

theorem tailTrace_3472473 : CollatzResearch.WordTrace tailWord_3472473 prefixEnd_3472473 1783047708760097667117893 := by
  unfold tailWord_3472473
  simp only [CollatzResearch.WordTrace]
  refine ⟨126651495148830847018294073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84434330099220564678862715 126651495148830847018294073)
  ·
    refine ⟨94988621361623135263720555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126651495148830847018294073 94988621361623135263720555)
    ·
      refine ⟨142482932042434702895580833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94988621361623135263720555 142482932042434702895580833)
      ·
        refine ⟨106862199031826027171685625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142482932042434702895580833 106862199031826027171685625)
        ·
          refine ⟨80146649273869520378764219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106862199031826027171685625 80146649273869520378764219)
          ·
            refine ⟨120219973910804280568146329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80146649273869520378764219 120219973910804280568146329)
            ·
              refine ⟨90164980433103210426109747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120219973910804280568146329 90164980433103210426109747)
              ·
                refine ⟨135247470649654815639164621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90164980433103210426109747 135247470649654815639164621)
                ·
                  refine ⟨50717801493620555864686733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135247470649654815639164621 50717801493620555864686733)
                  ·
                    refine ⟨19019175560107708449257525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50717801493620555864686733 19019175560107708449257525)
                    ·
                      refine ⟨1783047708760097667117893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19019175560107708449257525 1783047708760097667117893)
                      ·
                        rfl

theorem cell23_3472473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3472473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472473 prefixEnd_3472473 := by exact prefixLift 3472473
  have htrace : WordTrace (prefixWord ++ tailWord_3472473) baseStart_3472473 baseEnd_3472473 := by
    simpa [prefixWord, tailWord_3472473, baseEnd_3472473] using wordTrace_append hprefix tailTrace_3472473
  have hstable : (prefixWord ++ tailWord_3472473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472473).length < 2 ^ (prefixWord ++ tailWord_3472473).sum := by decide
  have hdescent : baseEnd_3472473 < baseStart_3472473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472538 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3472538 : Nat := 118140960795 + 3472538 * 2 ^ 59
def prefixEnd_3472538 : Nat := 4983230072969 + 3 ^ 40 * 3472538 * 2
def baseEnd_3472538 : Nat := 1783081085002639912805095

theorem tailTrace_3472538 : CollatzResearch.WordTrace tailWord_3472538 prefixEnd_3472538 1783081085002639912805095 := by
  unfold tailWord_3472538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31663466473398840779852567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84435910595730242079606845 31663466473398840779852567)
  ·
    refine ⟨47495199710098261169778851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31663466473398840779852567 47495199710098261169778851)
    ·
      refine ⟨71242799565147391754668277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47495199710098261169778851 71242799565147391754668277)
      ·
        refine ⟨6679012459232567977000151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71242799565147391754668277 6679012459232567977000151)
        ·
          refine ⟨10018518688848851965500227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6679012459232567977000151 10018518688848851965500227)
          ·
            refine ⟨15027778033273277948250341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018518688848851965500227 15027778033273277948250341)
            ·
              refine ⟨2817708381238739615296939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15027778033273277948250341 2817708381238739615296939)
              ·
                refine ⟨4226562571858109422945409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817708381238739615296939 4226562571858109422945409)
                ·
                  refine ⟨3169921928893582067209057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4226562571858109422945409 3169921928893582067209057)
                  ·
                    refine ⟨2377441446670186550406793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3169921928893582067209057 2377441446670186550406793)
                    ·
                      refine ⟨1783081085002639912805095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377441446670186550406793 1783081085002639912805095)
                      ·
                        rfl

theorem cell23_3472538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3472538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472538 prefixEnd_3472538 := by exact prefixLift 3472538
  have htrace : WordTrace (prefixWord ++ tailWord_3472538) baseStart_3472538 baseEnd_3472538 := by
    simpa [prefixWord, tailWord_3472538, baseEnd_3472538] using wordTrace_append hprefix tailTrace_3472538
  have hstable : (prefixWord ++ tailWord_3472538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472538).length < 2 ^ (prefixWord ++ tailWord_3472538).sum := by decide
  have hdescent : baseEnd_3472538 < baseStart_3472538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472560 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_3472560 : Nat := 118140960795 + 3472560 * 2 ^ 59
def prefixEnd_3472560 : Nat := 4983230072969 + 3 ^ 40 * 3472560 * 2
def baseEnd_3472560 : Nat := 1783092381577038826729993

theorem tailTrace_3472560 : CollatzResearch.WordTrace tailWord_3472560 prefixEnd_3472560 1783092381577038826729993 := by
  unfold tailWord_3472560
  simp only [CollatzResearch.WordTrace]
  refine ⟨63327334149757830438355567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84436445533010440584474089 63327334149757830438355567)
  ·
    refine ⟨94991001224636745657533351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63327334149757830438355567 94991001224636745657533351)
    ·
      refine ⟨142486501836955118486300027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94991001224636745657533351 142486501836955118486300027)
      ·
        refine ⟨213729752755432677729450041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142486501836955118486300027 213729752755432677729450041)
        ·
          refine ⟨160297314566574508297087531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213729752755432677729450041 160297314566574508297087531)
          ·
            refine ⟨240445971849861762445631297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160297314566574508297087531 240445971849861762445631297)
            ·
              refine ⟨180334478887396321834223473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240445971849861762445631297 180334478887396321834223473)
              ·
                refine ⟨135250859165547241375667605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180334478887396321834223473 135250859165547241375667605)
                ·
                  refine ⟨6339884023385026939484419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135250859165547241375667605 6339884023385026939484419)
                  ·
                    refine ⟨9509826035077540409226629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6339884023385026939484419 9509826035077540409226629)
                    ·
                      refine ⟨1783092381577038826729993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9509826035077540409226629 1783092381577038826729993)
                      ·
                        rfl

theorem cell23_3472560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_3472560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472560 prefixEnd_3472560 := by exact prefixLift 3472560
  have htrace : WordTrace (prefixWord ++ tailWord_3472560) baseStart_3472560 baseEnd_3472560 := by
    simpa [prefixWord, tailWord_3472560, baseEnd_3472560] using wordTrace_append hprefix tailTrace_3472560
  have hstable : (prefixWord ++ tailWord_3472560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472560).length < 2 ^ (prefixWord ++ tailWord_3472560).sum := by decide
  have hdescent : baseEnd_3472560 < baseStart_3472560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472578 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3472578 : Nat := 118140960795 + 3472578 * 2 ^ 59
def prefixEnd_3472578 : Nat := 4983230072969 + 3 ^ 40 * 3472578 * 2
def baseEnd_3472578 : Nat := 198122402692091084033879

theorem tailTrace_3472578 : CollatzResearch.WordTrace tailWord_3472578 prefixEnd_3472578 198122402692091084033879 := by
  unfold tailWord_3472578
  simp only [CollatzResearch.WordTrace]
  refine ⟨31663831203362612487716597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84436883208966966633910925 31663831203362612487716597)
  ·
    refine ⟨2968484175315244920723431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31663831203362612487716597 2968484175315244920723431)
    ·
      refine ⟨4452726262972867381085147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968484175315244920723431 4452726262972867381085147)
      ·
        refine ⟨6679089394459301071627721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452726262972867381085147 6679089394459301071627721)
        ·
          refine ⟨5009317045844475803720791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6679089394459301071627721 5009317045844475803720791)
          ·
            refine ⟨7513975568766713705581187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009317045844475803720791 7513975568766713705581187)
            ·
              refine ⟨11270963353150070558371781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7513975568766713705581187 11270963353150070558371781)
              ·
                refine ⟨2113305628715638229694709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11270963353150070558371781 2113305628715638229694709)
                ·
                  refine ⟨198122402692091084033879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113305628715638229694709 198122402692091084033879)
                  ·
                    rfl

theorem cell23_3472578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3472578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472578 prefixEnd_3472578 := by exact prefixLift 3472578
  have htrace : WordTrace (prefixWord ++ tailWord_3472578) baseStart_3472578 baseEnd_3472578 := by
    simpa [prefixWord, tailWord_3472578, baseEnd_3472578] using wordTrace_append hprefix tailTrace_3472578
  have hstable : (prefixWord ++ tailWord_3472578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472578).length < 2 ^ (prefixWord ++ tailWord_3472578).sum := by decide
  have hdescent : baseEnd_3472578 < baseStart_3472578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472594 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_3472594 : Nat := 118140960795 + 3472594 * 2 ^ 59
def prefixEnd_3472594 : Nat := 4983230072969 + 3 ^ 40 * 3472594 * 2
def baseEnd_3472594 : Nat := 1783109839919291693704837

theorem tailTrace_3472594 : CollatzResearch.WordTrace tailWord_3472594 prefixEnd_3472594 1783109839919291693704837 := by
  unfold tailWord_3472594
  simp only [CollatzResearch.WordTrace]
  refine ⟨31663977095348121170862209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84437272254261656455632557 31663977095348121170862209)
  ·
    refine ⟨23747982821511090878146657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31663977095348121170862209 23747982821511090878146657)
    ·
      refine ⟨17810987116133318158609993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23747982821511090878146657 17810987116133318158609993)
      ·
        refine ⟨13358240337099988618957495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17810987116133318158609993 13358240337099988618957495)
        ·
          refine ⟨20037360505649982928436243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358240337099988618957495 20037360505649982928436243)
          ·
            refine ⟨30056040758474974392654365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20037360505649982928436243 30056040758474974392654365)
            ·
              refine ⟨11271015284428115397245387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30056040758474974392654365 11271015284428115397245387)
              ·
                refine ⟨16906522926642173095868081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271015284428115397245387 16906522926642173095868081)
                ·
                  refine ⟨12679892194981629821901061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16906522926642173095868081 12679892194981629821901061)
                  ·
                    refine ⟨2377479786559055591606449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12679892194981629821901061 2377479786559055591606449)
                    ·
                      refine ⟨1783109839919291693704837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377479786559055591606449 1783109839919291693704837)
                      ·
                        rfl

theorem cell23_3472594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_3472594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472594 prefixEnd_3472594 := by exact prefixLift 3472594
  have htrace : WordTrace (prefixWord ++ tailWord_3472594) baseStart_3472594 baseEnd_3472594 := by
    simpa [prefixWord, tailWord_3472594, baseEnd_3472594] using wordTrace_append hprefix tailTrace_3472594
  have hstable : (prefixWord ++ tailWord_3472594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472594).length < 2 ^ (prefixWord ++ tailWord_3472594).sum := by decide
  have hdescent : baseEnd_3472594 < baseStart_3472594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472621 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_3472621 : Nat := 118140960795 + 3472621 * 2 ^ 59
def prefixEnd_3472621 : Nat := 4983230072969 + 3 ^ 40 * 3472621 * 2
def baseEnd_3472621 : Nat := 594374567965654362689071

theorem tailTrace_3472621 : CollatzResearch.WordTrace tailWord_3472621 prefixEnd_3472621 594374567965654362689071 := by
  unfold tailWord_3472621
  simp only [CollatzResearch.WordTrace]
  refine ⟨126656893152294668294681717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84437928768196445529787811 126656893152294668294681717)
  ·
    refine ⟨11874083733027625152626411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126656893152294668294681717 11874083733027625152626411)
    ·
      refine ⟨17811125599541437728939617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11874083733027625152626411 17811125599541437728939617)
      ·
        refine ⟨13358344199656078296704713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17811125599541437728939617 13358344199656078296704713)
        ·
          refine ⟨10018758149742058722528535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13358344199656078296704713 10018758149742058722528535)
          ·
            refine ⟨15028137224613088083792803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018758149742058722528535 15028137224613088083792803)
            ·
              refine ⟨22542205836919632125689205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15028137224613088083792803 22542205836919632125689205)
              ·
                refine ⟨2113331797211215511783363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22542205836919632125689205 2113331797211215511783363)
                ·
                  refine ⟨3169997695816823267675045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113331797211215511783363 3169997695816823267675045)
                  ·
                    refine ⟨594374567965654362689071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169997695816823267675045 594374567965654362689071)
                    ·
                      rfl

theorem cell23_3472621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_3472621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472621 prefixEnd_3472621 := by exact prefixLift 3472621
  have htrace : WordTrace (prefixWord ++ tailWord_3472621) baseStart_3472621 baseEnd_3472621 := by
    simpa [prefixWord, tailWord_3472621, baseEnd_3472621] using wordTrace_append hprefix tailTrace_3472621
  have hstable : (prefixWord ++ tailWord_3472621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472621).length < 2 ^ (prefixWord ++ tailWord_3472621).sum := by decide
  have hdescent : baseEnd_3472621 < baseStart_3472621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472654 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3472654 : Nat := 118140960795 + 3472654 * 2 ^ 59
def prefixEnd_3472654 : Nat := 4983230072969 + 3 ^ 40 * 3472654 * 2
def baseEnd_3472654 : Nat := 1783140648758561458954561

theorem tailTrace_3472654 : CollatzResearch.WordTrace tailWord_3472654 prefixEnd_3472654 1783140648758561458954561 := by
  unfold tailWord_3472654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15832262095146889366329127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84438731174116743287088677 15832262095146889366329127)
  ·
    refine ⟨23748393142720334049493691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15832262095146889366329127 23748393142720334049493691)
    ·
      refine ⟨35622589714080501074240537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23748393142720334049493691 35622589714080501074240537)
      ·
        refine ⟨26716942285560375805680403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35622589714080501074240537 26716942285560375805680403)
        ·
          refine ⟨40075413428340563708520605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26716942285560375805680403 40075413428340563708520605)
          ·
            refine ⟨15028280035627711390695227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40075413428340563708520605 15028280035627711390695227)
            ·
              refine ⟨22542420053441567086042841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15028280035627711390695227 22542420053441567086042841)
              ·
                refine ⟨16906815040081175314532131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22542420053441567086042841 16906815040081175314532131)
                ·
                  refine ⟨25360222560121762971798197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16906815040081175314532131 25360222560121762971798197)
                  ·
                    refine ⟨2377520865011415278606081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25360222560121762971798197 2377520865011415278606081)
                    ·
                      refine ⟨1783140648758561458954561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377520865011415278606081 1783140648758561458954561)
                      ·
                        rfl

theorem cell23_3472654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3472654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472654 prefixEnd_3472654 := by exact prefixLift 3472654
  have htrace : WordTrace (prefixWord ++ tailWord_3472654) baseStart_3472654 baseEnd_3472654 := by
    simpa [prefixWord, tailWord_3472654, baseEnd_3472654] using wordTrace_append hprefix tailTrace_3472654
  have hstable : (prefixWord ++ tailWord_3472654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472654).length < 2 ^ (prefixWord ++ tailWord_3472654).sum := by decide
  have hdescent : baseEnd_3472654 < baseStart_3472654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472664 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 1, 5]
def baseStart_3472664 : Nat := 118140960795 + 3472664 * 2 ^ 59
def prefixEnd_3472664 : Nat := 4983230072969 + 3 ^ 40 * 3472664 * 2
def baseEnd_3472664 : Nat := 594381927855035473276505

theorem tailTrace_3472664 : CollatzResearch.WordTrace tailWord_3472664 prefixEnd_3472664 594381927855035473276505 := by
  unfold tailWord_3472664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63329230745569443319248523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84438974327425924425664697 63329230745569443319248523)
  ·
    refine ⟨94993846118354164978872785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63329230745569443319248523 94993846118354164978872785)
    ·
      refine ⟨71245384588765623734154589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94993846118354164978872785 71245384588765623734154589)
      ·
        refine ⟨26717019220787108900307971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71245384588765623734154589 26717019220787108900307971)
        ·
          refine ⟨40075528831180663350461957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26717019220787108900307971 40075528831180663350461957)
          ·
            refine ⟨7514161655846374378211617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40075528831180663350461957 7514161655846374378211617)
            ·
              refine ⟨5635621241884780783658713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7514161655846374378211617 5635621241884780783658713)
              ·
                refine ⟨4226715931413585587744035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5635621241884780783658713 4226715931413585587744035)
                ·
                  refine ⟨6340073897120378381616053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4226715931413585587744035 6340073897120378381616053)
                  ·
                    refine ⟨594381927855035473276505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6340073897120378381616053 594381927855035473276505)
                    ·
                      rfl

theorem cell23_3472664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_3472664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472664 prefixEnd_3472664 := by exact prefixLift 3472664
  have htrace : WordTrace (prefixWord ++ tailWord_3472664) baseStart_3472664 baseEnd_3472664 := by
    simpa [prefixWord, tailWord_3472664, baseEnd_3472664] using wordTrace_append hprefix tailTrace_3472664
  have hstable : (prefixWord ++ tailWord_3472664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472664).length < 2 ^ (prefixWord ++ tailWord_3472664).sum := by decide
  have hdescent : baseEnd_3472664 < baseStart_3472664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472667 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 8, 2]
def baseStart_3472667 : Nat := 118140960795 + 3472667 * 2 ^ 59
def prefixEnd_3472667 : Nat := 4983230072969 + 3 ^ 40 * 3472667 * 2
def baseEnd_3472667 : Nat := 1783147324007069908092001

theorem tailTrace_3472667 : CollatzResearch.WordTrace tailWord_3472667 prefixEnd_3472667 1783147324007069908092001 := by
  unfold tailWord_3472667
  simp only [CollatzResearch.WordTrace]
  refine ⟨126658570910128018150856255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84439047273418678767237503 126658570910128018150856255)
  ·
    refine ⟨189987856365192027226284383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126658570910128018150856255 189987856365192027226284383)
    ·
      refine ⟨284981784547788040839426575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189987856365192027226284383 284981784547788040839426575)
      ·
        refine ⟨427472676821682061259139863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284981784547788040839426575 427472676821682061259139863)
        ·
          refine ⟨641209015232523091888709795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427472676821682061259139863 641209015232523091888709795)
          ·
            refine ⟨961813522848784637833064693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641209015232523091888709795 961813522848784637833064693)
            ·
              refine ⟨90170017767073559796849815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 961813522848784637833064693 90170017767073559796849815)
              ·
                refine ⟨135255026650610339695274723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90170017767073559796849815 135255026650610339695274723)
                ·
                  refine ⟨202882539975915509542912085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135255026650610339695274723 202882539975915509542912085)
                  ·
                    refine ⟨2377529765342759877456001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 202882539975915509542912085 2377529765342759877456001)
                    ·
                      refine ⟨1783147324007069908092001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377529765342759877456001 1783147324007069908092001)
                      ·
                        rfl

theorem cell23_3472667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8, 2].length) (baseStart_3472667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472667 prefixEnd_3472667 := by exact prefixLift 3472667
  have htrace : WordTrace (prefixWord ++ tailWord_3472667) baseStart_3472667 baseEnd_3472667 := by
    simpa [prefixWord, tailWord_3472667, baseEnd_3472667] using wordTrace_append hprefix tailTrace_3472667
  have hstable : (prefixWord ++ tailWord_3472667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472667).length < 2 ^ (prefixWord ++ tailWord_3472667).sum := by decide
  have hdescent : baseEnd_3472667 < baseStart_3472667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472687 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_3472687 : Nat := 118140960795 + 3472687 * 2 ^ 59
def prefixEnd_3472687 : Nat := 4983230072969 + 3 ^ 40 * 3472687 * 2
def baseEnd_3472687 : Nat := 1783157593620159829841909

theorem tailTrace_3472687 : CollatzResearch.WordTrace tailWord_3472687 prefixEnd_3472687 1783157593620159829841909 := by
  unfold tailWord_3472687
  simp only [CollatzResearch.WordTrace]
  refine ⟨126659300370055561566584315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84439533580037041044389543 126659300370055561566584315)
  ·
    refine ⟨189988950555083342349876473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126659300370055561566584315 189988950555083342349876473)
    ·
      refine ⟨142491712916312506762407355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189988950555083342349876473 142491712916312506762407355)
      ·
        refine ⟨213737569374468760143611033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142491712916312506762407355 213737569374468760143611033)
        ·
          refine ⟨160303177030851570107708275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213737569374468760143611033 160303177030851570107708275)
          ·
            refine ⟨240454765546277355161562413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160303177030851570107708275 240454765546277355161562413)
            ·
              refine ⟨90170537079854008185585905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240454765546277355161562413 90170537079854008185585905)
              ·
                refine ⟨67627902809890506139189429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90170537079854008185585905 67627902809890506139189429)
                ·
                  refine ⟨6340115888427234950549009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67627902809890506139189429 6340115888427234950549009)
                  ·
                    refine ⟨4755086916320426212911757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6340115888427234950549009 4755086916320426212911757)
                    ·
                      refine ⟨1783157593620159829841909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755086916320426212911757 1783157593620159829841909)
                      ·
                        rfl

theorem cell23_3472687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_3472687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472687 prefixEnd_3472687 := by exact prefixLift 3472687
  have htrace : WordTrace (prefixWord ++ tailWord_3472687) baseStart_3472687 baseEnd_3472687 := by
    simpa [prefixWord, tailWord_3472687, baseEnd_3472687] using wordTrace_append hprefix tailTrace_3472687
  have hstable : (prefixWord ++ tailWord_3472687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472687).length < 2 ^ (prefixWord ++ tailWord_3472687).sum := by decide
  have hdescent : baseEnd_3472687 < baseStart_3472687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472711 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 2, 4]
def baseStart_3472711 : Nat := 118140960795 + 3472711 * 2 ^ 59
def prefixEnd_3472711 : Nat := 4983230072969 + 3 ^ 40 * 3472711 * 2
def baseEnd_3472711 : Nat := 594389972385289245313933

theorem tailTrace_3472711 : CollatzResearch.WordTrace tailWord_3472711 prefixEnd_3472711 594389972385289245313933 := by
  unfold tailWord_3472711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126660175721968613665457987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84440117147979075776971991 126660175721968613665457987)
  ·
    refine ⟨189990263582952920498186981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126660175721968613665457987 189990263582952920498186981)
    ·
      refine ⟨35623174421803672593410059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189990263582952920498186981 35623174421803672593410059)
      ·
        refine ⟨53434761632705508890115089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35623174421803672593410059 53434761632705508890115089)
        ·
          refine ⟨40076071224529131667586317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53434761632705508890115089 40076071224529131667586317)
          ·
            refine ⟨15028526709198424375344869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40076071224529131667586317 15028526709198424375344869)
            ·
              refine ⟨2817848757974704570377163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15028526709198424375344869 2817848757974704570377163)
              ·
                refine ⟨4226773136962056855565745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817848757974704570377163 4226773136962056855565745)
                ·
                  refine ⟨3170079852721542641674309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4226773136962056855565745 3170079852721542641674309)
                  ·
                    refine ⟨594389972385289245313933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3170079852721542641674309 594389972385289245313933)
                    ·
                      rfl

theorem cell23_3472711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_3472711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472711 prefixEnd_3472711 := by exact prefixLift 3472711
  have htrace : WordTrace (prefixWord ++ tailWord_3472711) baseStart_3472711 baseEnd_3472711 := by
    simpa [prefixWord, tailWord_3472711, baseEnd_3472711] using wordTrace_append hprefix tailTrace_3472711
  have hstable : (prefixWord ++ tailWord_3472711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472711).length < 2 ^ (prefixWord ++ tailWord_3472711).sum := by decide
  have hdescent : baseEnd_3472711 < baseStart_3472711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472738 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_3472738 : Nat := 118140960795 + 3472738 * 2 ^ 59
def prefixEnd_3472738 : Nat := 4983230072969 + 3 ^ 40 * 3472738 * 2
def baseEnd_3472738 : Nat := 1783183781133539130304175

theorem tailTrace_3472738 : CollatzResearch.WordTrace tailWord_3472738 prefixEnd_3472738 1783183781133539130304175 := by
  unfold tailWord_3472738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31665290123217699319172717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84440773661913864851127245 31665290123217699319172717)
  ·
    refine ⟨11874483796206637244689769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31665290123217699319172717 11874483796206637244689769)
    ·
      refine ⟨8905862847154977933517327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11874483796206637244689769 8905862847154977933517327)
      ·
        refine ⟨13358794270732466900275991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8905862847154977933517327 13358794270732466900275991)
        ·
          refine ⟨20038191406098700350413987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358794270732466900275991 20038191406098700350413987)
          ·
            refine ⟨30057287109148050525620981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20038191406098700350413987 30057287109148050525620981)
            ·
              refine ⟨2817870666482629736776967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30057287109148050525620981 2817870666482629736776967)
              ·
                refine ⟨4226805999723944605165451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817870666482629736776967 4226805999723944605165451)
                ·
                  refine ⟨6340208999585916907748177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4226805999723944605165451 6340208999585916907748177)
                  ·
                    refine ⟨4755156749689437680811133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6340208999585916907748177 4755156749689437680811133)
                    ·
                      refine ⟨1783183781133539130304175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755156749689437680811133 1783183781133539130304175)
                      ·
                        rfl

theorem cell23_3472738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_3472738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472738 prefixEnd_3472738 := by exact prefixLift 3472738
  have htrace : WordTrace (prefixWord ++ tailWord_3472738) baseStart_3472738 baseEnd_3472738 := by
    simpa [prefixWord, tailWord_3472738, baseEnd_3472738] using wordTrace_append hprefix tailTrace_3472738
  have hstable : (prefixWord ++ tailWord_3472738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472738).length < 2 ^ (prefixWord ++ tailWord_3472738).sum := by decide
  have hdescent : baseEnd_3472738 < baseStart_3472738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472751 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 3]
def baseStart_3472751 : Nat := 118140960795 + 3472751 * 2 ^ 59
def prefixEnd_3472751 : Nat := 4983230072969 + 3 ^ 40 * 3472751 * 2
def baseEnd_3472751 : Nat := 1783190456382047579441615

theorem tailTrace_3472751 : CollatzResearch.WordTrace tailWord_3472751 prefixEnd_3472751 1783190456382047579441615 := by
  unfold tailWord_3472751
  simp only [CollatzResearch.WordTrace]
  refine ⟨126661634641823700496914107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84441089761215800331276071 126661634641823700496914107)
  ·
    refine ⟨189992451962735550745371161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126661634641823700496914107 189992451962735550745371161)
    ·
      refine ⟨142494338972051663059028371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189992451962735550745371161 142494338972051663059028371)
      ·
        refine ⟨213741508458077494588542557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142494338972051663059028371 213741508458077494588542557)
        ·
          refine ⟨80153065671779060470703459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213741508458077494588542557 80153065671779060470703459)
          ·
            refine ⟨120229598507668590706055189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80153065671779060470703459 120229598507668590706055189)
            ·
              refine ⟨5635762430046965189346337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120229598507668590706055189 5635762430046965189346337)
              ·
                refine ⟨4226821822535223892009753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5635762430046965189346337 4226821822535223892009753)
                ·
                  refine ⟨3170116366901417919007315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4226821822535223892009753 3170116366901417919007315)
                  ·
                    refine ⟨4755174550352126878510973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3170116366901417919007315 4755174550352126878510973)
                    ·
                      refine ⟨1783190456382047579441615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755174550352126878510973 1783190456382047579441615)
                      ·
                        rfl

theorem cell23_3472751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_3472751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472751 prefixEnd_3472751 := by exact prefixLift 3472751
  have htrace : WordTrace (prefixWord ++ tailWord_3472751) baseStart_3472751 baseEnd_3472751 := by
    simpa [prefixWord, tailWord_3472751, baseEnd_3472751] using wordTrace_append hprefix tailTrace_3472751
  have hstable : (prefixWord ++ tailWord_3472751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472751).length < 2 ^ (prefixWord ++ tailWord_3472751).sum := by decide
  have hdescent : baseEnd_3472751 < baseStart_3472751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472791 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 4, 2, 2]
def baseStart_3472791 : Nat := 118140960795 + 3472791 * 2 ^ 59
def prefixEnd_3472791 : Nat := 4983230072969 + 3 ^ 40 * 3472791 * 2
def baseEnd_3472791 : Nat := 1783210995608227422941431

theorem tailTrace_3472791 : CollatzResearch.WordTrace tailWord_3472791 prefixEnd_3472791 1783210995608227422941431 := by
  unfold tailWord_3472791
  simp only [CollatzResearch.WordTrace]
  refine ⟨126663093561678787328370227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84442062374452524885580151 126663093561678787328370227)
  ·
    refine ⟨189994640342518180992555341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126663093561678787328370227 189994640342518180992555341)
    ·
      refine ⟨71247990128444317872208253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189994640342518180992555341 71247990128444317872208253)
      ·
        refine ⟨26717996298166619202078095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71247990128444317872208253 26717996298166619202078095)
        ·
          refine ⟨40076994447249928803117143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26717996298166619202078095 40076994447249928803117143)
          ·
            refine ⟨60115491670874893204675715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40076994447249928803117143 60115491670874893204675715)
            ·
              refine ⟨90173237506312339807013573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60115491670874893204675715 90173237506312339807013573)
              ·
                refine ⟨16907482032433563713815045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90173237506312339807013573 16907482032433563713815045)
                ·
                  refine ⟨3170152881081293196340321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16907482032433563713815045 3170152881081293196340321)
                  ·
                    refine ⟨2377614660810969897255241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3170152881081293196340321 2377614660810969897255241)
                    ·
                      refine ⟨1783210995608227422941431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377614660810969897255241 1783210995608227422941431)
                      ·
                        rfl

theorem cell23_3472791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_3472791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472791 prefixEnd_3472791 := by exact prefixLift 3472791
  have htrace : WordTrace (prefixWord ++ tailWord_3472791) baseStart_3472791 baseEnd_3472791 := by
    simpa [prefixWord, tailWord_3472791, baseEnd_3472791] using wordTrace_append hprefix tailTrace_3472791
  have hstable : (prefixWord ++ tailWord_3472791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472791).length < 2 ^ (prefixWord ++ tailWord_3472791).sum := by decide
  have hdescent : baseEnd_3472791 < baseStart_3472791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472824 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_3472824 : Nat := 118140960795 + 3472824 * 2 ^ 59
def prefixEnd_3472824 : Nat := 4983230072969 + 3 ^ 40 * 3472824 * 2
def baseEnd_3472824 : Nat := 1783227940469825793828779

theorem tailTrace_3472824 : CollatzResearch.WordTrace tailWord_3472824 prefixEnd_3472824 1783227940469825793828779 := by
  unfold tailWord_3472824
  simp only [CollatzResearch.WordTrace]
  refine ⟨63332148585279616982160763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84442864780372822642881017 63332148585279616982160763)
  ·
    refine ⟨94998222877919425473241145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63332148585279616982160763 94998222877919425473241145)
    ·
      refine ⟨71248667158439569104930859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94998222877919425473241145 71248667158439569104930859)
      ·
        refine ⟨106873000737659353657396289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71248667158439569104930859 106873000737659353657396289)
        ·
          refine ⟨80154750553244515243047217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106873000737659353657396289 80154750553244515243047217)
          ·
            refine ⟨60116062914933386432285413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80154750553244515243047217 60116062914933386432285413)
            ·
              refine ⟨11271761796550009956053515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60116062914933386432285413 11271761796550009956053515)
              ·
                refine ⟨16907642694825014934080273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271761796550009956053515 16907642694825014934080273)
                ·
                  refine ⟨12680732021118761200560205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16907642694825014934080273 12680732021118761200560205)
                  ·
                    refine ⟨4755274507919535450210077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12680732021118761200560205 4755274507919535450210077)
                    ·
                      refine ⟨1783227940469825793828779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755274507919535450210077 1783227940469825793828779)
                      ·
                        rfl

theorem cell23_3472824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_3472824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472824 prefixEnd_3472824 := by exact prefixLift 3472824
  have htrace : WordTrace (prefixWord ++ tailWord_3472824) baseStart_3472824 baseEnd_3472824 := by
    simpa [prefixWord, tailWord_3472824, baseEnd_3472824] using wordTrace_append hprefix tailTrace_3472824
  have hstable : (prefixWord ++ tailWord_3472824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472824).length < 2 ^ (prefixWord ++ tailWord_3472824).sum := by decide
  have hdescent : baseEnd_3472824 < baseStart_3472824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472825 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3472825 : Nat := 118140960795 + 3472825 * 2 ^ 59
def prefixEnd_3472825 : Nat := 4983230072969 + 3 ^ 40 * 3472825 * 2
def baseEnd_3472825 : Nat := 1783228453950480289916275

theorem tailTrace_3472825 : CollatzResearch.WordTrace tailWord_3472825 prefixEnd_3472825 1783228453950480289916275 := by
  unfold tailWord_3472825
  simp only [CollatzResearch.WordTrace]
  refine ⟨126664333643555611135107929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84442889095703740756738619 126664333643555611135107929)
  ·
    refine ⟨94998250232666708351330947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126664333643555611135107929 94998250232666708351330947)
    ·
      refine ⟨142497375349000062526996421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94998250232666708351330947 142497375349000062526996421)
      ·
        refine ⟨26718257877937511723811829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142497375349000062526996421 26718257877937511723811829)
        ·
          refine ⟨2504836676056641724107359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26718257877937511723811829 2504836676056641724107359)
          ·
            refine ⟨3757255014084962586161039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504836676056641724107359 3757255014084962586161039)
            ·
              refine ⟨5635882521127443879241559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757255014084962586161039 5635882521127443879241559)
              ·
                refine ⟨8453823781691165818862339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635882521127443879241559 8453823781691165818862339)
                ·
                  refine ⟨12680735672536748728293509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453823781691165818862339 12680735672536748728293509)
                  ·
                    refine ⟨2377637938600640386555033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12680735672536748728293509 2377637938600640386555033)
                    ·
                      refine ⟨1783228453950480289916275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377637938600640386555033 1783228453950480289916275)
                      ·
                        rfl

theorem cell23_3472825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3472825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472825 prefixEnd_3472825 := by exact prefixLift 3472825
  have htrace : WordTrace (prefixWord ++ tailWord_3472825) baseStart_3472825 baseEnd_3472825 := by
    simpa [prefixWord, tailWord_3472825, baseEnd_3472825] using wordTrace_append hprefix tailTrace_3472825
  have hstable : (prefixWord ++ tailWord_3472825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472825).length < 2 ^ (prefixWord ++ tailWord_3472825).sum := by decide
  have hdescent : baseEnd_3472825 < baseStart_3472825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472844 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_3472844 : Nat := 118140960795 + 3472844 * 2 ^ 59
def prefixEnd_3472844 : Nat := 4983230072969 + 3 ^ 40 * 3472844 * 2
def baseEnd_3472844 : Nat := 594412736694305238526229

theorem tailTrace_3472844 : CollatzResearch.WordTrace tailWord_3472844 prefixEnd_3472844 594412736694305238526229 := by
  unfold tailWord_3472844
  simp only [CollatzResearch.WordTrace]
  refine ⟨63332513315243388690024793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84443351086991184920033057 63332513315243388690024793)
  ·
    refine ⟨47499384986432541517518595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63332513315243388690024793 47499384986432541517518595)
    ·
      refine ⟨71249077479648812276277893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47499384986432541517518595 71249077479648812276277893)
      ·
        refine ⟨13359202027434152301802105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71249077479648812276277893 13359202027434152301802105)
        ·
          refine ⟨10019401520575614226351579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13359202027434152301802105 10019401520575614226351579)
          ·
            refine ⟨15029102280863421339527369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019401520575614226351579 15029102280863421339527369)
            ·
              refine ⟨11271826710647566004645527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15029102280863421339527369 11271826710647566004645527)
              ·
                refine ⟨16907740065971349006968291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271826710647566004645527 16907740065971349006968291)
                ·
                  refine ⟨25361610098957023510452437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16907740065971349006968291 25361610098957023510452437)
                  ·
                    refine ⟨594412736694305238526229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25361610098957023510452437 594412736694305238526229)
                    ·
                      rfl

theorem cell23_3472844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_3472844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472844 prefixEnd_3472844 := by exact prefixLift 3472844
  have htrace : WordTrace (prefixWord ++ tailWord_3472844) baseStart_3472844 baseEnd_3472844 := by
    simpa [prefixWord, tailWord_3472844, baseEnd_3472844] using wordTrace_append hprefix tailTrace_3472844
  have hstable : (prefixWord ++ tailWord_3472844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472844).length < 2 ^ (prefixWord ++ tailWord_3472844).sum := by decide
  have hdescent : baseEnd_3472844 < baseStart_3472844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472861 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3472861 : Nat := 118140960795 + 3472861 * 2 ^ 59
def prefixEnd_3472861 : Nat := 4983230072969 + 3 ^ 40 * 3472861 * 2
def baseEnd_3472861 : Nat := 594415646418014049688703

theorem tailTrace_3472861 : CollatzResearch.WordTrace tailWord_3472861 prefixEnd_3472861 594415646418014049688703 := by
  unfold tailWord_3472861
  simp only [CollatzResearch.WordTrace]
  refine ⟨126665646671425189283418437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84443764447616792855612291 126665646671425189283418437)
  ·
    refine ⟨23749808750892222990640957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126665646671425189283418437 23749808750892222990640957)
    ·
      refine ⟨8906178281584583621490359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23749808750892222990640957 8906178281584583621490359)
      ·
        refine ⟨13359267422376875432235539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906178281584583621490359 13359267422376875432235539)
        ·
          refine ⟨20038901133565313148353309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13359267422376875432235539 20038901133565313148353309)
          ·
            refine ⟨7514587925086992430632491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20038901133565313148353309 7514587925086992430632491)
            ·
              refine ⟨11271881887630488645948737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514587925086992430632491 11271881887630488645948737)
              ·
                refine ⟨8453911415722866484461553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11271881887630488645948737 8453911415722866484461553)
                ·
                  refine ⟨6340433561792149863346165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8453911415722866484461553 6340433561792149863346165)
                  ·
                    refine ⟨594415646418014049688703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6340433561792149863346165 594415646418014049688703)
                    ·
                      rfl

theorem cell23_3472861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3472861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472861 prefixEnd_3472861 := by exact prefixLift 3472861
  have htrace : WordTrace (prefixWord ++ tailWord_3472861) baseStart_3472861 baseEnd_3472861 := by
    simpa [prefixWord, tailWord_3472861, baseEnd_3472861] using wordTrace_append hprefix tailTrace_3472861
  have hstable : (prefixWord ++ tailWord_3472861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472861).length < 2 ^ (prefixWord ++ tailWord_3472861).sum := by decide
  have hdescent : baseEnd_3472861 < baseStart_3472861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472887 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 10]
def baseStart_3472887 : Nat := 118140960795 + 3472887 * 2 ^ 59
def prefixEnd_3472887 : Nat := 4983230072969 + 3 ^ 40 * 3472887 * 2
def baseEnd_3472887 : Nat := 198140032194562116371221

theorem tailTrace_3472887 : CollatzResearch.WordTrace tailWord_3472887 prefixEnd_3472887 198140032194562116371221 := by
  unfold tailWord_3472887
  simp only [CollatzResearch.WordTrace]
  refine ⟨126666594969330995723864915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84444396646220663815909943 126666594969330995723864915)
  ·
    refine ⟨189999892453996493585797373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126666594969330995723864915 189999892453996493585797373)
    ·
      refine ⟨71249959670248685094674015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189999892453996493585797373 71249959670248685094674015)
      ·
        refine ⟨106874939505373027642011023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71249959670248685094674015 106874939505373027642011023)
        ·
          refine ⟨160312409258059541463016535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106874939505373027642011023 160312409258059541463016535)
          ·
            refine ⟨240468613887089312194524803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160312409258059541463016535 240468613887089312194524803)
            ·
              refine ⟨360702920830633968291787205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240468613887089312194524803 360702920830633968291787205)
              ·
                refine ⟨67631797655743869054710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360702920830633968291787205 67631797655743869054710101)
                ·
                  refine ⟨198140032194562116371221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67631797655743869054710101 198140032194562116371221)
                  ·
                    rfl

theorem cell23_3472887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 10].length) (baseStart_3472887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472887 prefixEnd_3472887 := by exact prefixLift 3472887
  have htrace : WordTrace (prefixWord ++ tailWord_3472887) baseStart_3472887 baseEnd_3472887 := by
    simpa [prefixWord, tailWord_3472887, baseEnd_3472887] using wordTrace_append hprefix tailTrace_3472887
  have hstable : (prefixWord ++ tailWord_3472887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472887).length < 2 ^ (prefixWord ++ tailWord_3472887).sum := by decide
  have hdescent : baseEnd_3472887 < baseStart_3472887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472898 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3472898 : Nat := 118140960795 + 3472898 * 2 ^ 59
def prefixEnd_3472898 : Nat := 4983230072969 + 3 ^ 40 * 3472898 * 2
def baseEnd_3472898 : Nat := 1783265938038258504303439

theorem tailTrace_3472898 : CollatzResearch.WordTrace tailWord_3472898 prefixEnd_3472898 1783265938038258504303439 := by
  unfold tailWord_3472898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31666749043072786150628837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84444664114860763068343565 31666749043072786150628837)
  ·
    refine ⟨5937515445576147403242907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31666749043072786150628837 5937515445576147403242907)
    ·
      refine ⟨8906273168364221104864361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937515445576147403242907 8906273168364221104864361)
      ·
        refine ⟨6679704876273165828648271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8906273168364221104864361 6679704876273165828648271)
        ·
          refine ⟨10019557314409748742972407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6679704876273165828648271 10019557314409748742972407)
          ·
            refine ⟨15029335971614623114458611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019557314409748742972407 15029335971614623114458611)
            ·
              refine ⟨22544003957421934671687917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15029335971614623114458611 22544003957421934671687917)
              ·
                refine ⟨8454001484033225501882969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22544003957421934671687917 8454001484033225501882969)
                ·
                  refine ⟨6340501113024919126412227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8454001484033225501882969 6340501113024919126412227)
                  ·
                    refine ⟨9510751669537378689618341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6340501113024919126412227 9510751669537378689618341)
                    ·
                      refine ⟨1783265938038258504303439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9510751669537378689618341 1783265938038258504303439)
                      ·
                        rfl

theorem cell23_3472898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3472898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472898 prefixEnd_3472898 := by exact prefixLift 3472898
  have htrace : WordTrace (prefixWord ++ tailWord_3472898) baseStart_3472898 baseEnd_3472898 := by
    simpa [prefixWord, tailWord_3472898, baseEnd_3472898] using wordTrace_append hprefix tailTrace_3472898
  have hstable : (prefixWord ++ tailWord_3472898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472898).length < 2 ^ (prefixWord ++ tailWord_3472898).sum := by decide
  have hdescent : baseEnd_3472898 < baseStart_3472898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472924 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3472924 : Nat := 118140960795 + 3472924 * 2 ^ 59
def prefixEnd_3472924 : Nat := 4983230072969 + 3 ^ 40 * 3472924 * 2
def baseEnd_3472924 : Nat := 1783279288535275402578319

theorem tailTrace_3472924 : CollatzResearch.WordTrace tailWord_3472924 prefixEnd_3472924 1783279288535275402578319 := by
  unfold tailWord_3472924
  simp only [CollatzResearch.WordTrace]
  refine ⟨63333972235098475521480913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84445296313464634028641217 63333972235098475521480913)
  ·
    refine ⟨47500479176323856641110685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63333972235098475521480913 47500479176323856641110685)
    ·
      refine ⟨17812679691121446240416507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47500479176323856641110685 17812679691121446240416507)
      ·
        refine ⟨26719019536682169360624761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17812679691121446240416507 26719019536682169360624761)
        ·
          refine ⟨20039264652511627020468571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26719019536682169360624761 20039264652511627020468571)
          ·
            refine ⟨30058896978767440530702857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20039264652511627020468571 30058896978767440530702857)
            ·
              refine ⟨22544172734075580398027143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30058896978767440530702857 22544172734075580398027143)
              ·
                refine ⟨33816259101113370597040715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22544172734075580398027143 33816259101113370597040715)
                ·
                  refine ⟨50724388651670055895561073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33816259101113370597040715 50724388651670055895561073)
                  ·
                    refine ⟨38043291488752541921670805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50724388651670055895561073 38043291488752541921670805)
                    ·
                      refine ⟨1783279288535275402578319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38043291488752541921670805 1783279288535275402578319)
                      ·
                        rfl

theorem cell23_3472924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3472924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472924 prefixEnd_3472924 := by exact prefixLift 3472924
  have htrace : WordTrace (prefixWord ++ tailWord_3472924) baseStart_3472924 baseEnd_3472924 := by
    simpa [prefixWord, tailWord_3472924, baseEnd_3472924] using wordTrace_append hprefix tailTrace_3472924
  have hstable : (prefixWord ++ tailWord_3472924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472924).length < 2 ^ (prefixWord ++ tailWord_3472924).sum := by decide
  have hdescent : baseEnd_3472924 < baseStart_3472924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472965 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 1, 1, 3]
def baseStart_3472965 : Nat := 118140960795 + 3472965 * 2 ^ 59
def prefixEnd_3472965 : Nat := 4983230072969 + 3 ^ 40 * 3472965 * 2
def baseEnd_3472965 : Nat := 1783300341242109742165631

theorem tailTrace_3472965 : CollatzResearch.WordTrace tailWord_3472965 prefixEnd_3472965 1783300341242109742165631 := by
  unfold tailWord_3472965
  simp only [CollatzResearch.WordTrace]
  refine ⟨126669439863048415045204349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84446293242032276696802899 126669439863048415045204349)
  ·
    refine ⟨47501039948643155641951631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126669439863048415045204349 47501039948643155641951631)
    ·
      refine ⟨71251559922964733462927447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47501039948643155641951631 71251559922964733462927447)
      ·
        refine ⟨106877339884447100194391171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71251559922964733462927447 106877339884447100194391171)
        ·
          refine ⟨160316009826670650291586757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106877339884447100194391171 160316009826670650291586757)
          ·
            refine ⟨30059251842500746929672517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160316009826670650291586757 30059251842500746929672517)
            ·
              refine ⟨5636109720468890049313597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30059251842500746929672517 5636109720468890049313597)
              ·
                refine ⟨2113541145175833768492599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5636109720468890049313597 2113541145175833768492599)
                ·
                  refine ⟨3170311717763750652738899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113541145175833768492599 3170311717763750652738899)
                  ·
                    refine ⟨4755467576645625979108349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3170311717763750652738899 4755467576645625979108349)
                    ·
                      refine ⟨1783300341242109742165631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755467576645625979108349 1783300341242109742165631)
                      ·
                        rfl

theorem cell23_3472965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_3472965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472965 prefixEnd_3472965 := by exact prefixLift 3472965
  have htrace : WordTrace (prefixWord ++ tailWord_3472965) baseStart_3472965 baseEnd_3472965 := by
    simpa [prefixWord, tailWord_3472965, baseEnd_3472965] using wordTrace_append hprefix tailTrace_3472965
  have hstable : (prefixWord ++ tailWord_3472965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472965).length < 2 ^ (prefixWord ++ tailWord_3472965).sum := by decide
  have hdescent : baseEnd_3472965 < baseStart_3472965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472984 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_3472984 : Nat := 118140960795 + 3472984 * 2 ^ 59
def prefixEnd_3472984 : Nat := 4983230072969 + 3 ^ 40 * 3472984 * 2
def baseEnd_3472984 : Nat := 1783310097374545167828043

theorem tailTrace_3472984 : CollatzResearch.WordTrace tailWord_3472984 prefixEnd_3472984 1783310097374545167828043 := by
  unfold tailWord_3472984
  simp only [CollatzResearch.WordTrace]
  refine ⟨63335066424989790645073003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84446755233319720860097337 63335066424989790645073003)
  ·
    refine ⟨95002599637484685967609505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63335066424989790645073003 95002599637484685967609505)
    ·
      refine ⟨71251949728113514475707129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95002599637484685967609505 71251949728113514475707129)
      ·
        refine ⟨53438962296085135856780347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71251949728113514475707129 53438962296085135856780347)
        ·
          refine ⟨80158443444127703785170521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53438962296085135856780347 80158443444127703785170521)
          ·
            refine ⟨60118832583095777838877891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80158443444127703785170521 60118832583095777838877891)
            ·
              refine ⟨90178248874643666758316837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60118832583095777838877891 90178248874643666758316837)
              ·
                refine ⟨16908421663995687517184407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90178248874643666758316837 16908421663995687517184407)
                ·
                  refine ⟨25362632495993531275776611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16908421663995687517184407 25362632495993531275776611)
                  ·
                    refine ⟨38043948743990296913664917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25362632495993531275776611 38043948743990296913664917)
                    ·
                      refine ⟨1783310097374545167828043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38043948743990296913664917 1783310097374545167828043)
                      ·
                        rfl

theorem cell23_3472984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_3472984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3472984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3472984 prefixEnd_3472984 := by exact prefixLift 3472984
  have htrace : WordTrace (prefixWord ++ tailWord_3472984) baseStart_3472984 baseEnd_3472984 := by
    simpa [prefixWord, tailWord_3472984, baseEnd_3472984] using wordTrace_append hprefix tailTrace_3472984
  have hstable : (prefixWord ++ tailWord_3472984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472984).length < 2 ^ (prefixWord ++ tailWord_3472984).sum := by decide
  have hdescent : baseEnd_3472984 < baseStart_3472984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473001 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_3473001 : Nat := 118140960795 + 3473001 * 2 ^ 59
def prefixEnd_3473001 : Nat := 4983230072969 + 3 ^ 40 * 3473001 * 2
def baseEnd_3473001 : Nat := 1783318826545671601315465

theorem tailTrace_3473001 : CollatzResearch.WordTrace tailWord_3473001 prefixEnd_3473001 1783318826545671601315465 := by
  unfold tailWord_3473001
  simp only [CollatzResearch.WordTrace]
  refine ⟨126670752890917993193514857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84447168593945328795676571 126670752890917993193514857)
  ·
    refine ⟨95003064668188494895136143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126670752890917993193514857 95003064668188494895136143)
    ·
      refine ⟨142504597002282742342704215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95003064668188494895136143 142504597002282742342704215)
      ·
        refine ⟨213756895503424113514056323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142504597002282742342704215 213756895503424113514056323)
        ·
          refine ⟨320635343255136170271084485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213756895503424113514056323 320635343255136170271084485)
          ·
            refine ⟨60119126860338031925828341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320635343255136170271084485 60119126860338031925828341)
            ·
              refine ⟨5636168143156690493046407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60119126860338031925828341 5636168143156690493046407)
              ·
                refine ⟨8454252214735035739569611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636168143156690493046407 8454252214735035739569611)
                ·
                  refine ⟨12681378322102553609354417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8454252214735035739569611 12681378322102553609354417)
                  ·
                    refine ⟨9511033741576915207015813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12681378322102553609354417 9511033741576915207015813)
                    ·
                      refine ⟨1783318826545671601315465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9511033741576915207015813 1783318826545671601315465)
                      ·
                        rfl

theorem cell23_3473001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_3473001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473001 prefixEnd_3473001 := by exact prefixLift 3473001
  have htrace : WordTrace (prefixWord ++ tailWord_3473001) baseStart_3473001 baseEnd_3473001 := by
    simpa [prefixWord, tailWord_3473001, baseEnd_3473001] using wordTrace_append hprefix tailTrace_3473001
  have hstable : (prefixWord ++ tailWord_3473001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473001).length < 2 ^ (prefixWord ++ tailWord_3473001).sum := by decide
  have hdescent : baseEnd_3473001 < baseStart_3473001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473005 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3473005 : Nat := 118140960795 + 3473005 * 2 ^ 59
def prefixEnd_3473005 : Nat := 4983230072969 + 3 ^ 40 * 3473005 * 2
def baseEnd_3473005 : Nat := 1783320880468289585665447

theorem tailTrace_3473005 : CollatzResearch.WordTrace tailWord_3473005 prefixEnd_3473005 1783320880468289585665447 := by
  unfold tailWord_3473005
  simp only [CollatzResearch.WordTrace]
  refine ⟨126670898782903501876660469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84447265855269001251106979 126670898782903501876660469)
  ·
    refine ⟨11875396760897203300936919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126670898782903501876660469 11875396760897203300936919)
    ·
      refine ⟨17813095141345804951405379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11875396760897203300936919 17813095141345804951405379)
      ·
        refine ⟨26719642712018707427108069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17813095141345804951405379 26719642712018707427108069)
        ·
          refine ⟨5009933008503507642582763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26719642712018707427108069 5009933008503507642582763)
          ·
            refine ⟨7514899512755261463874145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009933008503507642582763 7514899512755261463874145)
            ·
              refine ⟨5636174634566446097905609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7514899512755261463874145 5636174634566446097905609)
              ·
                refine ⟨4227130975924834573429207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636174634566446097905609 4227130975924834573429207)
                ·
                  refine ⟨6340696463887251860143811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227130975924834573429207 6340696463887251860143811)
                  ·
                    refine ⟨9511044695830877790215717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6340696463887251860143811 9511044695830877790215717)
                    ·
                      refine ⟨1783320880468289585665447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9511044695830877790215717 1783320880468289585665447)
                      ·
                        rfl

theorem cell23_3473005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3473005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473005 prefixEnd_3473005 := by exact prefixLift 3473005
  have htrace : WordTrace (prefixWord ++ tailWord_3473005) baseStart_3473005 baseEnd_3473005 := by
    simpa [prefixWord, tailWord_3473005, baseEnd_3473005] using wordTrace_append hprefix tailTrace_3473005
  have hstable : (prefixWord ++ tailWord_3473005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473005).length < 2 ^ (prefixWord ++ tailWord_3473005).sum := by decide
  have hdescent : baseEnd_3473005 < baseStart_3473005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473008 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3]
def baseStart_3473008 : Nat := 118140960795 + 3473008 * 2 ^ 59
def prefixEnd_3473008 : Nat := 4983230072969 + 3 ^ 40 * 3473008 * 2
def baseEnd_3473008 : Nat := 1783322420910253073927933

theorem tailTrace_3473008 : CollatzResearch.WordTrace tailWord_3473008 prefixEnd_3473008 1783322420910253073927933 := by
  unfold tailWord_3473008
  simp only [CollatzResearch.WordTrace]
  refine ⟨63335504100946316694509839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84447338801261755592679785 63335504100946316694509839)
  ·
    refine ⟨95003256151419475041764759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63335504100946316694509839 95003256151419475041764759)
    ·
      refine ⟨142504884227129212562647139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95003256151419475041764759 142504884227129212562647139)
      ·
        refine ⟨213757326340693818843970709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142504884227129212562647139 213757326340693818843970709)
        ·
          refine ⟨10019874672220022758311127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213757326340693818843970709 10019874672220022758311127)
          ·
            refine ⟨15029812008330034137466691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019874672220022758311127 15029812008330034137466691)
            ·
              refine ⟨22544718012495051206200037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15029812008330034137466691 22544718012495051206200037)
              ·
                refine ⟨4227134627342822101162507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22544718012495051206200037 4227134627342822101162507)
                ·
                  refine ⟨6340701941014233151743761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227134627342822101162507 6340701941014233151743761)
                  ·
                    refine ⟨4755526455760674863807821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6340701941014233151743761 4755526455760674863807821)
                    ·
                      refine ⟨1783322420910253073927933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755526455760674863807821 1783322420910253073927933)
                      ·
                        rfl

theorem cell23_3473008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_3473008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473008 prefixEnd_3473008 := by exact prefixLift 3473008
  have htrace : WordTrace (prefixWord ++ tailWord_3473008) baseStart_3473008 baseEnd_3473008 := by
    simpa [prefixWord, tailWord_3473008, baseEnd_3473008] using wordTrace_append hprefix tailTrace_3473008
  have hstable : (prefixWord ++ tailWord_3473008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473008).length < 2 ^ (prefixWord ++ tailWord_3473008).sum := by decide
  have hdescent : baseEnd_3473008 < baseStart_3473008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473028 : List Nat := [2, 3, 2, 1, 5, 1, 9]
def baseStart_3473028 : Nat := 118140960795 + 3473028 * 2 ^ 59
def prefixEnd_3473028 : Nat := 4983230072969 + 3 ^ 40 * 3473028 * 2
def baseEnd_3473028 : Nat := 22016452969423987600961

theorem tailTrace_3473028 : CollatzResearch.WordTrace tailWord_3473028 prefixEnd_3473028 22016452969423987600961 := by
  unfold tailWord_3473028
  simp only [CollatzResearch.WordTrace]
  refine ⟨63335868830910088402373869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84447825107880117869831825 63335868830910088402373869)
  ·
    refine ⟨23750950811591283150890201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63335868830910088402373869 23750950811591283150890201)
    ·
      refine ⟨17813213108693462363167651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23750950811591283150890201 17813213108693462363167651)
      ·
        refine ⟨26719819663040193544751477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17813213108693462363167651 26719819663040193544751477)
        ·
          refine ⟨2504983093410018144820451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26719819663040193544751477 2504983093410018144820451)
          ·
            refine ⟨3757474640115027217230677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504983093410018144820451 3757474640115027217230677)
            ·
              refine ⟨22016452969423987600961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3757474640115027217230677 22016452969423987600961)
              ·
                rfl

theorem cell23_3473028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 9].length) (baseStart_3473028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473028 prefixEnd_3473028 := by exact prefixLift 3473028
  have htrace : WordTrace (prefixWord ++ tailWord_3473028) baseStart_3473028 baseEnd_3473028 := by
    simpa [prefixWord, tailWord_3473028, baseEnd_3473028] using wordTrace_append hprefix tailTrace_3473028
  have hstable : (prefixWord ++ tailWord_3473028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473028).length < 2 ^ (prefixWord ++ tailWord_3473028).sum := by decide
  have hdescent : baseEnd_3473028 < baseStart_3473028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473081 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3473081 : Nat := 118140960795 + 3473081 * 2 ^ 59
def prefixEnd_3473081 : Nat := 4983230072969 + 3 ^ 40 * 3473081 * 2
def baseEnd_3473081 : Nat := 1783359904998031288315097

theorem tailTrace_3473081 : CollatzResearch.WordTrace tailWord_3473081 prefixEnd_3473081 1783359904998031288315097 := by
  unfold tailWord_3473081
  simp only [CollatzResearch.WordTrace]
  refine ⟨126673670730628166856427097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84449113820418777904284731 126673670730628166856427097)
  ·
    refine ⟨95005253047971125142320323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126673670730628166856427097 95005253047971125142320323)
    ·
      refine ⟨142507879571956687713480485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95005253047971125142320323 142507879571956687713480485)
      ·
        refine ⟨26720227419741878946277591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142507879571956687713480485 26720227419741878946277591)
        ·
          refine ⟨40080341129612818419416387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26720227419741878946277591 40080341129612818419416387)
          ·
            refine ⟨60120511694419227629124581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40080341129612818419416387 60120511694419227629124581)
            ·
              refine ⟨11272595942703605180460859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60120511694419227629124581 11272595942703605180460859)
              ·
                refine ⟨16908893914055407770691289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11272595942703605180460859 16908893914055407770691289)
                ·
                  refine ⟨12681670435541555828018467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16908893914055407770691289 12681670435541555828018467)
                  ·
                    refine ⟨19022505653312333742027701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12681670435541555828018467 19022505653312333742027701)
                    ·
                      refine ⟨1783359904998031288315097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19022505653312333742027701 1783359904998031288315097)
                      ·
                        rfl

theorem cell23_3473081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3473081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473081 prefixEnd_3473081 := by exact prefixLift 3473081
  have htrace : WordTrace (prefixWord ++ tailWord_3473081) baseStart_3473081 baseEnd_3473081 := by
    simpa [prefixWord, tailWord_3473081, baseEnd_3473081] using wordTrace_append hprefix tailTrace_3473081
  have hstable : (prefixWord ++ tailWord_3473081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473081).length < 2 ^ (prefixWord ++ tailWord_3473081).sum := by decide
  have hdescent : baseEnd_3473081 < baseStart_3473081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473082 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2]
def baseStart_3473082 : Nat := 118140960795 + 3473082 * 2 ^ 59
def prefixEnd_3473082 : Nat := 4983230072969 + 3 ^ 40 * 3473082 * 2
def baseEnd_3473082 : Nat := 1783360418478685784402593

theorem tailTrace_3473082 : CollatzResearch.WordTrace tailWord_3473082 prefixEnd_3473082 1783360418478685784402593 := by
  unfold tailWord_3473082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31668426800906136006803375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84449138135749696018142333 31668426800906136006803375)
  ·
    refine ⟨47502640201359204010205063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31668426800906136006803375 47502640201359204010205063)
    ·
      refine ⟨71253960302038806015307595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47502640201359204010205063 71253960302038806015307595)
      ·
        refine ⟨106880940453058209022961393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71253960302038806015307595 106880940453058209022961393)
        ·
          refine ⟨80160705339793656767221045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106880940453058209022961393 80160705339793656767221045)
          ·
            refine ⟨7515066125605655321926973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80160705339793656767221045 7515066125605655321926973)
            ·
              refine ⟨2818149797102120745722615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7515066125605655321926973 2818149797102120745722615)
              ·
                refine ⟨4227224695653181118583923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818149797102120745722615 4227224695653181118583923)
                ·
                  refine ⟨6340837043479771677875885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227224695653181118583923 6340837043479771677875885)
                  ·
                    refine ⟨2377813891304914379203457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6340837043479771677875885 2377813891304914379203457)
                    ·
                      refine ⟨1783360418478685784402593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2377813891304914379203457 1783360418478685784402593)
                      ·
                        rfl

theorem cell23_3473082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_3473082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473082 prefixEnd_3473082 := by exact prefixLift 3473082
  have htrace : WordTrace (prefixWord ++ tailWord_3473082) baseStart_3473082 baseEnd_3473082 := by
    simpa [prefixWord, tailWord_3473082, baseEnd_3473082] using wordTrace_append hprefix tailTrace_3473082
  have hstable : (prefixWord ++ tailWord_3473082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473082).length < 2 ^ (prefixWord ++ tailWord_3473082).sum := by decide
  have hdescent : baseEnd_3473082 < baseStart_3473082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473108 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3473108 : Nat := 118140960795 + 3473108 * 2 ^ 59
def prefixEnd_3473108 : Nat := 4983230072969 + 3 ^ 40 * 3473108 * 2
def baseEnd_3473108 : Nat := 1783373768975702682677473

theorem tailTrace_3473108 : CollatzResearch.WordTrace tailWord_3473108 prefixEnd_3473108 1783373768975702682677473 := by
  unfold tailWord_3473108
  simp only [CollatzResearch.WordTrace]
  refine ⟨63337327750765175233829989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84449770334353566978439985 63337327750765175233829989)
  ·
    refine ⟨11875748953268470356343123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63337327750765175233829989 11875748953268470356343123)
    ·
      refine ⟨17813623429902705534514685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11875748953268470356343123 17813623429902705534514685)
      ·
        refine ⟨6680108786213514575443007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17813623429902705534514685 6680108786213514575443007)
        ·
          refine ⟨10020163179320271863164511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680108786213514575443007 10020163179320271863164511)
          ·
            refine ⟨15030244768980407794746767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10020163179320271863164511 15030244768980407794746767)
            ·
              refine ⟨22545367153470611692120151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15030244768980407794746767 22545367153470611692120151)
              ·
                refine ⟨33818050730205917538180227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22545367153470611692120151 33818050730205917538180227)
                ·
                  refine ⟨50727076095308876307270341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33818050730205917538180227 50727076095308876307270341)
                  ·
                    refine ⟨9511326767870414307613189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50727076095308876307270341 9511326767870414307613189)
                    ·
                      refine ⟨1783373768975702682677473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9511326767870414307613189 1783373768975702682677473)
                      ·
                        rfl

theorem cell23_3473108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3473108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473108 prefixEnd_3473108 := by exact prefixLift 3473108
  have htrace : WordTrace (prefixWord ++ tailWord_3473108) baseStart_3473108 baseEnd_3473108 := by
    simpa [prefixWord, tailWord_3473108, baseEnd_3473108] using wordTrace_append hprefix tailTrace_3473108
  have hstable : (prefixWord ++ tailWord_3473108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473108).length < 2 ^ (prefixWord ++ tailWord_3473108).sum := by decide
  have hdescent : baseEnd_3473108 < baseStart_3473108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473269 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3473269 : Nat := 118140960795 + 3473269 * 2 ^ 59
def prefixEnd_3473269 : Nat := 4983230072969 + 3 ^ 40 * 3473269 * 2
def baseEnd_3473269 : Nat := 1783456439361076552764233

theorem tailTrace_3473269 : CollatzResearch.WordTrace tailWord_3473269 prefixEnd_3473269 1783456439361076552764233 := by
  unfold tailWord_3473269
  simp only [CollatzResearch.WordTrace]
  refine ⟨126680527653947074964270861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84453685102631383309513907 126680527653947074964270861)
  ·
    refine ⟨47505197870230153111601573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126680527653947074964270861 47505197870230153111601573)
    ·
      refine ⟨8907224600668153708425295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47505197870230153111601573 8907224600668153708425295)
      ·
        refine ⟨13360836901002230562637943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907224600668153708425295 13360836901002230562637943)
        ·
          refine ⟨20041255351503345843956915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13360836901002230562637943 20041255351503345843956915)
          ·
            refine ⟨30061883027255018765935373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20041255351503345843956915 30061883027255018765935373)
            ·
              refine ⟨11273206135220632037225765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30061883027255018765935373 11273206135220632037225765)
              ·
                refine ⟨2113726150353868506979831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11273206135220632037225765 2113726150353868506979831)
                ·
                  refine ⟨3170589225530802760469747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113726150353868506979831 3170589225530802760469747)
                  ·
                    refine ⟨4755883838296204140704621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3170589225530802760469747 4755883838296204140704621)
                    ·
                      refine ⟨1783456439361076552764233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755883838296204140704621 1783456439361076552764233)
                      ·
                        rfl

theorem cell23_3473269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3473269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473269 prefixEnd_3473269 := by exact prefixLift 3473269
  have htrace : WordTrace (prefixWord ++ tailWord_3473269) baseStart_3473269 baseEnd_3473269 := by
    simpa [prefixWord, tailWord_3473269, baseEnd_3473269] using wordTrace_append hprefix tailTrace_3473269
  have hstable : (prefixWord ++ tailWord_3473269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473269).length < 2 ^ (prefixWord ++ tailWord_3473269).sum := by decide
  have hdescent : baseEnd_3473269 < baseStart_3473269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473285 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_3473285 : Nat := 118140960795 + 3473285 * 2 ^ 59
def prefixEnd_3473285 : Nat := 4983230072969 + 3 ^ 40 * 3473285 * 2
def baseEnd_3473285 : Nat := 594488218350516163388053

theorem tailTrace_3473285 : CollatzResearch.WordTrace tailWord_3473285 prefixEnd_3473285 594488218350516163388053 := by
  unfold tailWord_3473285
  simp only [CollatzResearch.WordTrace]
  refine ⟨126681111221889109696853309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84454074147926073131235539 126681111221889109696853309)
  ·
    refine ⟨47505416708208416136319991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126681111221889109696853309 47505416708208416136319991)
    ·
      refine ⟨71258125062312624204479987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47505416708208416136319991 71258125062312624204479987)
      ·
        refine ⟨106887187593468936306719981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71258125062312624204479987 106887187593468936306719981)
        ·
          refine ⟨40082695347550851115019993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106887187593468936306719981 40082695347550851115019993)
          ·
            refine ⟨30062021510663138336264995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40082695347550851115019993 30062021510663138336264995)
            ·
              refine ⟨45093032265994707504397493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30062021510663138336264995 45093032265994707504397493)
              ·
                refine ⟨4227471774937003828537265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45093032265994707504397493 4227471774937003828537265)
                ·
                  refine ⟨3170603831202752871402949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4227471774937003828537265 3170603831202752871402949)
                  ·
                    refine ⟨594488218350516163388053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3170603831202752871402949 594488218350516163388053)
                    ·
                      rfl

theorem cell23_3473285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_3473285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473285 prefixEnd_3473285 := by exact prefixLift 3473285
  have htrace : WordTrace (prefixWord ++ tailWord_3473285) baseStart_3473285 baseEnd_3473285 := by
    simpa [prefixWord, tailWord_3473285, baseEnd_3473285] using wordTrace_append hprefix tailTrace_3473285
  have hstable : (prefixWord ++ tailWord_3473285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473285).length < 2 ^ (prefixWord ++ tailWord_3473285).sum := by decide
  have hdescent : baseEnd_3473285 < baseStart_3473285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473309 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_3473309 : Nat := 118140960795 + 3473309 * 2 ^ 59
def prefixEnd_3473309 : Nat := 4983230072969 + 3 ^ 40 * 3473309 * 2
def baseEnd_3473309 : Nat := 1783476978587256396264049

theorem tailTrace_3473309 : CollatzResearch.WordTrace tailWord_3473309 prefixEnd_3473309 1783476978587256396264049 := by
  unfold tailWord_3473309
  simp only [CollatzResearch.WordTrace]
  refine ⟨126681986573802161795726981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84454657715868107863817987 126681986573802161795726981)
  ·
    refine ⟨23752872482587905336698809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126681986573802161795726981 23752872482587905336698809)
    ·
      refine ⟨17814654361940929002524107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23752872482587905336698809 17814654361940929002524107)
      ·
        refine ⟨26721981542911393503786161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17814654361940929002524107 26721981542911393503786161)
        ·
          refine ⟨20041486157183545127839621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26721981542911393503786161 20041486157183545127839621)
          ·
            refine ⟨3757778654471914711469929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20041486157183545127839621 3757778654471914711469929)
            ·
              refine ⟨2818333990853936033602447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3757778654471914711469929 2818333990853936033602447)
              ·
                refine ⟨4227500986280904050403671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818333990853936033602447 4227500986280904050403671)
                ·
                  refine ⟨6341251479421356075605507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227500986280904050403671 6341251479421356075605507)
                  ·
                    refine ⟨9511877219132034113408261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6341251479421356075605507 9511877219132034113408261)
                    ·
                      refine ⟨1783476978587256396264049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9511877219132034113408261 1783476978587256396264049)
                      ·
                        rfl

theorem cell23_3473309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_3473309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473309 prefixEnd_3473309 := by exact prefixLift 3473309
  have htrace : WordTrace (prefixWord ++ tailWord_3473309) baseStart_3473309 baseEnd_3473309 := by
    simpa [prefixWord, tailWord_3473309, baseEnd_3473309] using wordTrace_append hprefix tailTrace_3473309
  have hstable : (prefixWord ++ tailWord_3473309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473309).length < 2 ^ (prefixWord ++ tailWord_3473309).sum := by decide
  have hdescent : baseEnd_3473309 < baseStart_3473309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473319 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3473319 : Nat := 118140960795 + 3473319 * 2 ^ 59
def prefixEnd_3473319 : Nat := 4983230072969 + 3 ^ 40 * 3473319 * 2
def baseEnd_3473319 : Nat := 594494037797933785713001

theorem tailTrace_3473319 : CollatzResearch.WordTrace tailWord_3473319 prefixEnd_3473319 594494037797933785713001 := by
  unfold tailWord_3473319
  simp only [CollatzResearch.WordTrace]
  refine ⟨126682351303765933503591011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84454900869177289002394007 126682351303765933503591011)
  ·
    refine ⟨190023526955648900255386517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126682351303765933503591011 190023526955648900255386517)
    ·
      refine ⟨8907352826046042199471243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190023526955648900255386517 8907352826046042199471243)
      ·
        refine ⟨13361029239069063299206865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907352826046042199471243 13361029239069063299206865)
        ·
          refine ⟨10020771929301797474405149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13361029239069063299206865 10020771929301797474405149)
          ·
            refine ⟨3757789473488174052901931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10020771929301797474405149 3757789473488174052901931)
            ·
              refine ⟨5636684210232261079352897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757789473488174052901931 5636684210232261079352897)
              ·
                refine ⟨4227513157674195809514673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636684210232261079352897 4227513157674195809514673)
                ·
                  refine ⟨3170634868255646857136005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4227513157674195809514673 3170634868255646857136005)
                  ·
                    refine ⟨594494037797933785713001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3170634868255646857136005 594494037797933785713001)
                    ·
                      rfl

theorem cell23_3473319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3473319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473319 prefixEnd_3473319 := by exact prefixLift 3473319
  have htrace : WordTrace (prefixWord ++ tailWord_3473319) baseStart_3473319 baseEnd_3473319 := by
    simpa [prefixWord, tailWord_3473319, baseEnd_3473319] using wordTrace_append hprefix tailTrace_3473319
  have hstable : (prefixWord ++ tailWord_3473319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473319).length < 2 ^ (prefixWord ++ tailWord_3473319).sum := by decide
  have hdescent : baseEnd_3473319 < baseStart_3473319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473342 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3473342 : Nat := 118140960795 + 3473342 * 2 ^ 59
def prefixEnd_3473342 : Nat := 4983230072969 + 3 ^ 40 * 3473342 * 2
def baseEnd_3473342 : Nat := 1783493923448854767151397

theorem tailTrace_3473342 : CollatzResearch.WordTrace tailWord_3473342 prefixEnd_3473342 1783493923448854767151397 := by
  unfold tailWord_3473342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835398772835326053959785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84455460121788405621118853 15835398772835326053959785)
  ·
    refine ⟨11876549079626494540469839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15835398772835326053959785 11876549079626494540469839)
    ·
      refine ⟨17814823619439741810704759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876549079626494540469839 17814823619439741810704759)
      ·
        refine ⟨26722235429159612716057139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17814823619439741810704759 26722235429159612716057139)
        ·
          refine ⟨40083353143739419074085709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26722235429159612716057139 40083353143739419074085709)
          ·
            refine ⟨15031257428902282152782141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40083353143739419074085709 15031257428902282152782141)
            ·
              refine ⟨5636721535838355807293303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15031257428902282152782141 5636721535838355807293303)
              ·
                refine ⟨8455082303757533710939955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636721535838355807293303 8455082303757533710939955)
                ·
                  refine ⟨12682623455636300566409933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8455082303757533710939955 12682623455636300566409933)
                  ·
                    refine ⟨4755983795863612712403725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12682623455636300566409933 4755983795863612712403725)
                    ·
                      refine ⟨1783493923448854767151397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4755983795863612712403725 1783493923448854767151397)
                      ·
                        rfl

theorem cell23_3473342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3473342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473342 prefixEnd_3473342 := by exact prefixLift 3473342
  have htrace : WordTrace (prefixWord ++ tailWord_3473342) baseStart_3473342 baseEnd_3473342 := by
    simpa [prefixWord, tailWord_3473342, baseEnd_3473342] using wordTrace_append hprefix tailTrace_3473342
  have hstable : (prefixWord ++ tailWord_3473342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473342).length < 2 ^ (prefixWord ++ tailWord_3473342).sum := by decide
  have hdescent : baseEnd_3473342 < baseStart_3473342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473393 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 2, 1, 3]
def baseStart_3473393 : Nat := 118140960795 + 3473393 * 2 ^ 59
def prefixEnd_3473393 : Nat := 4983230072969 + 3 ^ 40 * 3473393 * 2
def baseEnd_3473393 : Nat := 1783520110962234067613663

theorem tailTrace_3473393 : CollatzResearch.WordTrace tailWord_3473393 prefixEnd_3473393 1783520110962234067613663 := by
  unfold tailWord_3473393
  simp only [CollatzResearch.WordTrace]
  refine ⟨126685050305497844141784833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84456700203665229427856555 126685050305497844141784833)
  ·
    refine ⟨95013787729123383106338625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126685050305497844141784833 95013787729123383106338625)
    ·
      refine ⟨71260340796842537329753969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95013787729123383106338625 71260340796842537329753969)
      ·
        refine ⟨53445255597631902997315477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71260340796842537329753969 53445255597631902997315477)
        ·
          refine ⟨2505246356138995452999163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53445255597631902997315477 2505246356138995452999163)
          ·
            refine ⟨3757869534208493179498745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505246356138995452999163 3757869534208493179498745)
            ·
              refine ⟨2818402150656369884624059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3757869534208493179498745 2818402150656369884624059)
              ·
                refine ⟨4227603225984554826936089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818402150656369884624059 4227603225984554826936089)
                ·
                  refine ⟨3170702419488416120202067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4227603225984554826936089 3170702419488416120202067)
                  ·
                    refine ⟨4756053629232624180303101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3170702419488416120202067 4756053629232624180303101)
                    ·
                      refine ⟨1783520110962234067613663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4756053629232624180303101 1783520110962234067613663)
                      ·
                        rfl

theorem cell23_3473393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_3473393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473393 prefixEnd_3473393 := by exact prefixLift 3473393
  have htrace : WordTrace (prefixWord ++ tailWord_3473393) baseStart_3473393 baseEnd_3473393 := by
    simpa [prefixWord, tailWord_3473393, baseEnd_3473393] using wordTrace_append hprefix tailTrace_3473393
  have hstable : (prefixWord ++ tailWord_3473393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473393).length < 2 ^ (prefixWord ++ tailWord_3473393).sum := by decide
  have hdescent : baseEnd_3473393 < baseStart_3473393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473422 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_3473422 : Nat := 118140960795 + 3473422 * 2 ^ 59
def prefixEnd_3473422 : Nat := 4983230072969 + 3 ^ 40 * 3473422 * 2
def baseEnd_3473422 : Nat := 198170555766801606016781

theorem tailTrace_3473422 : CollatzResearch.WordTrace tailWord_3473422 prefixEnd_3473422 198170555766801606016781 := by
  unfold tailWord_3473422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835763502799097761823815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84457405348261854729727013 15835763502799097761823815)
  ·
    refine ⟨23753645254198646642735723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15835763502799097761823815 23753645254198646642735723)
    ·
      refine ⟨35630467881297969964103585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23753645254198646642735723 35630467881297969964103585)
      ·
        refine ⟨26722850910973477473077689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35630467881297969964103585 26722850910973477473077689)
        ·
          refine ⟨20042138183230108104808267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26722850910973477473077689 20042138183230108104808267)
          ·
            refine ⟨30063207274845162157212401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20042138183230108104808267 30063207274845162157212401)
            ·
              refine ⟨22547405456133871617909301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30063207274845162157212401 22547405456133871617909301)
              ·
                refine ⟨2113819261512550464178997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22547405456133871617909301 2113819261512550464178997)
                ·
                  refine ⟨198170555766801606016781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113819261512550464178997 198170555766801606016781)
                  ·
                    rfl

theorem cell23_3473422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_3473422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473422 prefixEnd_3473422 := by exact prefixLift 3473422
  have htrace : WordTrace (prefixWord ++ tailWord_3473422) baseStart_3473422 baseEnd_3473422 := by
    simpa [prefixWord, tailWord_3473422, baseEnd_3473422] using wordTrace_append hprefix tailTrace_3473422
  have hstable : (prefixWord ++ tailWord_3473422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473422).length < 2 ^ (prefixWord ++ tailWord_3473422).sum := by decide
  have hdescent : baseEnd_3473422 < baseStart_3473422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473442 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_3473442 : Nat := 118140960795 + 3473442 * 2 ^ 59
def prefixEnd_3473442 : Nat := 4983230072969 + 3 ^ 40 * 3473442 * 2
def baseEnd_3473442 : Nat := 1783545271514304375900937

theorem tailTrace_3473442 : CollatzResearch.WordTrace tailWord_3473442 prefixEnd_3473442 1783545271514304375900937 := by
  unfold tailWord_3473442
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671709370580081377579645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84457891654880217006879053 31671709370580081377579645)
  ·
    refine ⟨11876891013967530516592367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31671709370580081377579645 11876891013967530516592367)
    ·
      refine ⟨17815336520951295774888551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876891013967530516592367 17815336520951295774888551)
      ·
        refine ⟨26723004781426943662332827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17815336520951295774888551 26723004781426943662332827)
        ·
          refine ⟨40084507172140415493499241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26723004781426943662332827 40084507172140415493499241)
          ·
            refine ⟨30063380379105311620124431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40084507172140415493499241 30063380379105311620124431)
            ·
              refine ⟨45095070568657967430186647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30063380379105311620124431 45095070568657967430186647)
              ·
                refine ⟨67642605852986951145279971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45095070568657967430186647 67642605852986951145279971)
                ·
                  refine ⟨101463908779480426717919957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67642605852986951145279971 101463908779480426717919957)
                  ·
                    refine ⟨2378060362019072501201249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101463908779480426717919957 2378060362019072501201249)
                    ·
                      refine ⟨1783545271514304375900937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378060362019072501201249 1783545271514304375900937)
                      ·
                        rfl

theorem cell23_3473442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_3473442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473442 prefixEnd_3473442 := by exact prefixLift 3473442
  have htrace : WordTrace (prefixWord ++ tailWord_3473442) baseStart_3473442 baseEnd_3473442 := by
    simpa [prefixWord, tailWord_3473442, baseEnd_3473442] using wordTrace_append hprefix tailTrace_3473442
  have hstable : (prefixWord ++ tailWord_3473442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473442).length < 2 ^ (prefixWord ++ tailWord_3473442).sum := by decide
  have hdescent : baseEnd_3473442 < baseStart_3473442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473445 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3473445 : Nat := 118140960795 + 3473445 * 2 ^ 59
def prefixEnd_3473445 : Nat := 4983230072969 + 3 ^ 40 * 3473445 * 2
def baseEnd_3473445 : Nat := 1783546811956267864163423

theorem tailTrace_3473445 : CollatzResearch.WordTrace tailWord_3473445 prefixEnd_3473445 1783546811956267864163423 := by
  unfold tailWord_3473445
  simp only [CollatzResearch.WordTrace]
  refine ⟨126686946901309457022677789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84457964600872971348451859 126686946901309457022677789)
  ·
    refine ⟨47507605087991046383504171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126686946901309457022677789 47507605087991046383504171)
    ·
      refine ⟨71261407631986569575256257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47507605087991046383504171 71261407631986569575256257)
      ·
        refine ⟨53446055723989927181442193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71261407631986569575256257 53446055723989927181442193)
        ·
          refine ⟨40084541792992445386081645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53446055723989927181442193 40084541792992445386081645)
          ·
            refine ⟨15031703172372167019780617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40084541792992445386081645 15031703172372167019780617)
            ·
              refine ⟨11273777379279125264835463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15031703172372167019780617 11273777379279125264835463)
              ·
                refine ⟨16910666068918687897253195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11273777379279125264835463 16910666068918687897253195)
                ·
                  refine ⟨25365999103378031845879793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16910666068918687897253195 25365999103378031845879793)
                  ·
                    refine ⟨19024499327533523884409845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25365999103378031845879793 19024499327533523884409845)
                    ·
                      refine ⟨1783546811956267864163423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19024499327533523884409845 1783546811956267864163423)
                      ·
                        rfl

theorem cell23_3473445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3473445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473445 prefixEnd_3473445 := by exact prefixLift 3473445
  have htrace : WordTrace (prefixWord ++ tailWord_3473445) baseStart_3473445 baseEnd_3473445 := by
    simpa [prefixWord, tailWord_3473445, baseEnd_3473445] using wordTrace_append hprefix tailTrace_3473445
  have hstable : (prefixWord ++ tailWord_3473445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473445).length < 2 ^ (prefixWord ++ tailWord_3473445).sum := by decide
  have hdescent : baseEnd_3473445 < baseStart_3473445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473472 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_3473472 : Nat := 118140960795 + 3473472 * 2 ^ 59
def prefixEnd_3473472 : Nat := 4983230072969 + 3 ^ 40 * 3473472 * 2
def baseEnd_3473472 : Nat := 1783560675933939258525799

theorem tailTrace_3473472 : CollatzResearch.WordTrace tailWord_3473472 prefixEnd_3473472 1783560675933939258525799 := by
  unfold tailWord_3473472
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343965836105820316955335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84458621114807760422607113 63343965836105820316955335)
  ·
    refine ⟨95015948754158730475433003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63343965836105820316955335 95015948754158730475433003)
    ·
      refine ⟨142523923131238095713149505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95015948754158730475433003 142523923131238095713149505)
      ·
        refine ⟨106892942348428571784862129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142523923131238095713149505 106892942348428571784862129)
        ·
          refine ⟨80169706761321428838646597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106892942348428571784862129 80169706761321428838646597)
          ·
            refine ⟨15031820017747767907246237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80169706761321428838646597 15031820017747767907246237)
            ·
              refine ⟨5636932506655412965217339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15031820017747767907246237 5636932506655412965217339)
              ·
                refine ⟨8455398759983119447826009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636932506655412965217339 8455398759983119447826009)
                ·
                  refine ⟨6341549069987339585869507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8455398759983119447826009 6341549069987339585869507)
                  ·
                    refine ⟨9512323604981009378804261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6341549069987339585869507 9512323604981009378804261)
                    ·
                      refine ⟨1783560675933939258525799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9512323604981009378804261 1783560675933939258525799)
                      ·
                        rfl

theorem cell23_3473472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_3473472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473472 prefixEnd_3473472 := by exact prefixLift 3473472
  have htrace : WordTrace (prefixWord ++ tailWord_3473472) baseStart_3473472 baseEnd_3473472 := by
    simpa [prefixWord, tailWord_3473472, baseEnd_3473472] using wordTrace_append hprefix tailTrace_3473472
  have hstable : (prefixWord ++ tailWord_3473472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473472).length < 2 ^ (prefixWord ++ tailWord_3473472).sum := by decide
  have hdescent : baseEnd_3473472 < baseStart_3473472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473492 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_3473492 : Nat := 118140960795 + 3473492 * 2 ^ 59
def prefixEnd_3473492 : Nat := 4983230072969 + 3 ^ 40 * 3473492 * 2
def baseEnd_3473492 : Nat := 1783570945547029180275707

theorem tailTrace_3473492 : CollatzResearch.WordTrace tailWord_3473492 prefixEnd_3473492 1783570945547029180275707 := by
  unfold tailWord_3473492
  simp only [CollatzResearch.WordTrace]
  refine ⟨63344330566069592024819365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84459107421426122699759153 63344330566069592024819365)
  ·
    refine ⟨11877061981138048504653631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63344330566069592024819365 11877061981138048504653631)
    ·
      refine ⟨17815592971707072756980447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11877061981138048504653631 17815592971707072756980447)
      ·
        refine ⟨26723389457560609135470671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17815592971707072756980447 26723389457560609135470671)
        ·
          refine ⟨40085084186340913703206007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26723389457560609135470671 40085084186340913703206007)
          ·
            refine ⟨60127626279511370554809011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40085084186340913703206007 60127626279511370554809011)
            ·
              refine ⟨90191439419267055832213517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60127626279511370554809011 90191439419267055832213517)
              ·
                refine ⟨33821789782225145937080069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90191439419267055832213517 33821789782225145937080069)
                ·
                  refine ⟨6341585584167214863202513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33821789782225145937080069 6341585584167214863202513)
                  ·
                    refine ⟨4756189188125411147401885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6341585584167214863202513 4756189188125411147401885)
                    ·
                      refine ⟨1783570945547029180275707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4756189188125411147401885 1783570945547029180275707)
                      ·
                        rfl

theorem cell23_3473492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_3473492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473492 prefixEnd_3473492 := by exact prefixLift 3473492
  have htrace : WordTrace (prefixWord ++ tailWord_3473492) baseStart_3473492 baseEnd_3473492 := by
    simpa [prefixWord, tailWord_3473492, baseEnd_3473492] using wordTrace_append hprefix tailTrace_3473492
  have hstable : (prefixWord ++ tailWord_3473492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473492).length < 2 ^ (prefixWord ++ tailWord_3473492).sum := by decide
  have hdescent : baseEnd_3473492 < baseStart_3473492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473592 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_3473592 : Nat := 118140960795 + 3473592 * 2 ^ 59
def prefixEnd_3473592 : Nat := 4983230072969 + 3 ^ 40 * 3473592 * 2
def baseEnd_3473592 : Nat := 1783622293612478789025247

theorem tailTrace_3473592 : CollatzResearch.WordTrace tailWord_3473592 prefixEnd_3473592 1783622293612478789025247 := by
  unfold tailWord_3473592
  simp only [CollatzResearch.WordTrace]
  refine ⟨63346154215888450564139515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84461538954517934085519353 63346154215888450564139515)
  ·
    refine ⟨95019231323832675846209273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63346154215888450564139515 95019231323832675846209273)
    ·
      refine ⟨71264423492874506884656955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95019231323832675846209273 71264423492874506884656955)
      ·
        refine ⟨106896635239311760326985433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71264423492874506884656955 106896635239311760326985433)
        ·
          refine ⟨80172476429483820245239075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106896635239311760326985433 80172476429483820245239075)
          ·
            refine ⟨120258714644225730367858613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80172476429483820245239075 120258714644225730367858613)
            ·
              refine ⟨11274254497896162221986745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120258714644225730367858613 11274254497896162221986745)
              ·
                refine ⟨8455690873422121666490059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11274254497896162221986745 8455690873422121666490059)
                ·
                  refine ⟨12683536310133182499735089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8455690873422121666490059 12683536310133182499735089)
                  ·
                    refine ⟨9512652232599886874801317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12683536310133182499735089 9512652232599886874801317)
                    ·
                      refine ⟨1783622293612478789025247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9512652232599886874801317 1783622293612478789025247)
                      ·
                        rfl

theorem cell23_3473592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_3473592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473592 prefixEnd_3473592 := by exact prefixLift 3473592
  have htrace : WordTrace (prefixWord ++ tailWord_3473592) baseStart_3473592 baseEnd_3473592 := by
    simpa [prefixWord, tailWord_3473592, baseEnd_3473592] using wordTrace_append hprefix tailTrace_3473592
  have hstable : (prefixWord ++ tailWord_3473592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473592).length < 2 ^ (prefixWord ++ tailWord_3473592).sum := by decide
  have hdescent : baseEnd_3473592 < baseStart_3473592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473615 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 9]
def baseStart_3473615 : Nat := 118140960795 + 3473615 * 2 ^ 59
def prefixEnd_3473615 : Nat := 4983230072969 + 3 ^ 40 * 3473615 * 2
def baseEnd_3473615 : Nat := 594544701222510733012547

theorem tailTrace_3473615 : CollatzResearch.WordTrace tailWord_3473615 prefixEnd_3473615 594544701222510733012547 := by
  unfold tailWord_3473615
  simp only [CollatzResearch.WordTrace]
  refine ⟨126693147310693576056366299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84462098207129050704244199 126693147310693576056366299)
  ·
    refine ⟨190039720966040364084549449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126693147310693576056366299 190039720966040364084549449)
    ·
      refine ⟨142529790724530273063412087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190039720966040364084549449 142529790724530273063412087)
      ·
        refine ⟨213794686086795409595118131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142529790724530273063412087 213794686086795409595118131)
        ·
          refine ⟨320692029130193114392677197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213794686086795409595118131 320692029130193114392677197)
          ·
            refine ⟨120259510923822417897253949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320692029130193114392677197 120259510923822417897253949)
            ·
              refine ⟨45097316596433406711470231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120259510923822417897253949 45097316596433406711470231)
              ·
                refine ⟨67645974894650110067205347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45097316596433406711470231 67645974894650110067205347)
                ·
                  refine ⟨101468962341975165100808021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67645974894650110067205347 101468962341975165100808021)
                  ·
                    refine ⟨594544701222510733012547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 101468962341975165100808021 594544701222510733012547)
                    ·
                      rfl

theorem cell23_3473615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_3473615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473615 prefixEnd_3473615 := by exact prefixLift 3473615
  have htrace : WordTrace (prefixWord ++ tailWord_3473615) baseStart_3473615 baseEnd_3473615 := by
    simpa [prefixWord, tailWord_3473615, baseEnd_3473615] using wordTrace_append hprefix tailTrace_3473615
  have hstable : (prefixWord ++ tailWord_3473615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473615).length < 2 ^ (prefixWord ++ tailWord_3473615).sum := by decide
  have hdescent : baseEnd_3473615 < baseStart_3473615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473634 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3473634 : Nat := 118140960795 + 3473634 * 2 ^ 59
def prefixEnd_3473634 : Nat := 4983230072969 + 3 ^ 40 * 3473634 * 2
def baseEnd_3473634 : Nat := 1783643859799967624700055

theorem tailTrace_3473634 : CollatzResearch.WordTrace tailWord_3473634 prefixEnd_3473634 1783643859799967624700055 := by
  unfold tailWord_3473634
  simp only [CollatzResearch.WordTrace]
  refine ⟨31673460074406185575326989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84462560198416494867538637 31673460074406185575326989)
  ·
    refine ⟨11877547527902319590747621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31673460074406185575326989 11877547527902319590747621)
    ·
      refine ⟨2227040161481684923265179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11877547527902319590747621 2227040161481684923265179)
      ·
        refine ⟨3340560242222527384897769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227040161481684923265179 3340560242222527384897769)
        ·
          refine ⟨2505420181666895538673327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340560242222527384897769 2505420181666895538673327)
          ·
            refine ⟨3758130272500343308009991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505420181666895538673327 3758130272500343308009991)
            ·
              refine ⟨5637195408750514962014987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758130272500343308009991 5637195408750514962014987)
              ·
                refine ⟨8455793113125772443022481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637195408750514962014987 8455793113125772443022481)
                ·
                  refine ⟨6341844834844329332266861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8455793113125772443022481 6341844834844329332266861)
                  ·
                    refine ⟨2378191813066623499600073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6341844834844329332266861 2378191813066623499600073)
                    ·
                      refine ⟨1783643859799967624700055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378191813066623499600073 1783643859799967624700055)
                      ·
                        rfl

theorem cell23_3473634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3473634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473634 prefixEnd_3473634 := by exact prefixLift 3473634
  have htrace : WordTrace (prefixWord ++ tailWord_3473634) baseStart_3473634 baseEnd_3473634 := by
    simpa [prefixWord, tailWord_3473634, baseEnd_3473634] using wordTrace_append hprefix tailTrace_3473634
  have hstable : (prefixWord ++ tailWord_3473634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473634).length < 2 ^ (prefixWord ++ tailWord_3473634).sum := by decide
  have hdescent : baseEnd_3473634 < baseStart_3473634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473642 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_3473642 : Nat := 118140960795 + 3473642 * 2 ^ 59
def prefixEnd_3473642 : Nat := 4983230072969 + 3 ^ 40 * 3473642 * 2
def baseEnd_3473642 : Nat := 1783647967645203593400017

theorem tailTrace_3473642 : CollatzResearch.WordTrace tailWord_3473642 prefixEnd_3473642 1783647967645203593400017 := by
  unfold tailWord_3473642
  simp only [CollatzResearch.WordTrace]
  refine ⟨31673533020398939916899795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84462754721063839778399453 31673533020398939916899795)
  ·
    refine ⟨47510299530598409875349693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31673533020398939916899795 47510299530598409875349693)
    ·
      refine ⟨17816362323974403703256135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47510299530598409875349693 17816362323974403703256135)
      ·
        refine ⟨26724543485961605554884203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17816362323974403703256135 26724543485961605554884203)
        ·
          refine ⟨40086815228942408332326305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26724543485961605554884203 40086815228942408332326305)
          ·
            refine ⟨30065111421706806249244729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40086815228942408332326305 30065111421706806249244729)
            ·
              refine ⟨22548833566280104686933547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30065111421706806249244729 22548833566280104686933547)
              ·
                refine ⟨33823250349420157030400321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22548833566280104686933547 33823250349420157030400321)
                ·
                  refine ⟨25367437762065117772800241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33823250349420157030400321 25367437762065117772800241)
                  ·
                    refine ⟨19025578321548838329600181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25367437762065117772800241 19025578321548838329600181)
                    ·
                      refine ⟨1783647967645203593400017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19025578321548838329600181 1783647967645203593400017)
                      ·
                        rfl

theorem cell23_3473642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_3473642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473642 prefixEnd_3473642 := by exact prefixLift 3473642
  have htrace : WordTrace (prefixWord ++ tailWord_3473642) baseStart_3473642 baseEnd_3473642 := by
    simpa [prefixWord, tailWord_3473642, baseEnd_3473642] using wordTrace_append hprefix tailTrace_3473642
  have hstable : (prefixWord ++ tailWord_3473642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473642).length < 2 ^ (prefixWord ++ tailWord_3473642).sum := by decide
  have hdescent : baseEnd_3473642 < baseStart_3473642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473706 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3473706 : Nat := 118140960795 + 3473706 * 2 ^ 59
def prefixEnd_3473706 : Nat := 4983230072969 + 3 ^ 40 * 3473706 * 2
def baseEnd_3473706 : Nat := 1783680830407091342999723

theorem tailTrace_3473706 : CollatzResearch.WordTrace tailWord_3473706 prefixEnd_3473706 1783680830407091342999723 := by
  unfold tailWord_3473706
  simp only [CollatzResearch.WordTrace]
  refine ⟨31674116588340974649482243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84464310902242599065285981 31674116588340974649482243)
  ·
    refine ⟨47511174882511461974223365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31674116588340974649482243 47511174882511461974223365)
    ·
      refine ⟨8908345290470899120166881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47511174882511461974223365 8908345290470899120166881)
      ·
        refine ⟨6681258967853174340125161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8908345290470899120166881 6681258967853174340125161)
        ·
          refine ⟨5010944225889880755093871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6681258967853174340125161 5010944225889880755093871)
          ·
            refine ⟨7516416338834821132640807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5010944225889880755093871 7516416338834821132640807)
            ·
              refine ⟨11274624508252231698961211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7516416338834821132640807 11274624508252231698961211)
              ·
                refine ⟨16911936762378347548441817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11274624508252231698961211 16911936762378347548441817)
                ·
                  refine ⟨12683952571783760661331363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16911936762378347548441817 12683952571783760661331363)
                  ·
                    refine ⟨19025928857675640991997045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12683952571783760661331363 19025928857675640991997045)
                    ·
                      refine ⟨1783680830407091342999723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19025928857675640991997045 1783680830407091342999723)
                      ·
                        rfl

theorem cell23_3473706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3473706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473706 prefixEnd_3473706 := by exact prefixLift 3473706
  have htrace : WordTrace (prefixWord ++ tailWord_3473706) baseStart_3473706 baseEnd_3473706 := by
    simpa [prefixWord, tailWord_3473706, baseEnd_3473706] using wordTrace_append hprefix tailTrace_3473706
  have hstable : (prefixWord ++ tailWord_3473706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473706).length < 2 ^ (prefixWord ++ tailWord_3473706).sum := by decide
  have hdescent : baseEnd_3473706 < baseStart_3473706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473726 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_3473726 : Nat := 118140960795 + 3473726 * 2 ^ 59
def prefixEnd_3473726 : Nat := 4983230072969 + 3 ^ 40 * 3473726 * 2
def baseEnd_3473726 : Nat := 198187900002242362749959

theorem tailTrace_3473726 : CollatzResearch.WordTrace tailWord_3473726 prefixEnd_3473726 198187900002242362749959 := by
  unfold tailWord_3473726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15837149476661430251707129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84464797208860961342438021 15837149476661430251707129)
  ·
    refine ⟨11877862107496072688780347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15837149476661430251707129 11877862107496072688780347)
    ·
      refine ⟨17816793161244109033170521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11877862107496072688780347 17816793161244109033170521)
      ·
        refine ⟨13362594870933081774877891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17816793161244109033170521 13362594870933081774877891)
        ·
          refine ⟨20043892306399622662316837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13362594870933081774877891 20043892306399622662316837)
          ·
            refine ⟨3758229807449929249184407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20043892306399622662316837 3758229807449929249184407)
            ·
              refine ⟨5637344711174893873776611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758229807449929249184407 5637344711174893873776611)
              ·
                refine ⟨8456017066762340810664917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637344711174893873776611 8456017066762340810664917)
                ·
                  refine ⟨198187900002242362749959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8456017066762340810664917 198187900002242362749959)
                  ·
                    rfl

theorem cell23_3473726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_3473726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473726 prefixEnd_3473726 := by exact prefixLift 3473726
  have htrace : WordTrace (prefixWord ++ tailWord_3473726) baseStart_3473726 baseEnd_3473726 := by
    simpa [prefixWord, tailWord_3473726, baseEnd_3473726] using wordTrace_append hprefix tailTrace_3473726
  have hstable : (prefixWord ++ tailWord_3473726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473726).length < 2 ^ (prefixWord ++ tailWord_3473726).sum := by decide
  have hdescent : baseEnd_3473726 < baseStart_3473726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473759 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_3473759 : Nat := 118140960795 + 3473759 * 2 ^ 59
def prefixEnd_3473759 : Nat := 4983230072969 + 3 ^ 40 * 3473759 * 2
def baseEnd_3473759 : Nat := 1783708044881779635636979

theorem tailTrace_3473759 : CollatzResearch.WordTrace tailWord_3473759 prefixEnd_3473759 1783708044881779635636979 := by
  unfold tailWord_3473759
  simp only [CollatzResearch.WordTrace]
  refine ⟨126698399422171888649608331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84465599614781259099738887 126698399422171888649608331)
  ·
    refine ⟨190047599133257832974412497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126698399422171888649608331 190047599133257832974412497)
    ·
      refine ⟨142535699349943374730809373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190047599133257832974412497 142535699349943374730809373)
      ·
        refine ⟨53450887256228765524053515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142535699349943374730809373 53450887256228765524053515)
        ·
          refine ⟨80176330884343148286080273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53450887256228765524053515 80176330884343148286080273)
          ·
            refine ⟨60132248163257361214560205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80176330884343148286080273 60132248163257361214560205)
            ·
              refine ⟨22549593061221510455460077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60132248163257361214560205 22549593061221510455460077)
              ·
                refine ⟨8456097397958066420797529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22549593061221510455460077 8456097397958066420797529)
                ·
                  refine ⟨6342073048468549815598147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456097397958066420797529 6342073048468549815598147)
                  ·
                    refine ⟨9513109572702824723397221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6342073048468549815598147 9513109572702824723397221)
                    ·
                      refine ⟨1783708044881779635636979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9513109572702824723397221 1783708044881779635636979)
                      ·
                        rfl

theorem cell23_3473759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_3473759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473759 prefixEnd_3473759 := by exact prefixLift 3473759
  have htrace : WordTrace (prefixWord ++ tailWord_3473759) baseStart_3473759 baseEnd_3473759 := by
    simpa [prefixWord, tailWord_3473759, baseEnd_3473759] using wordTrace_append hprefix tailTrace_3473759
  have hstable : (prefixWord ++ tailWord_3473759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473759).length < 2 ^ (prefixWord ++ tailWord_3473759).sum := by decide
  have hdescent : baseEnd_3473759 < baseStart_3473759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473793 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_3473793 : Nat := 118140960795 + 3473793 * 2 ^ 59
def prefixEnd_3473793 : Nat := 4983230072969 + 3 ^ 40 * 3473793 * 2
def baseEnd_3473793 : Nat := 1783725503224032502611823

theorem tailTrace_3473793 : CollatzResearch.WordTrace tailWord_3473793 prefixEnd_3473793 1783725503224032502611823 := by
  unfold tailWord_3473793
  simp only [CollatzResearch.WordTrace]
  refine ⟨126699639504048712456346033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84466426336032474970897355 126699639504048712456346033)
  ·
    refine ⟨95024729628036534342259525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126699639504048712456346033 95024729628036534342259525)
    ·
      refine ⟨17817136805256850189173661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95024729628036534342259525 17817136805256850189173661)
      ·
        refine ⟨6681426301971318820940123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17817136805256850189173661 6681426301971318820940123)
        ·
          refine ⟨10022139452956978231410185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681426301971318820940123 10022139452956978231410185)
          ·
            refine ⟨7516604589717733673557639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10022139452956978231410185 7516604589717733673557639)
            ·
              refine ⟨11274906884576600510336459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7516604589717733673557639 11274906884576600510336459)
              ·
                refine ⟨16912360326864900765504689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11274906884576600510336459 16912360326864900765504689)
                ·
                  refine ⟨12684270245148675574128517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16912360326864900765504689 12684270245148675574128517)
                  ·
                    refine ⟨2378300670965376670149097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12684270245148675574128517 2378300670965376670149097)
                    ·
                      refine ⟨1783725503224032502611823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378300670965376670149097 1783725503224032502611823)
                      ·
                        rfl

theorem cell23_3473793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_3473793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473793 prefixEnd_3473793 := by exact prefixLift 3473793
  have htrace : WordTrace (prefixWord ++ tailWord_3473793) baseStart_3473793 baseEnd_3473793 := by
    simpa [prefixWord, tailWord_3473793, baseEnd_3473793] using wordTrace_append hprefix tailTrace_3473793
  have hstable : (prefixWord ++ tailWord_3473793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473793).length < 2 ^ (prefixWord ++ tailWord_3473793).sum := by decide
  have hdescent : baseEnd_3473793 < baseStart_3473793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473799 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 6]
def baseStart_3473799 : Nat := 118140960795 + 3473799 * 2 ^ 59
def prefixEnd_3473799 : Nat := 4983230072969 + 3 ^ 40 * 3473799 * 2
def baseEnd_3473799 : Nat := 198192064900884386570755

theorem tailTrace_3473799 : CollatzResearch.WordTrace tailWord_3473799 prefixEnd_3473799 198192064900884386570755 := by
  unfold tailWord_3473799
  simp only [CollatzResearch.WordTrace]
  refine ⟨126699858342026975481064451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84466572228017983654042967 126699858342026975481064451)
  ·
    refine ⟨190049787513040463221596677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126699858342026975481064451 190049787513040463221596677)
    ·
      refine ⟨35634335158695086854049377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190049787513040463221596677 35634335158695086854049377)
      ·
        refine ⟨26725751369021315140537033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35634335158695086854049377 26725751369021315140537033)
        ·
          refine ⟨20044313526765986355402775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26725751369021315140537033 20044313526765986355402775)
          ·
            refine ⟨30066470290148979533104163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20044313526765986355402775 30066470290148979533104163)
            ·
              refine ⟨45099705435223469299656245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30066470290148979533104163 45099705435223469299656245)
              ·
                refine ⟨4228097384552200246842773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45099705435223469299656245 4228097384552200246842773)
                ·
                  refine ⟨198192064900884386570755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4228097384552200246842773 198192064900884386570755)
                  ·
                    rfl

theorem cell23_3473799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 6].length) (baseStart_3473799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473799 prefixEnd_3473799 := by exact prefixLift 3473799
  have htrace : WordTrace (prefixWord ++ tailWord_3473799) baseStart_3473799 baseEnd_3473799 := by
    simpa [prefixWord, tailWord_3473799, baseEnd_3473799] using wordTrace_append hprefix tailTrace_3473799
  have hstable : (prefixWord ++ tailWord_3473799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473799).length < 2 ^ (prefixWord ++ tailWord_3473799).sum := by decide
  have hdescent : baseEnd_3473799 < baseStart_3473799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473836 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 4, 3, 2]
def baseStart_3473836 : Nat := 118140960795 + 3473836 * 2 ^ 59
def prefixEnd_3473836 : Nat := 4983230072969 + 3 ^ 40 * 3473836 * 2
def baseEnd_3473836 : Nat := 1783747582892175834374125

theorem tailTrace_3473836 : CollatzResearch.WordTrace tailWord_3473836 prefixEnd_3473836 1783747582892175834374125 := by
  unfold tailWord_3473836
  simp only [CollatzResearch.WordTrace]
  refine ⟨63350603921446465400080681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84467471895261953866774241 63350603921446465400080681)
  ·
    refine ⟨47512952941084849050060511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63350603921446465400080681 47512952941084849050060511)
    ·
      refine ⟨71269429411627273575090767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47512952941084849050060511 71269429411627273575090767)
      ·
        refine ⟨106904144117440910362636151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71269429411627273575090767 106904144117440910362636151)
        ·
          refine ⟨160356216176161365543954227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106904144117440910362636151 160356216176161365543954227)
          ·
            refine ⟨240534324264242048315931341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160356216176161365543954227 240534324264242048315931341)
            ·
              refine ⟨90200371599090768118474253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240534324264242048315931341 90200371599090768118474253)
              ·
                refine ⟨33825139349659038044427845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90200371599090768118474253 33825139349659038044427845)
                ·
                  refine ⟨6342213628061069633330221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33825139349659038044427845 6342213628061069633330221)
                  ·
                    refine ⟨2378330110522901112498833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6342213628061069633330221 2378330110522901112498833)
                    ·
                      refine ⟨1783747582892175834374125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378330110522901112498833 1783747582892175834374125)
                      ·
                        rfl

theorem cell23_3473836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_3473836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473836 prefixEnd_3473836 := by exact prefixLift 3473836
  have htrace : WordTrace (prefixWord ++ tailWord_3473836) baseStart_3473836 baseEnd_3473836 := by
    simpa [prefixWord, tailWord_3473836, baseEnd_3473836] using wordTrace_append hprefix tailTrace_3473836
  have hstable : (prefixWord ++ tailWord_3473836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473836).length < 2 ^ (prefixWord ++ tailWord_3473836).sum := by decide
  have hdescent : baseEnd_3473836 < baseStart_3473836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473866 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_3473866 : Nat := 118140960795 + 3473866 * 2 ^ 59
def prefixEnd_3473866 : Nat := 4983230072969 + 3 ^ 40 * 3473866 * 2
def baseEnd_3473866 : Nat := 1783762987311810716998987

theorem tailTrace_3473866 : CollatzResearch.WordTrace tailWord_3473866 prefixEnd_3473866 1783762987311810716998987 := by
  unfold tailWord_3473866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31675575508196061480938363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84468201355189497282502301 31675575508196061480938363)
  ·
    refine ⟨47513363262294092221407545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31675575508196061480938363 47513363262294092221407545)
    ·
      refine ⟨35635022446720569166055659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47513363262294092221407545 35635022446720569166055659)
      ·
        refine ⟨53452533670080853749083489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35635022446720569166055659 53452533670080853749083489)
        ·
          refine ⟨40089400252560640311812617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53452533670080853749083489 40089400252560640311812617)
          ·
            refine ⟨30067050189420480233859463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40089400252560640311812617 30067050189420480233859463)
            ·
              refine ⟨45100575284130720350789195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30067050189420480233859463 45100575284130720350789195)
              ·
                refine ⟨67650862926196080526183793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45100575284130720350789195 67650862926196080526183793)
                ·
                  refine ⟨50738147194647060394637845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67650862926196080526183793 50738147194647060394637845)
                  ·
                    refine ⟨2378350649749080955998649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50738147194647060394637845 2378350649749080955998649)
                    ·
                      refine ⟨1783762987311810716998987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378350649749080955998649 1783762987311810716998987)
                      ·
                        rfl

theorem cell23_3473866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_3473866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473866 prefixEnd_3473866 := by exact prefixLift 3473866
  have htrace : WordTrace (prefixWord ++ tailWord_3473866) baseStart_3473866 baseEnd_3473866 := by
    simpa [prefixWord, tailWord_3473866, baseEnd_3473866] using wordTrace_append hprefix tailTrace_3473866
  have hstable : (prefixWord ++ tailWord_3473866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473866).length < 2 ^ (prefixWord ++ tailWord_3473866).sum := by decide
  have hdescent : baseEnd_3473866 < baseStart_3473866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473877 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_3473877 : Nat := 118140960795 + 3473877 * 2 ^ 59
def prefixEnd_3473877 : Nat := 4983230072969 + 3 ^ 40 * 3473877 * 2
def baseEnd_3473877 : Nat := 1783768635599010173961437

theorem tailTrace_3473877 : CollatzResearch.WordTrace tailWord_3473877 prefixEnd_3473877 1783768635599010173961437 := by
  unfold tailWord_3473877
  simp only [CollatzResearch.WordTrace]
  refine ⟨126702703235744394802403885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84468468823829596534935923 126702703235744394802403885)
  ·
    refine ⟨47513513713404148050901457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126702703235744394802403885 47513513713404148050901457)
    ·
      refine ⟨35635135285053111038176093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47513513713404148050901457 35635135285053111038176093)
      ·
        refine ⟨13363175731894916639316035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35635135285053111038176093 13363175731894916639316035)
        ·
          refine ⟨20044763597842374958974053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13363175731894916639316035 20044763597842374958974053)
          ·
            refine ⟨3758393174595445304807635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20044763597842374958974053 3758393174595445304807635)
            ·
              refine ⟨5637589761893167957211453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758393174595445304807635 5637589761893167957211453)
              ·
                refine ⟨2114096160709937983954295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5637589761893167957211453 2114096160709937983954295)
                ·
                  refine ⟨3171144241064906975931443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114096160709937983954295 3171144241064906975931443)
                  ·
                    refine ⟨4756716361597360463897165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3171144241064906975931443 4756716361597360463897165)
                    ·
                      refine ⟨1783768635599010173961437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4756716361597360463897165 1783768635599010173961437)
                      ·
                        rfl

theorem cell23_3473877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_3473877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473877 prefixEnd_3473877 := by exact prefixLift 3473877
  have htrace : WordTrace (prefixWord ++ tailWord_3473877) baseStart_3473877 baseEnd_3473877 := by
    simpa [prefixWord, tailWord_3473877, baseEnd_3473877] using wordTrace_append hprefix tailTrace_3473877
  have hstable : (prefixWord ++ tailWord_3473877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473877).length < 2 ^ (prefixWord ++ tailWord_3473877).sum := by decide
  have hdescent : baseEnd_3473877 < baseStart_3473877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473916 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_3473916 : Nat := 118140960795 + 3473916 * 2 ^ 59
def prefixEnd_3473916 : Nat := 4983230072969 + 3 ^ 40 * 3473916 * 2
def baseEnd_3473916 : Nat := 1783788661344535521373757

theorem tailTrace_3473916 : CollatzResearch.WordTrace tailWord_3473916 prefixEnd_3473916 1783788661344535521373757 := by
  unfold tailWord_3473916
  simp only [CollatzResearch.WordTrace]
  refine ⟨63352062841301552231536801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84469417121735402975382401 63352062841301552231536801)
  ·
    refine ⟨47514047130976164173652601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63352062841301552231536801 47514047130976164173652601)
    ·
      refine ⟨35635535348232123130239451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47514047130976164173652601 35635535348232123130239451)
      ·
        refine ⟨53453303022348184695359177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35635535348232123130239451 53453303022348184695359177)
        ·
          refine ⟨40089977266761138521519383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53453303022348184695359177 40089977266761138521519383)
          ·
            refine ⟨60134965900141707782279075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40089977266761138521519383 60134965900141707782279075)
            ·
              refine ⟨90202448850212561673418613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60134965900141707782279075 90202448850212561673418613)
              ·
                refine ⟨8456479579707427656882995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90202448850212561673418613 8456479579707427656882995)
                ·
                  refine ⟨12684719369561141485324493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456479579707427656882995 12684719369561141485324493)
                  ·
                    refine ⟨4756769763585428056996685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12684719369561141485324493 4756769763585428056996685)
                    ·
                      refine ⟨1783788661344535521373757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4756769763585428056996685 1783788661344535521373757)
                      ·
                        rfl

theorem cell23_3473916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_3473916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473916 prefixEnd_3473916 := by exact prefixLift 3473916
  have htrace : WordTrace (prefixWord ++ tailWord_3473916) baseStart_3473916 baseEnd_3473916 := by
    simpa [prefixWord, tailWord_3473916, baseEnd_3473916] using wordTrace_append hprefix tailTrace_3473916
  have hstable : (prefixWord ++ tailWord_3473916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473916).length < 2 ^ (prefixWord ++ tailWord_3473916).sum := by decide
  have hdescent : baseEnd_3473916 < baseStart_3473916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473929 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_3473929 : Nat := 118140960795 + 3473929 * 2 ^ 59
def prefixEnd_3473929 : Nat := 4983230072969 + 3 ^ 40 * 3473929 * 2
def baseEnd_3473929 : Nat := 1783795336593043970511197

theorem tailTrace_3473929 : CollatzResearch.WordTrace tailWord_3473929 prefixEnd_3473929 1783795336593043970511197 := by
  unfold tailWord_3473929
  simp only [CollatzResearch.WordTrace]
  refine ⟨126704599831556007683296841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84469733221037338455531227 126704599831556007683296841)
  ·
    refine ⟨95028449873667005762472631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126704599831556007683296841 95028449873667005762472631)
    ·
      refine ⟨142542674810500508643708947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95028449873667005762472631 142542674810500508643708947)
      ·
        refine ⟨213814012215750762965563421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142542674810500508643708947 213814012215750762965563421)
        ·
          refine ⟨80180254580906536112086283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213814012215750762965563421 80180254580906536112086283)
          ·
            refine ⟨120270381871359804168129425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80180254580906536112086283 120270381871359804168129425)
            ·
              refine ⟨90202786403519853126097069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120270381871359804168129425 90202786403519853126097069)
              ·
                refine ⟨33826044901319944922286401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90202786403519853126097069 33826044901319944922286401)
                ·
                  refine ⟨25369533675989958691714801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33826044901319944922286401 25369533675989958691714801)
                  ·
                    refine ⟨19027150256992469018786101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25369533675989958691714801 19027150256992469018786101)
                    ·
                      refine ⟨1783795336593043970511197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19027150256992469018786101 1783795336593043970511197)
                      ·
                        rfl

theorem cell23_3473929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_3473929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473929 prefixEnd_3473929 := by exact prefixLift 3473929
  have htrace : WordTrace (prefixWord ++ tailWord_3473929) baseStart_3473929 baseEnd_3473929 := by
    simpa [prefixWord, tailWord_3473929, baseEnd_3473929] using wordTrace_append hprefix tailTrace_3473929
  have hstable : (prefixWord ++ tailWord_3473929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473929).length < 2 ^ (prefixWord ++ tailWord_3473929).sum := by decide
  have hdescent : baseEnd_3473929 < baseStart_3473929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473960 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3473960 : Nat := 118140960795 + 3473960 * 2 ^ 59
def prefixEnd_3473960 : Nat := 4983230072969 + 3 ^ 40 * 3473960 * 2
def baseEnd_3473960 : Nat := 1783811254493333349223555

theorem tailTrace_3473960 : CollatzResearch.WordTrace tailWord_3473960 prefixEnd_3473960 1783811254493333349223555 := by
  unfold tailWord_3473960
  simp only [CollatzResearch.WordTrace]
  refine ⟨63352865247221849988837667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84470486996295799985116889 63352865247221849988837667)
  ·
    refine ⟨95029297870832774983256501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63352865247221849988837667 95029297870832774983256501)
    ·
      refine ⟨8908996675390572654680297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95029297870832774983256501 8908996675390572654680297)
      ·
        refine ⟨6681747506542929491010223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8908996675390572654680297 6681747506542929491010223)
        ·
          refine ⟨10022621259814394236515335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681747506542929491010223 10022621259814394236515335)
          ·
            refine ⟨15033931889721591354773003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10022621259814394236515335 15033931889721591354773003)
            ·
              refine ⟨22550897834582387032159505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15033931889721591354773003 22550897834582387032159505)
              ·
                refine ⟨16913173375936790274119629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22550897834582387032159505 16913173375936790274119629)
                ·
                  refine ⟨6342440015976296352794861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16913173375936790274119629 6342440015976296352794861)
                  ·
                    refine ⟨2378415005991111132298073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6342440015976296352794861 2378415005991111132298073)
                    ·
                      refine ⟨1783811254493333349223555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378415005991111132298073 1783811254493333349223555)
                      ·
                        rfl

theorem cell23_3473960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3473960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473960 prefixEnd_3473960 := by exact prefixLift 3473960
  have htrace : WordTrace (prefixWord ++ tailWord_3473960) baseStart_3473960 baseEnd_3473960 := by
    simpa [prefixWord, tailWord_3473960, baseEnd_3473960] using wordTrace_append hprefix tailTrace_3473960
  have hstable : (prefixWord ++ tailWord_3473960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473960).length < 2 ^ (prefixWord ++ tailWord_3473960).sum := by decide
  have hdescent : baseEnd_3473960 < baseStart_3473960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473976 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_3473976 : Nat := 118140960795 + 3473976 * 2 ^ 59
def prefixEnd_3473976 : Nat := 4983230072969 + 3 ^ 40 * 3473976 * 2
def baseEnd_3473976 : Nat := 1783819470183805286623481

theorem tailTrace_3473976 : CollatzResearch.WordTrace tailWord_3473976 prefixEnd_3473976 1783819470183805286623481 := by
  unfold tailWord_3473976
  simp only [CollatzResearch.WordTrace]
  refine ⟨63353157031192867355128891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84470876041590489806838521 63353157031192867355128891)
  ·
    refine ⟨95029735546789301032693337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63353157031192867355128891 95029735546789301032693337)
    ·
      refine ⟨71272301660091975774520003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95029735546789301032693337 71272301660091975774520003)
      ·
        refine ⟨106908452490137963661780005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71272301660091975774520003 106908452490137963661780005)
        ·
          refine ⟨20045334841900868186583751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106908452490137963661780005 20045334841900868186583751)
          ·
            refine ⟨30068002262851302279875627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20045334841900868186583751 30068002262851302279875627)
            ·
              refine ⟨45102003394276953419813441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30068002262851302279875627 45102003394276953419813441)
              ·
                refine ⟨33826502545707715064860081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45102003394276953419813441 33826502545707715064860081)
                ·
                  refine ⟨25369876909280786298645061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33826502545707715064860081 25369876909280786298645061)
                  ·
                    refine ⟨4756851920490147430995949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25369876909280786298645061 4756851920490147430995949)
                    ·
                      refine ⟨1783819470183805286623481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4756851920490147430995949 1783819470183805286623481)
                      ·
                        rfl

theorem cell23_3473976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_3473976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473976 prefixEnd_3473976 := by exact prefixLift 3473976
  have htrace : WordTrace (prefixWord ++ tailWord_3473976) baseStart_3473976 baseEnd_3473976 := by
    simpa [prefixWord, tailWord_3473976, baseEnd_3473976] using wordTrace_append hprefix tailTrace_3473976
  have hstable : (prefixWord ++ tailWord_3473976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473976).length < 2 ^ (prefixWord ++ tailWord_3473976).sum := by decide
  have hdescent : baseEnd_3473976 < baseStart_3473976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473988 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3473988 : Nat := 118140960795 + 3473988 * 2 ^ 59
def prefixEnd_3473988 : Nat := 4983230072969 + 3 ^ 40 * 3473988 * 2
def baseEnd_3473988 : Nat := 1783825631951659239673427

theorem tailTrace_3473988 : CollatzResearch.WordTrace tailWord_3473988 prefixEnd_3473988 1783825631951659239673427 := by
  unfold tailWord_3473988
  simp only [CollatzResearch.WordTrace]
  refine ⟨63353375869171130379847309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84471167825561507173129745 63353375869171130379847309)
  ·
    refine ⟨23757515950939173892442741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63353375869171130379847309 23757515950939173892442741)
    ·
      refine ⟨2227267120400547552416507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23757515950939173892442741 2227267120400547552416507)
      ·
        refine ⟨3340900680600821328624761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227267120400547552416507 3340900680600821328624761)
        ·
          refine ⟨2505675510450615996468571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340900680600821328624761 2505675510450615996468571)
          ·
            refine ⟨3758513265675923994702857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505675510450615996468571 3758513265675923994702857)
            ·
              refine ⟨2818884949256942996027143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3758513265675923994702857 2818884949256942996027143)
              ·
                refine ⟨4228327423885414494040715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818884949256942996027143 4228327423885414494040715)
                ·
                  refine ⟨6342491135828121741061073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228327423885414494040715 6342491135828121741061073)
                  ·
                    refine ⟨4756868351871091305795805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6342491135828121741061073 4756868351871091305795805)
                    ·
                      refine ⟨1783825631951659239673427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4756868351871091305795805 1783825631951659239673427)
                      ·
                        rfl

theorem cell23_3473988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3473988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3473988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3473988 prefixEnd_3473988 := by exact prefixLift 3473988
  have htrace : WordTrace (prefixWord ++ tailWord_3473988) baseStart_3473988 baseEnd_3473988 := by
    simpa [prefixWord, tailWord_3473988, baseEnd_3473988] using wordTrace_append hprefix tailTrace_3473988
  have hstable : (prefixWord ++ tailWord_3473988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473988).length < 2 ^ (prefixWord ++ tailWord_3473988).sum := by decide
  have hdescent : baseEnd_3473988 < baseStart_3473988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474024 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3474024 : Nat := 118140960795 + 3474024 * 2 ^ 59
def prefixEnd_3474024 : Nat := 4983230072969 + 3 ^ 40 * 3474024 * 2
def baseEnd_3474024 : Nat := 1783844117255221098823261

theorem tailTrace_3474024 : CollatzResearch.WordTrace tailWord_3474024 prefixEnd_3474024 1783844117255221098823261 := by
  unfold tailWord_3474024
  simp only [CollatzResearch.WordTrace]
  refine ⟨63354032383105919454002563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84472043177474559272003417 63354032383105919454002563)
  ·
    refine ⟨95031048574658879181003845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63354032383105919454002563 95031048574658879181003845)
    ·
      refine ⟨17818321607748539846438221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95031048574658879181003845 17818321607748539846438221)
      ·
        refine ⟨6681870602905702442414333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17818321607748539846438221 6681870602905702442414333)
        ·
          refine ⟨2505701476089638415905375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6681870602905702442414333 2505701476089638415905375)
          ·
            refine ⟨3758552214134457623858063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505701476089638415905375 3758552214134457623858063)
            ·
              refine ⟨5637828321201686435787095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758552214134457623858063 5637828321201686435787095)
              ·
                refine ⟨8456742481802529653680643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637828321201686435787095 8456742481802529653680643)
                ·
                  refine ⟨12685113722703794480520965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456742481802529653680643 12685113722703794480520965)
                  ·
                    refine ⟨2378458823006961465097681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12685113722703794480520965 2378458823006961465097681)
                    ·
                      refine ⟨1783844117255221098823261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378458823006961465097681 1783844117255221098823261)
                      ·
                        rfl

theorem cell23_3474024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3474024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474024 prefixEnd_3474024 := by exact prefixLift 3474024
  have htrace : WordTrace (prefixWord ++ tailWord_3474024) baseStart_3474024 baseEnd_3474024 := by
    simpa [prefixWord, tailWord_3474024, baseEnd_3474024] using wordTrace_append hprefix tailTrace_3474024
  have hstable : (prefixWord ++ tailWord_3474024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474024).length < 2 ^ (prefixWord ++ tailWord_3474024).sum := by decide
  have hdescent : baseEnd_3474024 < baseStart_3474024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474026 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3474026 : Nat := 118140960795 + 3474026 * 2 ^ 59
def prefixEnd_3474026 : Nat := 4983230072969 + 3 ^ 40 * 3474026 * 2
def baseEnd_3474026 : Nat := 594615048072176696999417

theorem tailTrace_3474026 : CollatzResearch.WordTrace tailWord_3474026 prefixEnd_3474026 594615048072176696999417 := by
  unfold tailWord_3474026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31677034428051148312394483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84472091808136395499718621 31677034428051148312394483)
  ·
    refine ⟨47515551642076722468591725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31677034428051148312394483 47515551642076722468591725)
    ·
      refine ⟨17818331865778770925721897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47515551642076722468591725 17818331865778770925721897)
      ·
        refine ⟨13363748899334078194291423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17818331865778770925721897 13363748899334078194291423)
        ·
          refine ⟨20045623349001117291437135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13363748899334078194291423 20045623349001117291437135)
          ·
            refine ⟨30068435023501675937155703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20045623349001117291437135 30068435023501675937155703)
            ·
              refine ⟨45102652535252513905733555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30068435023501675937155703 45102652535252513905733555)
              ·
                refine ⟨67653978802878770858600333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45102652535252513905733555 67653978802878770858600333)
                ·
                  refine ⟨25370242051079539071975125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67653978802878770858600333 25370242051079539071975125)
                  ·
                    refine ⟨594615048072176696999417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25370242051079539071975125 594615048072176696999417)
                    ·
                      rfl

theorem cell23_3474026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3474026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474026 prefixEnd_3474026 := by exact prefixLift 3474026
  have htrace : WordTrace (prefixWord ++ tailWord_3474026) baseStart_3474026 baseEnd_3474026 := by
    simpa [prefixWord, tailWord_3474026, baseEnd_3474026] using wordTrace_append hprefix tailTrace_3474026
  have hstable : (prefixWord ++ tailWord_3474026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474026).length < 2 ^ (prefixWord ++ tailWord_3474026).sum := by decide
  have hdescent : baseEnd_3474026 < baseStart_3474026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474097 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3474097 : Nat := 118140960795 + 3474097 * 2 ^ 59
def prefixEnd_3474097 : Nat := 4983230072969 + 3 ^ 40 * 3474097 * 2
def baseEnd_3474097 : Nat := 1783881601342999313210425

theorem tailTrace_3474097 : CollatzResearch.WordTrace tailWord_3474097 prefixEnd_3474097 1783881601342999313210425 := by
  unfold tailWord_3474097
  simp only [CollatzResearch.WordTrace]
  refine ⟨126710727294947372375412545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84473818196631581583608363 126710727294947372375412545)
  ·
    refine ⟨95033045471210529281559409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126710727294947372375412545 95033045471210529281559409)
    ·
      refine ⟨71274784103407896961169557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95033045471210529281559409 71274784103407896961169557)
      ·
        refine ⟨3341005504847245170054823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71274784103407896961169557 3341005504847245170054823)
        ·
          refine ⟨5011508257270867755082235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341005504847245170054823 5011508257270867755082235)
          ·
            refine ⟨7517262385906301632623353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011508257270867755082235 7517262385906301632623353)
            ·
              refine ⟨5637946789429726224467515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7517262385906301632623353 5637946789429726224467515)
              ·
                refine ⟨8456920184144589336701273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637946789429726224467515 8456920184144589336701273)
                ·
                  refine ⟨6342690138108442002525955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456920184144589336701273 6342690138108442002525955)
                  ·
                    refine ⟨9514035207162663003788933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6342690138108442002525955 9514035207162663003788933)
                    ·
                      refine ⟨1783881601342999313210425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9514035207162663003788933 1783881601342999313210425)
                      ·
                        rfl

theorem cell23_3474097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3474097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474097 prefixEnd_3474097 := by exact prefixLift 3474097
  have htrace : WordTrace (prefixWord ++ tailWord_3474097) baseStart_3474097 baseEnd_3474097 := by
    simpa [prefixWord, tailWord_3474097, baseEnd_3474097] using wordTrace_append hprefix tailTrace_3474097
  have hstable : (prefixWord ++ tailWord_3474097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474097).length < 2 ^ (prefixWord ++ tailWord_3474097).sum := by decide
  have hdescent : baseEnd_3474097 < baseStart_3474097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474123 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 5, 5, 2]
def baseStart_3474123 : Nat := 118140960795 + 3474123 * 2 ^ 59
def prefixEnd_3474123 : Nat := 4983230072969 + 3 ^ 40 * 3474123 * 2
def baseEnd_3474123 : Nat := 1783894951840016211485305

theorem tailTrace_3474123 : CollatzResearch.WordTrace tailWord_3474123 prefixEnd_3474123 1783894951840016211485305 := by
  unfold tailWord_3474123
  simp only [CollatzResearch.WordTrace]
  refine ⟨126711675592853178815859023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84474450395235452543906015 126711675592853178815859023)
  ·
    refine ⟨190067513389279768223788535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126711675592853178815859023 190067513389279768223788535)
    ·
      refine ⟨285101270083919652335682803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190067513389279768223788535 285101270083919652335682803)
      ·
        refine ⟨427651905125879478503524205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285101270083919652335682803 427651905125879478503524205)
        ·
          refine ⟨160369464422204804438821577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427651905125879478503524205 160369464422204804438821577)
          ·
            refine ⟨120277098316653603329116183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160369464422204804438821577 120277098316653603329116183)
            ·
              refine ⟨180415647474980404993674275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120277098316653603329116183 180415647474980404993674275)
              ·
                refine ⟨270623471212470607490511413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180415647474980404993674275 270623471212470607490511413)
                ·
                  refine ⟨25370950426169119452235445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270623471212470607490511413 25370950426169119452235445)
                  ·
                    refine ⟨2378526602453354948647073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25370950426169119452235445 2378526602453354948647073)
                    ·
                      refine ⟨1783894951840016211485305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378526602453354948647073 1783894951840016211485305)
                      ·
                        rfl

theorem cell23_3474123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5, 2].length) (baseStart_3474123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474123 prefixEnd_3474123 := by exact prefixLift 3474123
  have htrace : WordTrace (prefixWord ++ tailWord_3474123) baseStart_3474123 baseEnd_3474123 := by
    simpa [prefixWord, tailWord_3474123, baseEnd_3474123] using wordTrace_append hprefix tailTrace_3474123
  have hstable : (prefixWord ++ tailWord_3474123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474123).length < 2 ^ (prefixWord ++ tailWord_3474123).sum := by decide
  have hdescent : baseEnd_3474123 < baseStart_3474123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474124 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_3474124 : Nat := 118140960795 + 3474124 * 2 ^ 59
def prefixEnd_3474124 : Nat := 4983230072969 + 3 ^ 40 * 3474124 * 2
def baseEnd_3474124 : Nat := 594631821773556902524267

theorem tailTrace_3474124 : CollatzResearch.WordTrace tailWord_3474124 prefixEnd_3474124 594631821773556902524267 := by
  unfold tailWord_3474124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63355856032924777993322713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84474474710566370657763617 63355856032924777993322713)
  ·
    refine ⟨47516892024693583494992035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63355856032924777993322713 47516892024693583494992035)
    ·
      refine ⟨71275338037040375242488053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47516892024693583494992035 71275338037040375242488053)
      ·
        refine ⟨6682062940972535178983255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71275338037040375242488053 6682062940972535178983255)
        ·
          refine ⟨10023094411458802768474883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682062940972535178983255 10023094411458802768474883)
          ·
            refine ⟨15034641617188204152712325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023094411458802768474883 15034641617188204152712325)
            ·
              refine ⟨2818995303222788278633561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15034641617188204152712325 2818995303222788278633561)
              ·
                refine ⟨2114246477417091208975171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818995303222788278633561 2114246477417091208975171)
                ·
                  refine ⟨3171369716125636813462757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114246477417091208975171 3171369716125636813462757)
                  ·
                    refine ⟨594631821773556902524267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171369716125636813462757 594631821773556902524267)
                    ·
                      rfl

theorem cell23_3474124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_3474124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474124 prefixEnd_3474124 := by exact prefixLift 3474124
  have htrace : WordTrace (prefixWord ++ tailWord_3474124) baseStart_3474124 baseEnd_3474124 := by
    simpa [prefixWord, tailWord_3474124, baseEnd_3474124] using wordTrace_append hprefix tailTrace_3474124
  have hstable : (prefixWord ++ tailWord_3474124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474124).length < 2 ^ (prefixWord ++ tailWord_3474124).sum := by decide
  have hdescent : baseEnd_3474124 < baseStart_3474124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474147 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3474147 : Nat := 118140960795 + 3474147 * 2 ^ 59
def prefixEnd_3474147 : Nat := 4983230072969 + 3 ^ 40 * 3474147 * 2
def baseEnd_3474147 : Nat := 1783907275375724117585195

theorem tailTrace_3474147 : CollatzResearch.WordTrace tailWord_3474147 prefixEnd_3474147 1783907275375724117585195 := by
  unfold tailWord_3474147
  simp only [CollatzResearch.WordTrace]
  refine ⟨126712550944766230914732695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84475033963177487276488463 126712550944766230914732695)
  ·
    refine ⟨190068826417149346372099043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126712550944766230914732695 190068826417149346372099043)
    ·
      refine ⟨285103239625724019558148565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190068826417149346372099043 285103239625724019558148565)
      ·
        refine ⟨6682107178727906708394107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 285103239625724019558148565 6682107178727906708394107)
        ·
          refine ⟨10023160768091860062591161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682107178727906708394107 10023160768091860062591161)
          ·
            refine ⟨7517370576068895046943371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10023160768091860062591161 7517370576068895046943371)
            ·
              refine ⟨11276055864103342570415057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7517370576068895046943371 11276055864103342570415057)
              ·
                refine ⟨8457041898077506927811293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11276055864103342570415057 8457041898077506927811293)
                ·
                  refine ⟨3171390711779065097929235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8457041898077506927811293 3171390711779065097929235)
                  ·
                    refine ⟨4757086067668597646893853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3171390711779065097929235 4757086067668597646893853)
                    ·
                      refine ⟨1783907275375724117585195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4757086067668597646893853 1783907275375724117585195)
                      ·
                        rfl

theorem cell23_3474147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3474147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474147 prefixEnd_3474147 := by exact prefixLift 3474147
  have htrace : WordTrace (prefixWord ++ tailWord_3474147) baseStart_3474147 baseEnd_3474147 := by
    simpa [prefixWord, tailWord_3474147, baseEnd_3474147] using wordTrace_append hprefix tailTrace_3474147
  have hstable : (prefixWord ++ tailWord_3474147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474147).length < 2 ^ (prefixWord ++ tailWord_3474147).sum := by decide
  have hdescent : baseEnd_3474147 < baseStart_3474147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474153 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_3474153 : Nat := 118140960795 + 3474153 * 2 ^ 59
def prefixEnd_3474153 : Nat := 4983230072969 + 3 ^ 40 * 3474153 * 2
def baseEnd_3474153 : Nat := 1783910356259651094110167

theorem tailTrace_3474153 : CollatzResearch.WordTrace tailWord_3474153 prefixEnd_3474153 1783910356259651094110167 := by
  unfold tailWord_3474153
  simp only [CollatzResearch.WordTrace]
  refine ⟨126712769782744493939451113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84475179855162995959634075 126712769782744493939451113)
  ·
    refine ⟨95034577337058370454588335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126712769782744493939451113 95034577337058370454588335)
    ·
      refine ⟨142551866005587555681882503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95034577337058370454588335 142551866005587555681882503)
      ·
        refine ⟨213827799008381333522823755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142551866005587555681882503 213827799008381333522823755)
        ·
          refine ⟨320741698512572000284235633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213827799008381333522823755 320741698512572000284235633)
          ·
            refine ⟨240556273884429000213176725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320741698512572000284235633 240556273884429000213176725)
            ·
              refine ⟨11276075338332609384992659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240556273884429000213176725 11276075338332609384992659)
              ·
                refine ⟨16914113007498914077488989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11276075338332609384992659 16914113007498914077488989)
                ·
                  refine ⟨6342792377812092779058371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16914113007498914077488989 6342792377812092779058371)
                  ·
                    refine ⟨9514188566718139168587557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6342792377812092779058371 9514188566718139168587557)
                    ·
                      refine ⟨1783910356259651094110167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9514188566718139168587557 1783910356259651094110167)
                      ·
                        rfl

theorem cell23_3474153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_3474153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474153 prefixEnd_3474153 := by exact prefixLift 3474153
  have htrace : WordTrace (prefixWord ++ tailWord_3474153) baseStart_3474153 baseEnd_3474153 := by
    simpa [prefixWord, tailWord_3474153, baseEnd_3474153] using wordTrace_append hprefix tailTrace_3474153
  have hstable : (prefixWord ++ tailWord_3474153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474153).length < 2 ^ (prefixWord ++ tailWord_3474153).sum := by decide
  have hdescent : baseEnd_3474153 < baseStart_3474153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474163 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 4, 4]
def baseStart_3474163 : Nat := 118140960795 + 3474163 * 2 ^ 59
def prefixEnd_3474163 : Nat := 4983230072969 + 3 ^ 40 * 3474163 * 2
def baseEnd_3474163 : Nat := 594638497022065351661707

theorem tailTrace_3474163 : CollatzResearch.WordTrace tailWord_3474163 prefixEnd_3474163 594638497022065351661707 := by
  unfold tailWord_3474163
  simp only [CollatzResearch.WordTrace]
  refine ⟨126713134512708265647315143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84475423008472177098210095 126713134512708265647315143)
  ·
    refine ⟨190069701769062398470972715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126713134512708265647315143 190069701769062398470972715)
    ·
      refine ⟨285104552653593597706459073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190069701769062398470972715 285104552653593597706459073)
      ·
        refine ⟨213828414490195198279844305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285104552653593597706459073 213828414490195198279844305)
        ·
          refine ⟨160371310867646398709883229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213828414490195198279844305 160371310867646398709883229)
          ·
            refine ⟨60139241575367399516206211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160371310867646398709883229 60139241575367399516206211)
            ·
              refine ⟨90208862363051099274309317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60139241575367399516206211 90208862363051099274309317)
              ·
                refine ⟨16914161693072081113932997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90208862363051099274309317 16914161693072081113932997)
                ·
                  refine ⟨3171405317451015208862437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16914161693072081113932997 3171405317451015208862437)
                  ·
                    refine ⟨594638497022065351661707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171405317451015208862437 594638497022065351661707)
                    ·
                      rfl

theorem cell23_3474163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 4].length) (baseStart_3474163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474163 prefixEnd_3474163 := by exact prefixLift 3474163
  have htrace : WordTrace (prefixWord ++ tailWord_3474163) baseStart_3474163 baseEnd_3474163 := by
    simpa [prefixWord, tailWord_3474163, baseEnd_3474163] using wordTrace_append hprefix tailTrace_3474163
  have hstable : (prefixWord ++ tailWord_3474163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474163).length < 2 ^ (prefixWord ++ tailWord_3474163).sum := by decide
  have hdescent : baseEnd_3474163 < baseStart_3474163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474173 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_3474173 : Nat := 118140960795 + 3474173 * 2 ^ 59
def prefixEnd_3474173 : Nat := 4983230072969 + 3 ^ 40 * 3474173 * 2
def baseEnd_3474173 : Nat := 1783920625872741015860075

theorem tailTrace_3474173 : CollatzResearch.WordTrace tailWord_3474173 prefixEnd_3474173 1783920625872741015860075 := by
  unfold tailWord_3474173
  simp only [CollatzResearch.WordTrace]
  refine ⟨126713499242672037355179173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84475666161781358236786115 126713499242672037355179173)
  ·
    refine ⟨23758781108001007004096095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126713499242672037355179173 23758781108001007004096095)
    ·
      refine ⟨35638171662001510506144143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23758781108001007004096095 35638171662001510506144143)
      ·
        refine ⟨53457257493002265759216215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35638171662001510506144143 53457257493002265759216215)
        ·
          refine ⟨80185886239503398638824323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53457257493002265759216215 80185886239503398638824323)
          ·
            refine ⟨120278829359255097958236485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80185886239503398638824323 120278829359255097958236485)
            ·
              refine ⟨22552280504860330867169341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120278829359255097958236485 22552280504860330867169341)
              ·
                refine ⟨8457105189322624075188503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22552280504860330867169341 8457105189322624075188503)
                ·
                  refine ⟨12685657783983936112782755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8457105189322624075188503 12685657783983936112782755)
                  ·
                    refine ⟨19028486675975904169174133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12685657783983936112782755 19028486675975904169174133)
                    ·
                      refine ⟨1783920625872741015860075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19028486675975904169174133 1783920625872741015860075)
                      ·
                        rfl

theorem cell23_3474173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_3474173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474173 prefixEnd_3474173 := by exact prefixLift 3474173
  have htrace : WordTrace (prefixWord ++ tailWord_3474173) baseStart_3474173 baseEnd_3474173 := by
    simpa [prefixWord, tailWord_3474173, baseEnd_3474173] using wordTrace_append hprefix tailTrace_3474173
  have hstable : (prefixWord ++ tailWord_3474173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474173).length < 2 ^ (prefixWord ++ tailWord_3474173).sum := by decide
  have hdescent : baseEnd_3474173 < baseStart_3474173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474180 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3474180 : Nat := 118140960795 + 3474180 * 2 ^ 59
def prefixEnd_3474180 : Nat := 4983230072969 + 3 ^ 40 * 3474180 * 2
def baseEnd_3474180 : Nat := 594641406745774162824181

theorem tailTrace_3474180 : CollatzResearch.WordTrace tailWord_3474180 prefixEnd_3474180 594641406745774162824181 := by
  unfold tailWord_3474180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63356877276823338775341997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84475836369097785033789329 63356877276823338775341997)
  ·
    refine ⟨23758828978808752040753249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63356877276823338775341997 23758828978808752040753249)
    ·
      refine ⟨17819121734106564030564937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23758828978808752040753249 17819121734106564030564937)
      ·
        refine ⟨13364341300579923022923703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17819121734106564030564937 13364341300579923022923703)
        ·
          refine ⟨20046511950869884534385555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13364341300579923022923703 20046511950869884534385555)
          ·
            refine ⟨30069767926304826801578333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20046511950869884534385555 30069767926304826801578333)
            ·
              refine ⟨11276162972364310050591875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30069767926304826801578333 11276162972364310050591875)
              ·
                refine ⟨16914244458546465075887813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11276162972364310050591875 16914244458546465075887813)
                ·
                  refine ⟨3171420835977462201728965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16914244458546465075887813 3171420835977462201728965)
                  ·
                    refine ⟨594641406745774162824181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171420835977462201728965 594641406745774162824181)
                    ·
                      rfl

theorem cell23_3474180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3474180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474180 prefixEnd_3474180 := by exact prefixLift 3474180
  have htrace : WordTrace (prefixWord ++ tailWord_3474180) baseStart_3474180 baseEnd_3474180 := by
    simpa [prefixWord, tailWord_3474180, baseEnd_3474180] using wordTrace_append hprefix tailTrace_3474180
  have hstable : (prefixWord ++ tailWord_3474180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474180).length < 2 ^ (prefixWord ++ tailWord_3474180).sum := by decide
  have hdescent : baseEnd_3474180 < baseStart_3474180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474197 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_3474197 : Nat := 118140960795 + 3474197 * 2 ^ 59
def prefixEnd_3474197 : Nat := 4983230072969 + 3 ^ 40 * 3474197 * 2
def baseEnd_3474197 : Nat := 594644316469482973986655

theorem tailTrace_3474197 : CollatzResearch.WordTrace tailWord_3474197 prefixEnd_3474197 594644316469482973986655 := by
  unfold tailWord_3474197
  simp only [CollatzResearch.WordTrace]
  refine ⟨126714374594585089454052845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84476249729723392969368563 126714374594585089454052845)
  ·
    refine ⟨47517890472969408545269817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126714374594585089454052845 47517890472969408545269817)
    ·
      refine ⟨35638417854727056408952363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47517890472969408545269817 35638417854727056408952363)
      ·
        refine ⟨53457626782090584613428545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35638417854727056408952363 53457626782090584613428545)
        ·
          refine ⟨40093220086567938460071409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53457626782090584613428545 40093220086567938460071409)
          ·
            refine ⟨30069915064925953845053557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40093220086567938460071409 30069915064925953845053557)
            ·
              refine ⟨2819054537336808172973771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30069915064925953845053557 2819054537336808172973771)
              ·
                refine ⟨4228581806005212259460657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819054537336808172973771 4228581806005212259460657)
                ·
                  refine ⟨3171436354503909194595493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4228581806005212259460657 3171436354503909194595493)
                  ·
                    refine ⟨594644316469482973986655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171436354503909194595493 594644316469482973986655)
                    ·
                      rfl

theorem cell23_3474197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_3474197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474197 prefixEnd_3474197 := by exact prefixLift 3474197
  have htrace : WordTrace (prefixWord ++ tailWord_3474197) baseStart_3474197 baseEnd_3474197 := by
    simpa [prefixWord, tailWord_3474197, baseEnd_3474197] using wordTrace_append hprefix tailTrace_3474197
  have hstable : (prefixWord ++ tailWord_3474197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474197).length < 2 ^ (prefixWord ++ tailWord_3474197).sum := by decide
  have hdescent : baseEnd_3474197 < baseStart_3474197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474207 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 3]
def baseStart_3474207 : Nat := 118140960795 + 3474207 * 2 ^ 59
def prefixEnd_3474207 : Nat := 4983230072969 + 3 ^ 40 * 3474207 * 2
def baseEnd_3474207 : Nat := 1783938084214993882834919

theorem tailTrace_3474207 : CollatzResearch.WordTrace tailWord_3474207 prefixEnd_3474207 1783938084214993882834919 := by
  unfold tailWord_3474207
  simp only [CollatzResearch.WordTrace]
  refine ⟨126714739324548861161916875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84476492883032574107944583 126714739324548861161916875)
  ·
    refine ⟨190072108986823291742875313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126714739324548861161916875 190072108986823291742875313)
    ·
      refine ⟨142554081740117468807156485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190072108986823291742875313 142554081740117468807156485)
      ·
        refine ⟨26728890326272025401341841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142554081740117468807156485 26728890326272025401341841)
        ·
          refine ⟨20046667744704019051006381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26728890326272025401341841 20046667744704019051006381)
          ·
            refine ⟨7517500404264007144127393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20046667744704019051006381 7517500404264007144127393)
            ·
              refine ⟨5638125303198005358095545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7517500404264007144127393 5638125303198005358095545)
              ·
                refine ⟨4228593977398504018571659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638125303198005358095545 4228593977398504018571659)
                ·
                  refine ⟨6342890966097756027857489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228593977398504018571659 6342890966097756027857489)
                  ·
                    refine ⟨4757168224573317020893117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6342890966097756027857489 4757168224573317020893117)
                    ·
                      refine ⟨1783938084214993882834919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4757168224573317020893117 1783938084214993882834919)
                      ·
                        rfl

theorem cell23_3474207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_3474207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474207 prefixEnd_3474207 := by exact prefixLift 3474207
  have htrace : WordTrace (prefixWord ++ tailWord_3474207) baseStart_3474207 baseEnd_3474207 := by
    simpa [prefixWord, tailWord_3474207, baseEnd_3474207] using wordTrace_append hprefix tailTrace_3474207
  have hstable : (prefixWord ++ tailWord_3474207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474207).length < 2 ^ (prefixWord ++ tailWord_3474207).sum := by decide
  have hdescent : baseEnd_3474207 < baseStart_3474207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474210 : List Nat := [3, 3, 1, 1, 2, 2, 4, 7]
def baseStart_3474210 : Nat := 118140960795 + 3474210 * 2 ^ 59
def prefixEnd_3474210 : Nat := 4983230072969 + 3 ^ 40 * 3474210 * 2
def baseEnd_3474210 : Nat := 66071837950257680411015

theorem tailTrace_3474210 : CollatzResearch.WordTrace tailWord_3474210 prefixEnd_3474210 66071837950257680411015 := by
  unfold tailWord_3474210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31678712185884498168569021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84476565829025328449517389 31678712185884498168569021)
  ·
    refine ⟨11879517069706686813213383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31678712185884498168569021 11879517069706686813213383)
    ·
      refine ⟨17819275604560030219820075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11879517069706686813213383 17819275604560030219820075)
      ·
        refine ⟨26728913406840045329730113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17819275604560030219820075 26728913406840045329730113)
        ·
          refine ⟨20046685055130033997297585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26728913406840045329730113 20046685055130033997297585)
          ·
            refine ⟨15035013791347525497973189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20046685055130033997297585 15035013791347525497973189)
            ·
              refine ⟨2819065085877661030869973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15035013791347525497973189 2819065085877661030869973)
              ·
                refine ⟨66071837950257680411015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2819065085877661030869973 66071837950257680411015)
                ·
                  rfl

theorem cell23_3474210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_3474210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474210 prefixEnd_3474210 := by exact prefixLift 3474210
  have htrace : WordTrace (prefixWord ++ tailWord_3474210) baseStart_3474210 baseEnd_3474210 := by
    simpa [prefixWord, tailWord_3474210, baseEnd_3474210] using wordTrace_append hprefix tailTrace_3474210
  have hstable : (prefixWord ++ tailWord_3474210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474210).length < 2 ^ (prefixWord ++ tailWord_3474210).sum := by decide
  have hdescent : baseEnd_3474210 < baseStart_3474210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474220 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_3474220 : Nat := 118140960795 + 3474220 * 2 ^ 59
def prefixEnd_3474220 : Nat := 4983230072969 + 3 ^ 40 * 3474220 * 2
def baseEnd_3474220 : Nat := 1783944759463502331972359

theorem tailTrace_3474220 : CollatzResearch.WordTrace tailWord_3474220 prefixEnd_3474220 1783944759463502331972359 := by
  unfold tailWord_3474220
  simp only [CollatzResearch.WordTrace]
  refine ⟨63357606736750882191070057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84476808982334509588093409 63357606736750882191070057)
  ·
    refine ⟨47518205052563161643302543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63357606736750882191070057 47518205052563161643302543)
    ·
      refine ⟨71277307578844742464953815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47518205052563161643302543 71277307578844742464953815)
      ·
        refine ⟨106915961368267113697430723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71277307578844742464953815 106915961368267113697430723)
        ·
          refine ⟨160373942052400670546146085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106915961368267113697430723 160373942052400670546146085)
          ·
            refine ⟨30070114134825125727402391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160373942052400670546146085 30070114134825125727402391)
            ·
              refine ⟨45105171202237688591103587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30070114134825125727402391 45105171202237688591103587)
              ·
                refine ⟨67657756803356532886655381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45105171202237688591103587 67657756803356532886655381)
                ·
                  refine ⟨3171457350157337479061971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67657756803356532886655381 3171457350157337479061971)
                  ·
                    refine ⟨4757186025236006218592957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3171457350157337479061971 4757186025236006218592957)
                    ·
                      refine ⟨1783944759463502331972359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4757186025236006218592957 1783944759463502331972359)
                      ·
                        rfl

theorem cell23_3474220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_3474220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474220 prefixEnd_3474220 := by exact prefixLift 3474220
  have htrace : WordTrace (prefixWord ++ tailWord_3474220) baseStart_3474220 baseEnd_3474220 := by
    simpa [prefixWord, tailWord_3474220, baseEnd_3474220] using wordTrace_append hprefix tailTrace_3474220
  have hstable : (prefixWord ++ tailWord_3474220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474220).length < 2 ^ (prefixWord ++ tailWord_3474220).sum := by decide
  have hdescent : baseEnd_3474220 < baseStart_3474220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474238 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_3474238 : Nat := 118140960795 + 3474238 * 2 ^ 59
def prefixEnd_3474238 : Nat := 4983230072969 + 3 ^ 40 * 3474238 * 2
def baseEnd_3474238 : Nat := 1783954002115283261547277

theorem tailTrace_3474238 : CollatzResearch.WordTrace tailWord_3474238 prefixEnd_3474238 1783954002115283261547277 := by
  unfold tailWord_3474238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839483748429569182036921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84477246658291035637530245 15839483748429569182036921)
  ·
    refine ⟨11879612811322176886527691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15839483748429569182036921 11879612811322176886527691)
    ·
      refine ⟨17819419216983265329791537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11879612811322176886527691 17819419216983265329791537)
      ·
        refine ⟨13364564412737448997343653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17819419216983265329791537 13364564412737448997343653)
        ·
          refine ⟨2505855827388271687001935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13364564412737448997343653 2505855827388271687001935)
          ·
            refine ⟨3758783741082407530502903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505855827388271687001935 3758783741082407530502903)
            ·
              refine ⟨5638175611623611295754355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758783741082407530502903 5638175611623611295754355)
              ·
                refine ⟨8457263417435416943631533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5638175611623611295754355 8457263417435416943631533)
                ·
                  refine ⟨3171473781538281353861825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8457263417435416943631533 3171473781538281353861825)
                  ·
                    refine ⟨2378605336153711015396369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3171473781538281353861825 2378605336153711015396369)
                    ·
                      refine ⟨1783954002115283261547277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378605336153711015396369 1783954002115283261547277)
                      ·
                        rfl

theorem cell23_3474238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_3474238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474238 prefixEnd_3474238 := by exact prefixLift 3474238
  have htrace : WordTrace (prefixWord ++ tailWord_3474238) baseStart_3474238 baseEnd_3474238 := by
    simpa [prefixWord, tailWord_3474238, baseEnd_3474238] using wordTrace_append hprefix tailTrace_3474238
  have hstable : (prefixWord ++ tailWord_3474238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474238).length < 2 ^ (prefixWord ++ tailWord_3474238).sum := by decide
  have hdescent : baseEnd_3474238 < baseStart_3474238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474243 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4]
def baseStart_3474243 : Nat := 118140960795 + 3474243 * 2 ^ 59
def prefixEnd_3474243 : Nat := 4983230072969 + 3 ^ 40 * 3474243 * 2
def baseEnd_3474243 : Nat := 1783956569518555741984753

theorem tailTrace_3474243 : CollatzResearch.WordTrace tailWord_3474243 prefixEnd_3474243 1783956569518555741984753 := by
  unfold tailWord_3474243
  simp only [CollatzResearch.WordTrace]
  refine ⟨126716052352418439310227383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84477368234945626206818255 126716052352418439310227383)
  ·
    refine ⟨190074078528627658965341075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126716052352418439310227383 190074078528627658965341075)
    ·
      refine ⟨285111117792941488448011613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190074078528627658965341075 285111117792941488448011613)
      ·
        refine ⟨106916669172353058168004355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285111117792941488448011613 106916669172353058168004355)
        ·
          refine ⟨160375003758529587252006533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106916669172353058168004355 160375003758529587252006533)
          ·
            refine ⟨30070313204724297609751225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160375003758529587252006533 30070313204724297609751225)
            ·
              refine ⟨22552734903543223207313419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30070313204724297609751225 22552734903543223207313419)
              ·
                refine ⟨33829102355314834810970129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22552734903543223207313419 33829102355314834810970129)
                ·
                  refine ⟨25371826766486126108227597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33829102355314834810970129 25371826766486126108227597)
                  ·
                    refine ⟨9514435037432297290585349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25371826766486126108227597 9514435037432297290585349)
                    ·
                      refine ⟨1783956569518555741984753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9514435037432297290585349 1783956569518555741984753)
                      ·
                        rfl

theorem cell23_3474243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_3474243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474243 prefixEnd_3474243 := by exact prefixLift 3474243
  have htrace : WordTrace (prefixWord ++ tailWord_3474243) baseStart_3474243 baseEnd_3474243 := by
    simpa [prefixWord, tailWord_3474243, baseEnd_3474243] using wordTrace_append hprefix tailTrace_3474243
  have hstable : (prefixWord ++ tailWord_3474243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474243).length < 2 ^ (prefixWord ++ tailWord_3474243).sum := by decide
  have hdescent : baseEnd_3474243 < baseStart_3474243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474273 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3474273 : Nat := 118140960795 + 3474273 * 2 ^ 59
def prefixEnd_3474273 : Nat := 4983230072969 + 3 ^ 40 * 3474273 * 2
def baseEnd_3474273 : Nat := 1783971973938190624609615

theorem tailTrace_3474273 : CollatzResearch.WordTrace tailWord_3474273 prefixEnd_3474273 1783971973938190624609615 := by
  unfold tailWord_3474273
  simp only [CollatzResearch.WordTrace]
  refine ⟨126717146542309754433819473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84478097694873169622546315 126717146542309754433819473)
  ·
    refine ⟨95037859906732315825364605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126717146542309754433819473 95037859906732315825364605)
    ·
      refine ⟨35639197465024618434511727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95037859906732315825364605 35639197465024618434511727)
      ·
        refine ⟨53458796197536927651767591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35639197465024618434511727 53458796197536927651767591)
        ·
          refine ⟨80188194296305391477651387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53458796197536927651767591 80188194296305391477651387)
          ·
            refine ⟨120282291444458087216477081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80188194296305391477651387 120282291444458087216477081)
            ·
              refine ⟨90211718583343565412357811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120282291444458087216477081 90211718583343565412357811)
              ·
                refine ⟨135317577875015348118536717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90211718583343565412357811 135317577875015348118536717)
                ·
                  refine ⟨50744091703130755544451269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135317577875015348118536717 50744091703130755544451269)
                  ·
                    refine ⟨9514517194337016664584613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50744091703130755544451269 9514517194337016664584613)
                    ·
                      refine ⟨1783971973938190624609615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9514517194337016664584613 1783971973938190624609615)
                      ·
                        rfl

theorem cell23_3474273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3474273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474273 prefixEnd_3474273 := by exact prefixLift 3474273
  have htrace : WordTrace (prefixWord ++ tailWord_3474273) baseStart_3474273 baseEnd_3474273 := by
    simpa [prefixWord, tailWord_3474273, baseEnd_3474273] using wordTrace_append hprefix tailTrace_3474273
  have hstable : (prefixWord ++ tailWord_3474273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474273).length < 2 ^ (prefixWord ++ tailWord_3474273).sum := by decide
  have hdescent : baseEnd_3474273 < baseStart_3474273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474277 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 6, 2, 2]
def baseStart_3474277 : Nat := 118140960795 + 3474277 * 2 ^ 59
def prefixEnd_3474277 : Nat := 4983230072969 + 3 ^ 40 * 3474277 * 2
def baseEnd_3474277 : Nat := 1783974027860808608959597

theorem tailTrace_3474277 : CollatzResearch.WordTrace tailWord_3474277 prefixEnd_3474277 1783974027860808608959597 := by
  unfold tailWord_3474277
  simp only [CollatzResearch.WordTrace]
  refine ⟨126717292434295263116965085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84478194956196842077976723 126717292434295263116965085)
  ·
    refine ⟨47518984662860723668861907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126717292434295263116965085 47518984662860723668861907)
    ·
      refine ⟨71278476994291085503292861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47518984662860723668861907 71278476994291085503292861)
      ·
        refine ⟨26729428872859157063734823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71278476994291085503292861 26729428872859157063734823)
        ·
          refine ⟨40094143309288735595602235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26729428872859157063734823 40094143309288735595602235)
          ·
            refine ⟨60141214963933103393403353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40094143309288735595602235 60141214963933103393403353)
            ·
              refine ⟨45105911222949827545052515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60141214963933103393403353 45105911222949827545052515)
              ·
                refine ⟨67658866834424741317578773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45105911222949827545052515 67658866834424741317578773)
                ·
                  refine ⟨3171509382863659749261505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67658866834424741317578773 3171509382863659749261505)
                  ·
                    refine ⟨2378632037147744811946129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3171509382863659749261505 2378632037147744811946129)
                    ·
                      refine ⟨1783974027860808608959597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378632037147744811946129 1783974027860808608959597)
                      ·
                        rfl

theorem cell23_3474277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_3474277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474277 prefixEnd_3474277 := by exact prefixLift 3474277
  have htrace : WordTrace (prefixWord ++ tailWord_3474277) baseStart_3474277 baseEnd_3474277 := by
    simpa [prefixWord, tailWord_3474277, baseEnd_3474277] using wordTrace_append hprefix tailTrace_3474277
  have hstable : (prefixWord ++ tailWord_3474277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474277).length < 2 ^ (prefixWord ++ tailWord_3474277).sum := by decide
  have hdescent : baseEnd_3474277 < baseStart_3474277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474280 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3474280 : Nat := 118140960795 + 3474280 * 2 ^ 59
def prefixEnd_3474280 : Nat := 4983230072969 + 3 ^ 40 * 3474280 * 2
def baseEnd_3474280 : Nat := 1783975568302772097222083

theorem tailTrace_3474280 : CollatzResearch.WordTrace tailWord_3474280 prefixEnd_3474280 1783975568302772097222083 := by
  unfold tailWord_3474280
  simp only [CollatzResearch.WordTrace]
  refine ⟨63358700926642197314662147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84478267902189596419549529 63358700926642197314662147)
  ·
    refine ⟨95038051389963295971993221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63358700926642197314662147 95038051389963295971993221)
    ·
      refine ⟨17819634635618117994748729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95038051389963295971993221 17819634635618117994748729)
      ·
        refine ⟨13364725976713588496061547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17819634635618117994748729 13364725976713588496061547)
        ·
          refine ⟨20047088965070382744092321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13364725976713588496061547 20047088965070382744092321)
          ·
            refine ⟨15035316723802787058069241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20047088965070382744092321 15035316723802787058069241)
            ·
              refine ⟨11276487542852090293551931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15035316723802787058069241 11276487542852090293551931)
              ·
                refine ⟨16914731314278135440327897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11276487542852090293551931 16914731314278135440327897)
                ·
                  refine ⟨12686048485708601580245923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16914731314278135440327897 12686048485708601580245923)
                  ·
                    refine ⟨19029072728562902370368885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12686048485708601580245923 19029072728562902370368885)
                    ·
                      refine ⟨1783975568302772097222083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19029072728562902370368885 1783975568302772097222083)
                      ·
                        rfl

theorem cell23_3474280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3474280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474280 prefixEnd_3474280 := by exact prefixLift 3474280
  have htrace : WordTrace (prefixWord ++ tailWord_3474280) baseStart_3474280 baseEnd_3474280 := by
    simpa [prefixWord, tailWord_3474280, baseEnd_3474280] using wordTrace_append hprefix tailTrace_3474280
  have hstable : (prefixWord ++ tailWord_3474280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474280).length < 2 ^ (prefixWord ++ tailWord_3474280).sum := by decide
  have hdescent : baseEnd_3474280 < baseStart_3474280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474320 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 7, 2]
def baseStart_3474320 : Nat := 118140960795 + 3474320 * 2 ^ 59
def prefixEnd_3474320 : Nat := 4983230072969 + 3 ^ 40 * 3474320 * 2
def baseEnd_3474320 : Nat := 1783996107528951940721899

theorem tailTrace_3474320 : CollatzResearch.WordTrace tailWord_3474320 prefixEnd_3474320 1783996107528951940721899 := by
  unfold tailWord_3474320
  simp only [CollatzResearch.WordTrace]
  refine ⟨63359430386569740730390207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84479240515426320973853609 63359430386569740730390207)
  ·
    refine ⟨95039145579854611095585311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63359430386569740730390207 95039145579854611095585311)
    ·
      refine ⟨142558718369781916643377967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95039145579854611095585311 142558718369781916643377967)
      ·
        refine ⟨213838077554672874965066951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142558718369781916643377967 213838077554672874965066951)
        ·
          refine ⟨320757116332009312447600427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213838077554672874965066951 320757116332009312447600427)
          ·
            refine ⟨481135674498013968671400641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320757116332009312447600427 481135674498013968671400641)
            ·
              refine ⟨360851755873510476503550481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481135674498013968671400641 360851755873510476503550481)
              ·
                refine ⟨270638816905132857377662861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360851755873510476503550481 270638816905132857377662861)
                ·
                  refine ⟨101489556339424821516623573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270638816905132857377662861 101489556339424821516623573)
                  ·
                    refine ⟨2378661476705269254295865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101489556339424821516623573 2378661476705269254295865)
                    ·
                      refine ⟨1783996107528951940721899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378661476705269254295865 1783996107528951940721899)
                      ·
                        rfl

theorem cell23_3474320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 7, 2].length) (baseStart_3474320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474320 prefixEnd_3474320 := by exact prefixLift 3474320
  have htrace : WordTrace (prefixWord ++ tailWord_3474320) baseStart_3474320 baseEnd_3474320 := by
    simpa [prefixWord, tailWord_3474320, baseEnd_3474320] using wordTrace_append hprefix tailTrace_3474320
  have hstable : (prefixWord ++ tailWord_3474320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474320).length < 2 ^ (prefixWord ++ tailWord_3474320).sum := by decide
  have hdescent : baseEnd_3474320 < baseStart_3474320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474323 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_3474323 : Nat := 118140960795 + 3474323 * 2 ^ 59
def prefixEnd_3474323 : Nat := 4983230072969 + 3 ^ 40 * 3474323 * 2
def baseEnd_3474323 : Nat := 1783997647970915428984385

theorem tailTrace_3474323 : CollatzResearch.WordTrace tailWord_3474323 prefixEnd_3474323 1783997647970915428984385 := by
  unfold tailWord_3474323
  simp only [CollatzResearch.WordTrace]
  refine ⟨126718970192128612973139623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84479313461419075315426415 126718970192128612973139623)
  ·
    refine ⟨190078455288192919459709435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126718970192128612973139623 190078455288192919459709435)
    ·
      refine ⟨285117682932289379189564153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190078455288192919459709435 285117682932289379189564153)
      ·
        refine ⟨213838262199217034392173115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285117682932289379189564153 213838262199217034392173115)
        ·
          refine ⟨320757393298825551588259673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213838262199217034392173115 320757393298825551588259673)
          ·
            refine ⟨240568044974119163691194755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320757393298825551588259673 240568044974119163691194755)
            ·
              refine ⟨360852067461178745536792133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240568044974119163691194755 360852067461178745536792133)
              ·
                refine ⟨67659762648971014788148525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360852067461178745536792133 67659762648971014788148525)
                ·
                  refine ⟨25372410993364130545555697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67659762648971014788148525 25372410993364130545555697)
                  ·
                    refine ⟨19029308245023097909166773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25372410993364130545555697 19029308245023097909166773)
                    ·
                      refine ⟨1783997647970915428984385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19029308245023097909166773 1783997647970915428984385)
                      ·
                        rfl

theorem cell23_3474323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_3474323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474323 prefixEnd_3474323 := by exact prefixLift 3474323
  have htrace : WordTrace (prefixWord ++ tailWord_3474323) baseStart_3474323 baseEnd_3474323 := by
    simpa [prefixWord, tailWord_3474323, baseEnd_3474323] using wordTrace_append hprefix tailTrace_3474323
  have hstable : (prefixWord ++ tailWord_3474323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474323).length < 2 ^ (prefixWord ++ tailWord_3474323).sum := by decide
  have hdescent : baseEnd_3474323 < baseStart_3474323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474363 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_3474363 : Nat := 118140960795 + 3474363 * 2 ^ 59
def prefixEnd_3474363 : Nat := 4983230072969 + 3 ^ 40 * 3474363 * 2
def baseEnd_3474363 : Nat := 1784018187197095272484201

theorem tailTrace_3474363 : CollatzResearch.WordTrace tailWord_3474363 prefixEnd_3474363 1784018187197095272484201 := by
  unfold tailWord_3474363
  simp only [CollatzResearch.WordTrace]
  refine ⟨126720429111983699804595743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84480286074655799869730495 126720429111983699804595743)
  ·
    refine ⟨190080643667975549706893615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126720429111983699804595743 190080643667975549706893615)
    ·
      refine ⟨285120965501963324560340423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190080643667975549706893615 285120965501963324560340423)
      ·
        refine ⟨427681448252944986840510635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285120965501963324560340423 427681448252944986840510635)
        ·
          refine ⟨641522172379417480260765953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427681448252944986840510635 641522172379417480260765953)
          ·
            refine ⟨481141629284563110195574465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641522172379417480260765953 481141629284563110195574465)
            ·
              refine ⟨360856221963422332646680849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481141629284563110195574465 360856221963422332646680849)
              ·
                refine ⟨270642166472566749485010637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360856221963422332646680849 270642166472566749485010637)
                ·
                  refine ⟨101490812427212531056878989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270642166472566749485010637 101490812427212531056878989)
                  ·
                    refine ⟨38059054660204699146329621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101490812427212531056878989 38059054660204699146329621)
                    ·
                      refine ⟨1784018187197095272484201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38059054660204699146329621 1784018187197095272484201)
                      ·
                        rfl

theorem cell23_3474363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_3474363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474363 prefixEnd_3474363 := by exact prefixLift 3474363
  have htrace : WordTrace (prefixWord ++ tailWord_3474363) baseStart_3474363 baseEnd_3474363 := by
    simpa [prefixWord, tailWord_3474363, baseEnd_3474363] using wordTrace_append hprefix tailTrace_3474363
  have hstable : (prefixWord ++ tailWord_3474363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474363).length < 2 ^ (prefixWord ++ tailWord_3474363).sum := by decide
  have hdescent : baseEnd_3474363 < baseStart_3474363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474380 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3474380 : Nat := 118140960795 + 3474380 * 2 ^ 59
def prefixEnd_3474380 : Nat := 4983230072969 + 3 ^ 40 * 3474380 * 2
def baseEnd_3474380 : Nat := 1784026916368221705971623

theorem tailTrace_3474380 : CollatzResearch.WordTrace tailWord_3474380 prefixEnd_3474380 1784026916368221705971623 := by
  unfold tailWord_3474380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63360524576461055853982297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84480699435281407805309729 63360524576461055853982297)
  ·
    refine ⟨47520393432345791890486723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63360524576461055853982297 47520393432345791890486723)
    ·
      refine ⟨71280590148518687835730085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47520393432345791890486723 71280590148518687835730085)
      ·
        refine ⟨13365110652847253969199391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71280590148518687835730085 13365110652847253969199391)
        ·
          refine ⟨20047665979270880953799087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13365110652847253969199391 20047665979270880953799087)
          ·
            refine ⟨30071498968906321430698631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20047665979270880953799087 30071498968906321430698631)
            ·
              refine ⟨45107248453359482146047947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30071498968906321430698631 45107248453359482146047947)
              ·
                refine ⟨67660872680039223219071921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45107248453359482146047947 67660872680039223219071921)
                ·
                  refine ⟨50745654510029417414303941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67660872680039223219071921 50745654510029417414303941)
                  ·
                    refine ⟨9514810220630515765181989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50745654510029417414303941 9514810220630515765181989)
                    ·
                      refine ⟨1784026916368221705971623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9514810220630515765181989 1784026916368221705971623)
                      ·
                        rfl

theorem cell23_3474380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3474380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474380 prefixEnd_3474380 := by exact prefixLift 3474380
  have htrace : WordTrace (prefixWord ++ tailWord_3474380) baseStart_3474380 baseEnd_3474380 := by
    simpa [prefixWord, tailWord_3474380, baseEnd_3474380] using wordTrace_append hprefix tailTrace_3474380
  have hstable : (prefixWord ++ tailWord_3474380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474380).length < 2 ^ (prefixWord ++ tailWord_3474380).sum := by decide
  have hdescent : baseEnd_3474380 < baseStart_3474380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474427 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 6, 3, 2]
def baseStart_3474427 : Nat := 118140960795 + 3474427 * 2 ^ 59
def prefixEnd_3474427 : Nat := 4983230072969 + 3 ^ 40 * 3474427 * 2
def baseEnd_3474427 : Nat := 1784051049958983022083907

theorem tailTrace_3474427 : CollatzResearch.WordTrace tailWord_3474427 prefixEnd_3474427 1784051049958983022083907 := by
  unfold tailWord_3474427
  simp only [CollatzResearch.WordTrace]
  refine ⟨126722763383751838734925535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84481842255834559156617023 126722763383751838734925535)
  ·
    refine ⟨190084145075627758102388303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126722763383751838734925535 190084145075627758102388303)
    ·
      refine ⟨285126217613441637153582455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190084145075627758102388303 285126217613441637153582455)
      ·
        refine ⟨427689326420162455730373683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285126217613441637153582455 427689326420162455730373683)
        ·
          refine ⟨641533989630243683595560525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427689326420162455730373683 641533989630243683595560525)
          ·
            refine ⟨240575246111341381348335197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641533989630243683595560525 240575246111341381348335197)
            ·
              refine ⟨90215717291753018005625699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240575246111341381348335197 90215717291753018005625699)
              ·
                refine ⟨135323575937629527008438549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90215717291753018005625699 135323575937629527008438549)
                ·
                  refine ⟨6343292622076384078520557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135323575937629527008438549 6343292622076384078520557)
                  ·
                    refine ⟨2378734733278644029445209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6343292622076384078520557 2378734733278644029445209)
                    ·
                      refine ⟨1784051049958983022083907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378734733278644029445209 1784051049958983022083907)
                      ·
                        rfl

theorem cell23_3474427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3, 2].length) (baseStart_3474427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474427 prefixEnd_3474427 := by exact prefixLift 3474427
  have htrace : WordTrace (prefixWord ++ tailWord_3474427) baseStart_3474427 baseEnd_3474427 := by
    simpa [prefixWord, tailWord_3474427, baseEnd_3474427] using wordTrace_append hprefix tailTrace_3474427
  have hstable : (prefixWord ++ tailWord_3474427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474427).length < 2 ^ (prefixWord ++ tailWord_3474427).sum := by decide
  have hdescent : baseEnd_3474427 < baseStart_3474427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474444 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2]
def baseStart_3474444 : Nat := 118140960795 + 3474444 * 2 ^ 59
def prefixEnd_3474444 : Nat := 4983230072969 + 3 ^ 40 * 3474444 * 2
def baseEnd_3474444 : Nat := 1784059779130109455571329

theorem tailTrace_3474444 : CollatzResearch.WordTrace tailWord_3474444 prefixEnd_3474444 1784059779130109455571329 := by
  unfold tailWord_3474444
  simp only [CollatzResearch.WordTrace]
  refine ⟨63361691712345125319147193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84482255616460167092196257 63361691712345125319147193)
  ·
    refine ⟨47521268784258843989360395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63361691712345125319147193 47521268784258843989360395)
    ·
      refine ⟨71281903176388265984040593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47521268784258843989360395 71281903176388265984040593)
      ·
        refine ⟨53461427382291199488030445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71281903176388265984040593 53461427382291199488030445)
        ·
          refine ⟨20048035268359199808011417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53461427382291199488030445 20048035268359199808011417)
          ·
            refine ⟨15036026451269399856008563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20048035268359199808011417 15036026451269399856008563)
            ·
              refine ⟨22554039676904099784012845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15036026451269399856008563 22554039676904099784012845)
              ·
                refine ⟨8457764878839037419004817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22554039676904099784012845 8457764878839037419004817)
                ·
                  refine ⟨6343323659129278064253613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8457764878839037419004817 6343323659129278064253613)
                  ·
                    refine ⟨2378746372173479274095105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6343323659129278064253613 2378746372173479274095105)
                    ·
                      refine ⟨1784059779130109455571329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378746372173479274095105 1784059779130109455571329)
                      ·
                        rfl

theorem cell23_3474444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_3474444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474444 prefixEnd_3474444 := by exact prefixLift 3474444
  have htrace : WordTrace (prefixWord ++ tailWord_3474444) baseStart_3474444 baseEnd_3474444 := by
    simpa [prefixWord, tailWord_3474444, baseEnd_3474444] using wordTrace_append hprefix tailTrace_3474444
  have hstable : (prefixWord ++ tailWord_3474444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474444).length < 2 ^ (prefixWord ++ tailWord_3474444).sum := by decide
  have hdescent : baseEnd_3474444 < baseStart_3474444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474457 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 4]
def baseStart_3474457 : Nat := 118140960795 + 3474457 * 2 ^ 59
def prefixEnd_3474457 : Nat := 4983230072969 + 3 ^ 40 * 3474457 * 2
def baseEnd_3474457 : Nat := 1784066454378617904708769

theorem tailTrace_3474457 : CollatzResearch.WordTrace tailWord_3474457 prefixEnd_3474457 1784066454378617904708769 := by
  unfold tailWord_3474457
  simp only [CollatzResearch.WordTrace]
  refine ⟨126723857573643153858517625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84482571715762102572345083 126723857573643153858517625)
  ·
    refine ⟨95042893180232365393888219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126723857573643153858517625 95042893180232365393888219)
    ·
      refine ⟨142564339770348548090832329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95042893180232365393888219 142564339770348548090832329)
      ·
        refine ⟨106923254827761411068124247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142564339770348548090832329 106923254827761411068124247)
        ·
          refine ⟨160384882241642116602186371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106923254827761411068124247 160384882241642116602186371)
          ·
            refine ⟨240577323362463174903279557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160384882241642116602186371 240577323362463174903279557)
            ·
              refine ⟨45108248130461845294364917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240577323362463174903279557 45108248130461845294364917)
              ·
                refine ⟨4228898262230797996346711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45108248130461845294364917 4228898262230797996346711)
                ·
                  refine ⟨6343347393346196994520067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228898262230797996346711 6343347393346196994520067)
                  ·
                    refine ⟨9515021090019295491780101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6343347393346196994520067 9515021090019295491780101)
                    ·
                      refine ⟨1784066454378617904708769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9515021090019295491780101 1784066454378617904708769)
                      ·
                        rfl

theorem cell23_3474457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_3474457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474457 prefixEnd_3474457 := by exact prefixLift 3474457
  have htrace : WordTrace (prefixWord ++ tailWord_3474457) baseStart_3474457 baseEnd_3474457 := by
    simpa [prefixWord, tailWord_3474457, baseEnd_3474457] using wordTrace_append hprefix tailTrace_3474457
  have hstable : (prefixWord ++ tailWord_3474457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474457).length < 2 ^ (prefixWord ++ tailWord_3474457).sum := by decide
  have hdescent : baseEnd_3474457 < baseStart_3474457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474468 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3474468 : Nat := 118140960795 + 3474468 * 2 ^ 59
def prefixEnd_3474468 : Nat := 4983230072969 + 3 ^ 40 * 3474468 * 2
def baseEnd_3474468 : Nat := 1784072102665817361671219

theorem tailTrace_3474468 : CollatzResearch.WordTrace tailWord_3474468 prefixEnd_3474468 1784072102665817361671219 := by
  unfold tailWord_3474468
  simp only [CollatzResearch.WordTrace]
  refine ⟨63362129388301651368584029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84482839184402201824778705 63362129388301651368584029)
  ·
    refine ⟨23760798520613119263219011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63362129388301651368584029 23760798520613119263219011)
    ·
      refine ⟨35641197780919678894828517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23760798520613119263219011 35641197780919678894828517)
      ·
        refine ⟨6682724583922439792780347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35641197780919678894828517 6682724583922439792780347)
        ·
          refine ⟨10024086875883659689170521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682724583922439792780347 10024086875883659689170521)
          ·
            refine ⟨7518065156912744766877891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10024086875883659689170521 7518065156912744766877891)
            ·
              refine ⟨11277097735369117150316837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518065156912744766877891 11277097735369117150316837)
              ·
                refine ⟨2114455825381709465684407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11277097735369117150316837 2114455825381709465684407)
                ·
                  refine ⟨3171683738072564198526611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114455825381709465684407 3171683738072564198526611)
                  ·
                    refine ⟨4757525607108846297789917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3171683738072564198526611 4757525607108846297789917)
                    ·
                      refine ⟨1784072102665817361671219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4757525607108846297789917 1784072102665817361671219)
                      ·
                        rfl

theorem cell23_3474468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3474468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474468 prefixEnd_3474468 := by exact prefixLift 3474468
  have htrace : WordTrace (prefixWord ++ tailWord_3474468) baseStart_3474468 baseEnd_3474468 := by
    simpa [prefixWord, tailWord_3474468, baseEnd_3474468] using wordTrace_append hprefix tailTrace_3474468
  have hstable : (prefixWord ++ tailWord_3474468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474468).length < 2 ^ (prefixWord ++ tailWord_3474468).sum := by decide
  have hdescent : baseEnd_3474468 < baseStart_3474468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474484 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3474484 : Nat := 118140960795 + 3474484 * 2 ^ 59
def prefixEnd_3474484 : Nat := 4983230072969 + 3 ^ 40 * 3474484 * 2
def baseEnd_3474484 : Nat := 594693439452096433023715

theorem tailTrace_3474484 : CollatzResearch.WordTrace tailWord_3474484 prefixEnd_3474484 594693439452096433023715 := by
  unfold tailWord_3474484
  simp only [CollatzResearch.WordTrace]
  refine ⟨63362421172272668734875253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84483228229696891646500337 63362421172272668734875253)
  ·
    refine ⟨5940226984900562693894555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63362421172272668734875253 5940226984900562693894555)
    ·
      refine ⟨8910340477350844040841833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940226984900562693894555 8910340477350844040841833)
      ·
        refine ⟨6682755358013133030631375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8910340477350844040841833 6682755358013133030631375)
        ·
          refine ⟨10024133037019699545947063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682755358013133030631375 10024133037019699545947063)
          ·
            refine ⟨15036199555529549318920595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024133037019699545947063 15036199555529549318920595)
            ·
              refine ⟨22554299333294323978380893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15036199555529549318920595 22554299333294323978380893)
              ·
                refine ⟨8457862249985371491892835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22554299333294323978380893 8457862249985371491892835)
                ·
                  refine ⟨12686793374978057237839253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8457862249985371491892835 12686793374978057237839253)
                  ·
                    refine ⟨594693439452096433023715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12686793374978057237839253 594693439452096433023715)
                    ·
                      rfl

theorem cell23_3474484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3474484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474484 prefixEnd_3474484 := by exact prefixLift 3474484
  have htrace : WordTrace (prefixWord ++ tailWord_3474484) baseStart_3474484 baseEnd_3474484 := by
    simpa [prefixWord, tailWord_3474484, baseEnd_3474484] using wordTrace_append hprefix tailTrace_3474484
  have hstable : (prefixWord ++ tailWord_3474484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474484).length < 2 ^ (prefixWord ++ tailWord_3474484).sum := by decide
  have hdescent : baseEnd_3474484 < baseStart_3474484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474518 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3474518 : Nat := 118140960795 + 3474518 * 2 ^ 59
def prefixEnd_3474518 : Nat := 4983230072969 + 3 ^ 40 * 3474518 * 2
def baseEnd_3474518 : Nat := 594699258899514055348663

theorem tailTrace_3474518 : CollatzResearch.WordTrace tailWord_3474518 prefixEnd_3474518 594699258899514055348663 := by
  unfold tailWord_3474518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7920380151651385079780513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84484054950948107517658805 7920380151651385079780513)
  ·
    refine ⟨5940285113738538809835385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7920380151651385079780513 5940285113738538809835385)
    ·
      refine ⟨4455213835303904107376539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5940285113738538809835385 4455213835303904107376539)
      ·
        refine ⟨6682820752955856161064809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455213835303904107376539 6682820752955856161064809)
        ·
          refine ⟨5012115564716892120798607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6682820752955856161064809 5012115564716892120798607)
          ·
            refine ⟨7518173347075338181197911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012115564716892120798607 7518173347075338181197911)
            ·
              refine ⟨11277260020613007271796867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518173347075338181197911 11277260020613007271796867)
              ·
                refine ⟨16915890030919510907695301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11277260020613007271796867 16915890030919510907695301)
                ·
                  refine ⟨3171729380797408295192869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16915890030919510907695301 3171729380797408295192869)
                  ·
                    refine ⟨594699258899514055348663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171729380797408295192869 594699258899514055348663)
                    ·
                      rfl

theorem cell23_3474518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3474518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474518 prefixEnd_3474518 := by exact prefixLift 3474518
  have htrace : WordTrace (prefixWord ++ tailWord_3474518) baseStart_3474518 baseEnd_3474518 := by
    simpa [prefixWord, tailWord_3474518, baseEnd_3474518] using wordTrace_append hprefix tailTrace_3474518
  have hstable : (prefixWord ++ tailWord_3474518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474518).length < 2 ^ (prefixWord ++ tailWord_3474518).sum := by decide
  have hdescent : baseEnd_3474518 < baseStart_3474518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474525 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3474525 : Nat := 118140960795 + 3474525 * 2 ^ 59
def prefixEnd_3474525 : Nat := 4983230072969 + 3 ^ 40 * 3474525 * 2
def baseEnd_3474525 : Nat := 1784101371063123638658457

theorem tailTrace_3474525 : CollatzResearch.WordTrace tailWord_3474525 prefixEnd_3474525 1784101371063123638658457 := by
  unfold tailWord_3474525
  simp only [CollatzResearch.WordTrace]
  refine ⟨126726337737396801471993029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84484225158264534314662019 126726337737396801471993029)
  ·
    refine ⟨23761188325761900275998693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126726337737396801471993029 23761188325761900275998693)
    ·
      refine ⟨4455222811080356301749755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23761188325761900275998693 4455222811080356301749755)
      ·
        refine ⟨6682834216620534452624633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455222811080356301749755 6682834216620534452624633)
        ·
          refine ⟨5012125662465400839468475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6682834216620534452624633 5012125662465400839468475)
          ·
            refine ⟨7518188493698101259202713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012125662465400839468475 7518188493698101259202713)
            ·
              refine ⟨5638641370273575944402035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518188493698101259202713 5638641370273575944402035)
              ·
                refine ⟨8457962055410363916603053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5638641370273575944402035 8457962055410363916603053)
                ·
                  refine ⟨3171735770778886468726145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8457962055410363916603053 3171735770778886468726145)
                  ·
                    refine ⟨2378801828084164851544609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3171735770778886468726145 2378801828084164851544609)
                    ·
                      refine ⟨1784101371063123638658457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378801828084164851544609 1784101371063123638658457)
                      ·
                        rfl

theorem cell23_3474525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3474525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474525 prefixEnd_3474525 := by exact prefixLift 3474525
  have htrace : WordTrace (prefixWord ++ tailWord_3474525) baseStart_3474525 baseEnd_3474525 := by
    simpa [prefixWord, tailWord_3474525, baseEnd_3474525] using wordTrace_append hprefix tailTrace_3474525
  have hstable : (prefixWord ++ tailWord_3474525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474525).length < 2 ^ (prefixWord ++ tailWord_3474525).sum := by decide
  have hdescent : baseEnd_3474525 < baseStart_3474525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474541 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3474541 : Nat := 118140960795 + 3474541 * 2 ^ 59
def prefixEnd_3474541 : Nat := 4983230072969 + 3 ^ 40 * 3474541 * 2
def baseEnd_3474541 : Nat := 1784109586753595576058383

theorem tailTrace_3474541 : CollatzResearch.WordTrace tailWord_3474541 prefixEnd_3474541 1784109586753595576058383 := by
  unfold tailWord_3474541
  simp only [CollatzResearch.WordTrace]
  refine ⟨126726921305338836204575477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84484614203559224136383651 126726921305338836204575477)
  ·
    refine ⟨11880648872375515894178951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126726921305338836204575477 11880648872375515894178951)
    ·
      refine ⟨17820973308563273841268427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11880648872375515894178951 17820973308563273841268427)
      ·
        refine ⟨26731459962844910761902641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17820973308563273841268427 26731459962844910761902641)
        ·
          refine ⟨20048594972133683071426981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26731459962844910761902641 20048594972133683071426981)
          ·
            refine ⟨3759111557275065575892559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20048594972133683071426981 3759111557275065575892559)
            ·
              refine ⟨5638667335912598363838839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759111557275065575892559 5638667335912598363838839)
              ·
                refine ⟨8458001003868897545758259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5638667335912598363838839 8458001003868897545758259)
                ·
                  refine ⟨12687001505803346318637389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8458001003868897545758259 12687001505803346318637389)
                  ·
                    refine ⟨4757625564676254869489021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12687001505803346318637389 4757625564676254869489021)
                    ·
                      refine ⟨1784109586753595576058383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4757625564676254869489021 1784109586753595576058383)
                      ·
                        rfl

theorem cell23_3474541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3474541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474541 prefixEnd_3474541 := by exact prefixLift 3474541
  have htrace : WordTrace (prefixWord ++ tailWord_3474541) baseStart_3474541 baseEnd_3474541 := by
    simpa [prefixWord, tailWord_3474541, baseEnd_3474541] using wordTrace_append hprefix tailTrace_3474541
  have hstable : (prefixWord ++ tailWord_3474541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474541).length < 2 ^ (prefixWord ++ tailWord_3474541).sum := by decide
  have hdescent : baseEnd_3474541 < baseStart_3474541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474551 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 1, 3, 2]
def baseStart_3474551 : Nat := 118140960795 + 3474551 * 2 ^ 59
def prefixEnd_3474551 : Nat := 4983230072969 + 3 ^ 40 * 3474551 * 2
def baseEnd_3474551 : Nat := 1784114721560140536933337

theorem tailTrace_3474551 : CollatzResearch.WordTrace tailWord_3474551 prefixEnd_3474551 1784114721560140536933337 := by
  unfold tailWord_3474551
  simp only [CollatzResearch.WordTrace]
  refine ⟨126727286035302607912439507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84484857356868405274959671 126727286035302607912439507)
  ·
    refine ⟨190090929052953911868659261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126727286035302607912439507 190090929052953911868659261)
    ·
      refine ⟨71284098394857716950747223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190090929052953911868659261 71284098394857716950747223)
      ·
        refine ⟨106926147592286575426120835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71284098394857716950747223 106926147592286575426120835)
        ·
          refine ⟨160389221388429863139181253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106926147592286575426120835 160389221388429863139181253)
          ·
            refine ⟨30072979010330599338596485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160389221388429863139181253 30072979010330599338596485)
            ·
              refine ⟨5638683564436987375986841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30072979010330599338596485 5638683564436987375986841)
              ·
                refine ⟨4229012673327740531990131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638683564436987375986841 4229012673327740531990131)
                ·
                  refine ⟨6343519009991610797985197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229012673327740531990131 6343519009991610797985197)
                  ·
                    refine ⟨2378819628746854049244449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6343519009991610797985197 2378819628746854049244449)
                    ·
                      refine ⟨1784114721560140536933337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378819628746854049244449 1784114721560140536933337)
                      ·
                        rfl

theorem cell23_3474551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_3474551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474551 prefixEnd_3474551 := by exact prefixLift 3474551
  have htrace : WordTrace (prefixWord ++ tailWord_3474551) baseStart_3474551 baseEnd_3474551 := by
    simpa [prefixWord, tailWord_3474551, baseEnd_3474551] using wordTrace_append hprefix tailTrace_3474551
  have hstable : (prefixWord ++ tailWord_3474551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474551).length < 2 ^ (prefixWord ++ tailWord_3474551).sum := by decide
  have hdescent : baseEnd_3474551 < baseStart_3474551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474567 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_3474567 : Nat := 118140960795 + 3474567 * 2 ^ 59
def prefixEnd_3474567 : Nat := 4983230072969 + 3 ^ 40 * 3474567 * 2
def baseEnd_3474567 : Nat := 1784122937250612474333263

theorem tailTrace_3474567 : CollatzResearch.WordTrace tailWord_3474567 prefixEnd_3474567 1784122937250612474333263 := by
  unfold tailWord_3474567
  simp only [CollatzResearch.WordTrace]
  refine ⟨126727869603244642645021955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84485246402163095096681303 126727869603244642645021955)
  ·
    refine ⟨190091804404866963967532933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126727869603244642645021955 190091804404866963967532933)
    ·
      refine ⟨35642213325912555743912425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190091804404866963967532933 35642213325912555743912425)
      ·
        refine ⟨26731659994434416807934319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35642213325912555743912425 26731659994434416807934319)
        ·
          refine ⟨40097489991651625211901479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26731659994434416807934319 40097489991651625211901479)
          ·
            refine ⟨60146234987477437817852219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40097489991651625211901479 60146234987477437817852219)
            ·
              refine ⟨90219352481216156726778329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60146234987477437817852219 90219352481216156726778329)
              ·
                refine ⟨67664514360912117545083747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90219352481216156726778329 67664514360912117545083747)
                ·
                  refine ⟨101496771541368176317625621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67664514360912117545083747 101496771541368176317625621)
                  ·
                    refine ⟨4757661166001633264888701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101496771541368176317625621 4757661166001633264888701)
                    ·
                      refine ⟨1784122937250612474333263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4757661166001633264888701 1784122937250612474333263)
                      ·
                        rfl

theorem cell23_3474567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_3474567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474567 prefixEnd_3474567 := by exact prefixLift 3474567
  have htrace : WordTrace (prefixWord ++ tailWord_3474567) baseStart_3474567 baseEnd_3474567 := by
    simpa [prefixWord, tailWord_3474567, baseEnd_3474567] using wordTrace_append hprefix tailTrace_3474567
  have hstable : (prefixWord ++ tailWord_3474567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474567).length < 2 ^ (prefixWord ++ tailWord_3474567).sum := by decide
  have hdescent : baseEnd_3474567 < baseStart_3474567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474634 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3474634 : Nat := 118140960795 + 3474634 * 2 ^ 59
def prefixEnd_3474634 : Nat := 4983230072969 + 3 ^ 40 * 3474634 * 2
def baseEnd_3474634 : Nat := 594719113484821237398485

theorem tailTrace_3474634 : CollatzResearch.WordTrace tailWord_3474634 prefixEnd_3474634 594719113484821237398485 := by
  unfold tailWord_3474634
  simp only [CollatzResearch.WordTrace]
  refine ⟨31682578323500478271927739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84486875529334608725140637 31682578323500478271927739)
  ·
    refine ⟨47523867485250717407891609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31682578323500478271927739 47523867485250717407891609)
    ·
      refine ⟨35642900613938038055918707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47523867485250717407891609 35642900613938038055918707)
      ·
        refine ⟨53464350920907057083878061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35642900613938038055918707 53464350920907057083878061)
        ·
          refine ⟨20049131595340146406454273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53464350920907057083878061 20049131595340146406454273)
          ·
            refine ⟨15036848696505109804840705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20049131595340146406454273 15036848696505109804840705)
            ·
              refine ⟨11277636522378832353630529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15036848696505109804840705 11277636522378832353630529)
              ·
                refine ⟨8458227391784124265222897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11277636522378832353630529 8458227391784124265222897)
                ·
                  refine ⟨6343670543838093198917173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8458227391784124265222897 6343670543838093198917173)
                  ·
                    refine ⟨594719113484821237398485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6343670543838093198917173 594719113484821237398485)
                    ·
                      rfl

theorem cell23_3474634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3474634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474634 prefixEnd_3474634 := by exact prefixLift 3474634
  have htrace : WordTrace (prefixWord ++ tailWord_3474634) baseStart_3474634 baseEnd_3474634 := by
    simpa [prefixWord, tailWord_3474634, baseEnd_3474634] using wordTrace_append hprefix tailTrace_3474634
  have hstable : (prefixWord ++ tailWord_3474634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474634).length < 2 ^ (prefixWord ++ tailWord_3474634).sum := by decide
  have hdescent : baseEnd_3474634 < baseStart_3474634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474697 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_3474697 : Nat := 118140960795 + 3474697 * 2 ^ 59
def prefixEnd_3474697 : Nat := 4983230072969 + 3 ^ 40 * 3474697 * 2
def baseEnd_3474697 : Nat := 1784189689735696965707665

theorem tailTrace_3474697 : CollatzResearch.WordTrace tailWord_3474697 prefixEnd_3474697 1784189689735696965707665 := by
  unfold tailWord_3474697
  simp only [CollatzResearch.WordTrace]
  refine ⟨126732611092773674847254345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84488407395182449898169563 126732611092773674847254345)
  ·
    refine ⟨95049458319580256135440759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126732611092773674847254345 95049458319580256135440759)
    ·
      refine ⟨142574187479370384203161139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95049458319580256135440759 142574187479370384203161139)
      ·
        refine ⟨213861281219055576304741709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142574187479370384203161139 213861281219055576304741709)
        ·
          refine ⟨80197980457145841114278141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213861281219055576304741709 80197980457145841114278141)
          ·
            refine ⟨30074242671429690417854303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80197980457145841114278141 30074242671429690417854303)
            ·
              refine ⟨45111364007144535626781455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30074242671429690417854303 45111364007144535626781455)
              ·
                refine ⟨67667046010716803440172183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45111364007144535626781455 67667046010716803440172183)
                ·
                  refine ⟨101500569016075205160258275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67667046010716803440172183 101500569016075205160258275)
                  ·
                    refine ⟨152250853524112807740387413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101500569016075205160258275 152250853524112807740387413)
                    ·
                      refine ⟨1784189689735696965707665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 152250853524112807740387413 1784189689735696965707665)
                      ·
                        rfl

theorem cell23_3474697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_3474697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474697 prefixEnd_3474697 := by exact prefixLift 3474697
  have htrace : WordTrace (prefixWord ++ tailWord_3474697) baseStart_3474697 baseEnd_3474697 := by
    simpa [prefixWord, tailWord_3474697, baseEnd_3474697] using wordTrace_append hprefix tailTrace_3474697
  have hstable : (prefixWord ++ tailWord_3474697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474697).length < 2 ^ (prefixWord ++ tailWord_3474697).sum := by decide
  have hdescent : baseEnd_3474697 < baseStart_3474697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474711 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 6]
def baseStart_3474711 : Nat := 118140960795 + 3474711 * 2 ^ 59
def prefixEnd_3474711 : Nat := 4983230072969 + 3 ^ 40 * 3474711 * 2
def baseEnd_3474711 : Nat := 198244097607206656770289

theorem tailTrace_3474711 : CollatzResearch.WordTrace tailWord_3474711 prefixEnd_3474711 198244097607206656770289 := by
  unfold tailWord_3474711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126733121714722955238263987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84488747809815303492175991 126733121714722955238263987)
  ·
    refine ⟨190099682572084432857395981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126733121714722955238263987 190099682572084432857395981)
    ·
      refine ⟨71287380964531662321523493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190099682572084432857395981 71287380964531662321523493)
      ·
        refine ⟨13366383930849686685285655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71287380964531662321523493 13366383930849686685285655)
        ·
          refine ⟨20049575896274530027928483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13366383930849686685285655 20049575896274530027928483)
          ·
            refine ⟨30074363844411795041892725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20049575896274530027928483 30074363844411795041892725)
            ·
              refine ⟨2819471610413605785177443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30074363844411795041892725 2819471610413605785177443)
              ·
                refine ⟨4229207415620408677766165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819471610413605785177443 4229207415620408677766165)
                ·
                  refine ⟨198244097607206656770289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4229207415620408677766165 198244097607206656770289)
                  ·
                    rfl

theorem cell23_3474711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 6].length) (baseStart_3474711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474711 prefixEnd_3474711 := by exact prefixLift 3474711
  have htrace : WordTrace (prefixWord ++ tailWord_3474711) baseStart_3474711 baseEnd_3474711 := by
    simpa [prefixWord, tailWord_3474711, baseEnd_3474711] using wordTrace_append hprefix tailTrace_3474711
  have hstable : (prefixWord ++ tailWord_3474711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474711).length < 2 ^ (prefixWord ++ tailWord_3474711).sum := by decide
  have hdescent : baseEnd_3474711 < baseStart_3474711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474741 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3474741 : Nat := 118140960795 + 3474741 * 2 ^ 59
def prefixEnd_3474741 : Nat := 4983230072969 + 3 ^ 40 * 3474741 * 2
def baseEnd_3474741 : Nat := 594737427628164931185821

theorem tailTrace_3474741 : CollatzResearch.WordTrace tailWord_3474741 prefixEnd_3474741 594737427628164931185821 := by
  unfold tailWord_3474741
  simp only [CollatzResearch.WordTrace]
  refine ⟨126734215904614270361856077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84489477269742846907904051 126734215904614270361856077)
  ·
    refine ⟨47525330964230351385696029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126734215904614270361856077 47525330964230351385696029)
    ·
      refine ⟨17821999111586381769636011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47525330964230351385696029 17821999111586381769636011)
      ·
        refine ⟨26732998667379572654454017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17821999111586381769636011 26732998667379572654454017)
        ·
          refine ⟨20049749000534679490840513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26732998667379572654454017 20049749000534679490840513)
          ·
            refine ⟨15037311750401009618130385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20049749000534679490840513 15037311750401009618130385)
            ·
              refine ⟨11277983812800757213597789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15037311750401009618130385 11277983812800757213597789)
              ·
                refine ⟨4229243929800283955099171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11277983812800757213597789 4229243929800283955099171)
                ·
                  refine ⟨6343865894700425932648757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229243929800283955099171 6343865894700425932648757)
                  ·
                    refine ⟨594737427628164931185821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6343865894700425932648757 594737427628164931185821)
                    ·
                      rfl

theorem cell23_3474741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3474741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474741 prefixEnd_3474741 := by exact prefixLift 3474741
  have htrace : WordTrace (prefixWord ++ tailWord_3474741) baseStart_3474741 baseEnd_3474741 := by
    simpa [prefixWord, tailWord_3474741, baseEnd_3474741] using wordTrace_append hprefix tailTrace_3474741
  have hstable : (prefixWord ++ tailWord_3474741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474741).length < 2 ^ (prefixWord ++ tailWord_3474741).sum := by decide
  have hdescent : baseEnd_3474741 < baseStart_3474741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474744 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_3474744 : Nat := 118140960795 + 3474744 * 2 ^ 59
def prefixEnd_3474744 : Nat := 4983230072969 + 3 ^ 40 * 3474744 * 2
def baseEnd_3474744 : Nat := 1784213823326458281819949

theorem tailTrace_3474744 : CollatzResearch.WordTrace tailWord_3474744 prefixEnd_3474744 1784213823326458281819949 := by
  unfold tailWord_3474744
  simp only [CollatzResearch.WordTrace]
  refine ⟨63367162661801700937107643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84489550215735601249476857 63367162661801700937107643)
  ·
    refine ⟨95050743992702551405661465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63367162661801700937107643 95050743992702551405661465)
    ·
      refine ⟨71288057994526913554246099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95050743992702551405661465 71288057994526913554246099)
      ·
        refine ⟨106932086991790370331369149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71288057994526913554246099 106932086991790370331369149)
        ·
          refine ⟨40099532621921388874263431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106932086991790370331369149 40099532621921388874263431)
          ·
            refine ⟨60149298932882083311395147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40099532621921388874263431 60149298932882083311395147)
            ·
              refine ⟨90223948399323124967092721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60149298932882083311395147 90223948399323124967092721)
              ·
                refine ⟨67667961299492343725319541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90223948399323124967092721 67667961299492343725319541)
                ·
                  refine ⟨6343871371827407224248707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67667961299492343725319541 6343871371827407224248707)
                  ·
                    refine ⟨9515807057741110836373061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6343871371827407224248707 9515807057741110836373061)
                    ·
                      refine ⟨1784213823326458281819949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9515807057741110836373061 1784213823326458281819949)
                      ·
                        rfl

theorem cell23_3474744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_3474744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474744 prefixEnd_3474744 := by exact prefixLift 3474744
  have htrace : WordTrace (prefixWord ++ tailWord_3474744) baseStart_3474744 baseEnd_3474744 := by
    simpa [prefixWord, tailWord_3474744, baseEnd_3474744] using wordTrace_append hprefix tailTrace_3474744
  have hstable : (prefixWord ++ tailWord_3474744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474744).length < 2 ^ (prefixWord ++ tailWord_3474744).sum := by decide
  have hdescent : baseEnd_3474744 < baseStart_3474744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474748 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_3474748 : Nat := 118140960795 + 3474748 * 2 ^ 59
def prefixEnd_3474748 : Nat := 4983230072969 + 3 ^ 40 * 3474748 * 2
def baseEnd_3474748 : Nat := 1784215877249076266169931

theorem tailTrace_3474748 : CollatzResearch.WordTrace tailWord_3474748 prefixEnd_3474748 1784215877249076266169931 := by
  unfold tailWord_3474748
  simp only [CollatzResearch.WordTrace]
  refine ⟨63367235607794455278680449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84489647477059273704907265 63367235607794455278680449)
  ·
    refine ⟨47525426705845841459010337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63367235607794455278680449 47525426705845841459010337)
    ·
      refine ⟨35644070029384381094257753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47525426705845841459010337 35644070029384381094257753)
      ·
        refine ⟨26733052522038285820693315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35644070029384381094257753 26733052522038285820693315)
        ·
          refine ⟨40099578783057428731039973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26733052522038285820693315 40099578783057428731039973)
          ·
            refine ⟨7518671021823267887069995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40099578783057428731039973 7518671021823267887069995)
            ·
              refine ⟨11278006532734901830604993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518671021823267887069995 11278006532734901830604993)
              ·
                refine ⟨8458504899551176372953745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11278006532734901830604993 8458504899551176372953745)
                ·
                  refine ⟨6343878674663382279715309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8458504899551176372953745 6343878674663382279715309)
                  ·
                    refine ⟨2378954502998768354893241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6343878674663382279715309 2378954502998768354893241)
                    ·
                      refine ⟨1784215877249076266169931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378954502998768354893241 1784215877249076266169931)
                      ·
                        rfl

theorem cell23_3474748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_3474748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474748 prefixEnd_3474748 := by exact prefixLift 3474748
  have htrace : WordTrace (prefixWord ++ tailWord_3474748) baseStart_3474748 baseEnd_3474748 := by
    simpa [prefixWord, tailWord_3474748, baseEnd_3474748] using wordTrace_append hprefix tailTrace_3474748
  have hstable : (prefixWord ++ tailWord_3474748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474748).length < 2 ^ (prefixWord ++ tailWord_3474748).sum := by decide
  have hdescent : baseEnd_3474748 < baseStart_3474748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474771 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 2, 4]
def baseStart_3474771 : Nat := 118140960795 + 3474771 * 2 ^ 59
def prefixEnd_3474771 : Nat := 4983230072969 + 3 ^ 40 * 3474771 * 2
def baseEnd_3474771 : Nat := 594742562434709892060775

theorem tailTrace_3474771 : CollatzResearch.WordTrace tailWord_3474771 prefixEnd_3474771 594742562434709892060775 := by
  unfold tailWord_3474771
  simp only [CollatzResearch.WordTrace]
  refine ⟨126735310094505585485448167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84490206729670390323632111 126735310094505585485448167)
  ·
    refine ⟨190102965141758378228172251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126735310094505585485448167 190102965141758378228172251)
    ·
      refine ⟨285154447712637567342258377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190102965141758378228172251 285154447712637567342258377)
      ·
        refine ⟨213865835784478175506693783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285154447712637567342258377 213865835784478175506693783)
        ·
          refine ⟨320798753676717263260040675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213865835784478175506693783 320798753676717263260040675)
          ·
            refine ⟨481198130515075894890061013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320798753676717263260040675 481198130515075894890061013)
            ·
              refine ⟨11278081183947091286485805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 481198130515075894890061013 11278081183947091286485805)
              ·
                refine ⟨4229280443980159232432177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11278081183947091286485805 4229280443980159232432177)
                ·
                  refine ⟨3171960332985119424324133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4229280443980159232432177 3171960332985119424324133)
                  ·
                    refine ⟨594742562434709892060775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171960332985119424324133 594742562434709892060775)
                    ·
                      rfl

theorem cell23_3474771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 4].length) (baseStart_3474771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474771 prefixEnd_3474771 := by exact prefixLift 3474771
  have htrace : WordTrace (prefixWord ++ tailWord_3474771) baseStart_3474771 baseEnd_3474771 := by
    simpa [prefixWord, tailWord_3474771, baseEnd_3474771] using wordTrace_append hprefix tailTrace_3474771
  have hstable : (prefixWord ++ tailWord_3474771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474771).length < 2 ^ (prefixWord ++ tailWord_3474771).sum := by decide
  have hdescent : baseEnd_3474771 < baseStart_3474771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474778 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2]
def baseStart_3474778 : Nat := 118140960795 + 3474778 * 2 ^ 59
def prefixEnd_3474778 : Nat := 4983230072969 + 3 ^ 40 * 3474778 * 2
def baseEnd_3474778 : Nat := 1784231281668711148794793

theorem tailTrace_3474778 : CollatzResearch.WordTrace tailWord_3474778 prefixEnd_3474778 1784231281668711148794793 := by
  unfold tailWord_3474778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31683891351370056420238247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84490376936986817120635325 31683891351370056420238247)
  ·
    refine ⟨47525837027055084630357371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31683891351370056420238247 47525837027055084630357371)
    ·
      refine ⟨71288755540582626945536057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47525837027055084630357371 71288755540582626945536057)
      ·
        refine ⟨53466566655436970209152043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71288755540582626945536057 53466566655436970209152043)
        ·
          refine ⟨80199849983155455313728065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53466566655436970209152043 80199849983155455313728065)
          ·
            refine ⟨60149887487366591485296049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80199849983155455313728065 60149887487366591485296049)
            ·
              refine ⟨45112415615524943613972037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60149887487366591485296049 45112415615524943613972037)
              ·
                refine ⟨8458577927910926927619757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45112415615524943613972037 8458577927910926927619757)
                ·
                  refine ⟨3171966722966597597857409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8458577927910926927619757 3171966722966597597857409)
                  ·
                    refine ⟨2378975042224948198393057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3171966722966597597857409 2378975042224948198393057)
                    ·
                      refine ⟨1784231281668711148794793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2378975042224948198393057 1784231281668711148794793)
                      ·
                        rfl

theorem cell23_3474778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_3474778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474778 prefixEnd_3474778 := by exact prefixLift 3474778
  have htrace : WordTrace (prefixWord ++ tailWord_3474778) baseStart_3474778 baseEnd_3474778 := by
    simpa [prefixWord, tailWord_3474778, baseEnd_3474778] using wordTrace_append hprefix tailTrace_3474778
  have hstable : (prefixWord ++ tailWord_3474778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474778).length < 2 ^ (prefixWord ++ tailWord_3474778).sum := by decide
  have hdescent : baseEnd_3474778 < baseStart_3474778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474784 : List Nat := [2, 1, 1, 3, 4, 1, 2, 9]
def baseStart_3474784 : Nat := 118140960795 + 3474784 * 2 ^ 59
def prefixEnd_3474784 : Nat := 4983230072969 + 3 ^ 40 * 3474784 * 2
def baseEnd_3474784 : Nat := 66082754168616226863695

theorem tailTrace_3474784 : CollatzResearch.WordTrace tailWord_3474784 prefixEnd_3474784 66082754168616226863695 := by
  unfold tailWord_3474784
  simp only [CollatzResearch.WordTrace]
  refine ⟨63367892121729244352835703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84490522828972325803780937 63367892121729244352835703)
  ·
    refine ⟨95051838182593866529253555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63367892121729244352835703 95051838182593866529253555)
    ·
      refine ⟨142577757273890799793880333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95051838182593866529253555 142577757273890799793880333)
      ·
        refine ⟨53466658977709049922705125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142577757273890799793880333 53466658977709049922705125)
        ·
          refine ⟨10024998558320446860507211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53466658977709049922705125 10024998558320446860507211)
          ·
            refine ⟨15037497837480670290760817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024998558320446860507211 15037497837480670290760817)
            ·
              refine ⟨11278123378110502718070613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15037497837480670290760817 11278123378110502718070613)
              ·
                refine ⟨66082754168616226863695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11278123378110502718070613 66082754168616226863695)
                ·
                  rfl

theorem cell23_3474784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 9].length) (baseStart_3474784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474784 prefixEnd_3474784 := by exact prefixLift 3474784
  have htrace : WordTrace (prefixWord ++ tailWord_3474784) baseStart_3474784 baseEnd_3474784 := by
    simpa [prefixWord, tailWord_3474784, baseEnd_3474784] using wordTrace_append hprefix tailTrace_3474784
  have hstable : (prefixWord ++ tailWord_3474784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474784).length < 2 ^ (prefixWord ++ tailWord_3474784).sum := by decide
  have hdescent : baseEnd_3474784 < baseStart_3474784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474805 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3474805 : Nat := 118140960795 + 3474805 * 2 ^ 59
def prefixEnd_3474805 : Nat := 4983230072969 + 3 ^ 40 * 3474805 * 2
def baseEnd_3474805 : Nat := 594748381882127514385723

theorem tailTrace_3474805 : CollatzResearch.WordTrace tailWord_3474805 prefixEnd_3474805 594748381882127514385723 := by
  unfold tailWord_3474805
  simp only [CollatzResearch.WordTrace]
  refine ⟨126736550176382409292185869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84491033450921606194790579 126736550176382409292185869)
  ·
    refine ⟨47526206316143403484569701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126736550176382409292185869 47526206316143403484569701)
    ·
      refine ⟨8911163684276888153356819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47526206316143403484569701 8911163684276888153356819)
      ·
        refine ⟨13366745526415332230035229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8911163684276888153356819 13366745526415332230035229)
        ·
          refine ⟨5012529572405749586263211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13366745526415332230035229 5012529572405749586263211)
          ·
            refine ⟨7518794358608624379394817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012529572405749586263211 7518794358608624379394817)
            ·
              refine ⟨5639095768956468284546113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518794358608624379394817 5639095768956468284546113)
              ·
                refine ⟨4229321826717351213409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5639095768956468284546113 4229321826717351213409585)
                ·
                  refine ⟨3171991370038013410057189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4229321826717351213409585 3171991370038013410057189)
                  ·
                    refine ⟨594748381882127514385723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171991370038013410057189 594748381882127514385723)
                    ·
                      rfl

theorem cell23_3474805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3474805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474805 prefixEnd_3474805 := by exact prefixLift 3474805
  have htrace : WordTrace (prefixWord ++ tailWord_3474805) baseStart_3474805 baseEnd_3474805 := by
    simpa [prefixWord, tailWord_3474805, baseEnd_3474805] using wordTrace_append hprefix tailTrace_3474805
  have hstable : (prefixWord ++ tailWord_3474805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474805).length < 2 ^ (prefixWord ++ tailWord_3474805).sum := by decide
  have hdescent : baseEnd_3474805 < baseStart_3474805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474818 : List Nat := [3, 4, 2, 1, 1, 1, 3, 8]
def baseStart_3474818 : Nat := 118140960795 + 3474818 * 2 ^ 59
def prefixEnd_3474818 : Nat := 4983230072969 + 3 ^ 40 * 3474818 * 2
def baseEnd_3474818 : Nat := 66083400773884851566467

theorem tailTrace_3474818 : CollatzResearch.WordTrace tailWord_3474818 prefixEnd_3474818 66083400773884851566467 := by
  unfold tailWord_3474818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31684256081333828128102277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84491349550223541674939405 31684256081333828128102277)
  ·
    refine ⟨5940798015250092774019177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31684256081333828128102277 5940798015250092774019177)
    ·
      refine ⟨4455598511437569580514383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5940798015250092774019177 4455598511437569580514383)
      ·
        refine ⟨6683397767156354370771575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455598511437569580514383 6683397767156354370771575)
        ·
          refine ⟨10025096650734531556157363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6683397767156354370771575 10025096650734531556157363)
          ·
            refine ⟨15037644976101797334236045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10025096650734531556157363 15037644976101797334236045)
            ·
              refine ⟨5639116866038174000338517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15037644976101797334236045 5639116866038174000338517)
              ·
                refine ⟨66083400773884851566467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5639116866038174000338517 66083400773884851566467)
                ·
                  rfl

theorem cell23_3474818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_3474818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474818 prefixEnd_3474818 := by exact prefixLift 3474818
  have htrace : WordTrace (prefixWord ++ tailWord_3474818) baseStart_3474818 baseEnd_3474818 := by
    simpa [prefixWord, tailWord_3474818, baseEnd_3474818] using wordTrace_append hprefix tailTrace_3474818
  have hstable : (prefixWord ++ tailWord_3474818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474818).length < 2 ^ (prefixWord ++ tailWord_3474818).sum := by decide
  have hdescent : baseEnd_3474818 < baseStart_3474818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474828 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3474828 : Nat := 118140960795 + 3474828 * 2 ^ 59
def prefixEnd_3474828 : Nat := 4983230072969 + 3 ^ 40 * 3474828 * 2
def baseEnd_3474828 : Nat := 1784256955701435953169563

theorem tailTrace_3474828 : CollatzResearch.WordTrace tailWord_3474828 prefixEnd_3474828 1784256955701435953169563 := by
  unfold tailWord_3474828
  simp only [CollatzResearch.WordTrace]
  refine ⟨63368694527649542110136569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84491592703532722813515425 63368694527649542110136569)
  ·
    refine ⟨47526520895737156582602427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63368694527649542110136569 47526520895737156582602427)
    ·
      refine ⟨71289781343605734873903641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47526520895737156582602427 71289781343605734873903641)
      ·
        refine ⟨53467336007704301155427731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71289781343605734873903641 53467336007704301155427731)
        ·
          refine ⟨80201004011556451733141597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53467336007704301155427731 80201004011556451733141597)
          ·
            refine ⟨30075376504333669399928099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80201004011556451733141597 30075376504333669399928099)
            ·
              refine ⟨45113064756500504099892149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30075376504333669399928099 45113064756500504099892149)
              ·
                refine ⟨4229349820921922259364889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45113064756500504099892149 4229349820921922259364889)
                ·
                  refine ⟨3172012365691441694523667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4229349820921922259364889 3172012365691441694523667)
                  ·
                    refine ⟨4758018548537162541785501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3172012365691441694523667 4758018548537162541785501)
                    ·
                      refine ⟨1784256955701435953169563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4758018548537162541785501 1784256955701435953169563)
                      ·
                        rfl

theorem cell23_3474828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3474828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474828 prefixEnd_3474828 := by exact prefixLift 3474828
  have htrace : WordTrace (prefixWord ++ tailWord_3474828) baseStart_3474828 baseEnd_3474828 := by
    simpa [prefixWord, tailWord_3474828, baseEnd_3474828] using wordTrace_append hprefix tailTrace_3474828
  have hstable : (prefixWord ++ tailWord_3474828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474828).length < 2 ^ (prefixWord ++ tailWord_3474828).sum := by decide
  have hdescent : baseEnd_3474828 < baseStart_3474828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474846 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3474846 : Nat := 118140960795 + 3474846 * 2 ^ 59
def prefixEnd_3474846 : Nat := 4983230072969 + 3 ^ 40 * 3474846 * 2
def baseEnd_3474846 : Nat := 1784266198353216882744481

theorem tailTrace_3474846 : CollatzResearch.WordTrace tailWord_3474846 prefixEnd_3474846 1784266198353216882744481 := by
  unfold tailWord_3474846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842255696154234161803549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84492030379489248862952261 15842255696154234161803549)
  ·
    refine ⟨5940845886057837810676331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15842255696154234161803549 5940845886057837810676331)
    ·
      refine ⟨8911268829086756716014497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940845886057837810676331 8911268829086756716014497)
      ·
        refine ⟨6683451621815067537010873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8911268829086756716014497 6683451621815067537010873)
        ·
          refine ⟨5012588716361300652758155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6683451621815067537010873 5012588716361300652758155)
          ·
            refine ⟨7518883074541950979137233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012588716361300652758155 7518883074541950979137233)
            ·
              refine ⟨5639162305906463234352925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518883074541950979137233 5639162305906463234352925)
              ·
                refine ⟨2114685864714923712882347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5639162305906463234352925 2114685864714923712882347)
                ·
                  refine ⟨3172028797072385569323521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114685864714923712882347 3172028797072385569323521)
                  ·
                    refine ⟨2379021597804289176992641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3172028797072385569323521 2379021597804289176992641)
                    ·
                      refine ⟨1784266198353216882744481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379021597804289176992641 1784266198353216882744481)
                      ·
                        rfl

theorem cell23_3474846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3474846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474846 prefixEnd_3474846 := by exact prefixLift 3474846
  have htrace : WordTrace (prefixWord ++ tailWord_3474846) baseStart_3474846 baseEnd_3474846 := by
    simpa [prefixWord, tailWord_3474846, baseEnd_3474846] using wordTrace_append hprefix tailTrace_3474846
  have hstable : (prefixWord ++ tailWord_3474846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474846).length < 2 ^ (prefixWord ++ tailWord_3474846).sum := by decide
  have hdescent : baseEnd_3474846 < baseStart_3474846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474855 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_3474855 : Nat := 118140960795 + 3474855 * 2 ^ 59
def prefixEnd_3474855 : Nat := 4983230072969 + 3 ^ 40 * 3474855 * 2
def baseEnd_3474855 : Nat := 1784270819679107347531939

theorem tailTrace_3474855 : CollatzResearch.WordTrace tailWord_3474855 prefixEnd_3474855 1784270819679107347531939 := by
  unfold tailWord_3474855
  simp only [CollatzResearch.WordTrace]
  refine ⟨126738373826201267831506019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84492249217467511887670679 126738373826201267831506019)
  ·
    refine ⟨190107560739301901747259029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126738373826201267831506019 190107560739301901747259029)
    ·
      refine ⟨8911291909654776644402767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190107560739301901747259029 8911291909654776644402767)
      ·
        refine ⟨13366937864482164966604151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8911291909654776644402767 13366937864482164966604151)
        ·
          refine ⟨20050406796723247449906227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13366937864482164966604151 20050406796723247449906227)
          ·
            refine ⟨30075610195084871174859341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20050406796723247449906227 30075610195084871174859341)
            ·
              refine ⟨11278353823156826690572253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30075610195084871174859341 11278353823156826690572253)
              ·
                refine ⟨4229382683683810008964595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11278353823156826690572253 4229382683683810008964595)
                ·
                  refine ⟨6344074025525715013446893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229382683683810008964595 6344074025525715013446893)
                  ·
                    refine ⟨2379027759572143130042585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6344074025525715013446893 2379027759572143130042585)
                    ·
                      refine ⟨1784270819679107347531939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379027759572143130042585 1784270819679107347531939)
                      ·
                        rfl

theorem cell23_3474855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_3474855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474855 prefixEnd_3474855 := by exact prefixLift 3474855
  have htrace : WordTrace (prefixWord ++ tailWord_3474855) baseStart_3474855 baseEnd_3474855 := by
    simpa [prefixWord, tailWord_3474855, baseEnd_3474855] using wordTrace_append hprefix tailTrace_3474855
  have hstable : (prefixWord ++ tailWord_3474855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474855).length < 2 ^ (prefixWord ++ tailWord_3474855).sum := by decide
  have hdescent : baseEnd_3474855 < baseStart_3474855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474902 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3474902 : Nat := 118140960795 + 3474902 * 2 ^ 59
def prefixEnd_3474902 : Nat := 4983230072969 + 3 ^ 40 * 3474902 * 2
def baseEnd_3474902 : Nat := 1784294953269868663644223

theorem tailTrace_3474902 : CollatzResearch.WordTrace tailWord_3474902 prefixEnd_3474902 1784294953269868663644223 := by
  unfold tailWord_3474902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921255503564437178654185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84493392038020663238977973 7921255503564437178654185)
  ·
    refine ⟨5940941627673327883990639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7921255503564437178654185 5940941627673327883990639)
    ·
      refine ⟨8911412441509991825985959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940941627673327883990639 8911412441509991825985959)
      ·
        refine ⟨13367118662264987738978939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8911412441509991825985959 13367118662264987738978939)
        ·
          refine ⟨20050677993397481608468409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13367118662264987738978939 20050677993397481608468409)
          ·
            refine ⟨15038008495048111206351307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20050677993397481608468409 15038008495048111206351307)
            ·
              refine ⟨22557012742572166809526961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15038008495048111206351307 22557012742572166809526961)
              ·
                refine ⟨16917759556929125107145221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22557012742572166809526961 16917759556929125107145221)
                ·
                  refine ⟨3172079916924210957589729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16917759556929125107145221 3172079916924210957589729)
                  ·
                    refine ⟨2379059937693158218192297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3172079916924210957589729 2379059937693158218192297)
                    ·
                      refine ⟨1784294953269868663644223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379059937693158218192297 1784294953269868663644223)
                      ·
                        rfl

theorem cell23_3474902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3474902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474902 prefixEnd_3474902 := by exact prefixLift 3474902
  have htrace : WordTrace (prefixWord ++ tailWord_3474902) baseStart_3474902 baseEnd_3474902 := by
    simpa [prefixWord, tailWord_3474902, baseEnd_3474902] using wordTrace_append hprefix tailTrace_3474902
  have hstable : (prefixWord ++ tailWord_3474902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474902).length < 2 ^ (prefixWord ++ tailWord_3474902).sum := by decide
  have hdescent : baseEnd_3474902 < baseStart_3474902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474925 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 7]
def baseStart_3474925 : Nat := 118140960795 + 3474925 * 2 ^ 59
def prefixEnd_3474925 : Nat := 4983230072969 + 3 ^ 40 * 3474925 * 2
def baseEnd_3474925 : Nat := 198256307036102452628513

theorem tailTrace_3474925 : CollatzResearch.WordTrace tailWord_3474925 prefixEnd_3474925 198256307036102452628513 := by
  unfold tailWord_3474925
  simp only [CollatzResearch.WordTrace]
  refine ⟨126740926935947669786554229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84493951290631779857702819 126740926935947669786554229)
  ·
    refine ⟨11881961900245094042489459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126740926935947669786554229 11881961900245094042489459)
    ·
      refine ⟨17822942850367641063734189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11881961900245094042489459 17822942850367641063734189)
      ·
        refine ⟨6683603568887865398900321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17822942850367641063734189 6683603568887865398900321)
        ·
          refine ⟨5012702676665899049175241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6683603568887865398900321 5012702676665899049175241)
          ·
            refine ⟨3759527007499424286881431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5012702676665899049175241 3759527007499424286881431)
            ·
              refine ⟨5639290511249136430322147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759527007499424286881431 5639290511249136430322147)
              ·
                refine ⟨8458935766873704645483221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639290511249136430322147 8458935766873704645483221)
                ·
                  refine ⟨198256307036102452628513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8458935766873704645483221 198256307036102452628513)
                  ·
                    rfl

theorem cell23_3474925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_3474925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3474925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3474925 prefixEnd_3474925 := by exact prefixLift 3474925
  have htrace : WordTrace (prefixWord ++ tailWord_3474925) baseStart_3474925 baseEnd_3474925 := by
    simpa [prefixWord, tailWord_3474925, baseEnd_3474925] using wordTrace_append hprefix tailTrace_3474925
  have hstable : (prefixWord ++ tailWord_3474925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474925).length < 2 ^ (prefixWord ++ tailWord_3474925).sum := by decide
  have hdescent : baseEnd_3474925 < baseStart_3474925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475062 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_3475062 : Nat := 118140960795 + 3475062 * 2 ^ 59
def prefixEnd_3475062 : Nat := 4983230072969 + 3 ^ 40 * 3475062 * 2
def baseEnd_3475062 : Nat := 594792370058196012547829

theorem tailTrace_3475062 : CollatzResearch.WordTrace tailWord_3475062 prefixEnd_3475062 594792370058196012547829 := by
  unfold tailWord_3475062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921620233528208886518215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84497282490967561456194293 7921620233528208886518215)
  ·
    refine ⟨11882430350292313329777323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7921620233528208886518215 11882430350292313329777323)
    ·
      refine ⟨17823645525438469994665985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11882430350292313329777323 17823645525438469994665985)
      ·
        refine ⟨13367734144078852495999489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17823645525438469994665985 13367734144078852495999489)
        ·
          refine ⟨10025800608059139371999617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13367734144078852495999489 10025800608059139371999617)
          ·
            refine ⟨7519350456044354528999713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10025800608059139371999617 7519350456044354528999713)
            ·
              refine ⟨5639512842033265896749785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7519350456044354528999713 5639512842033265896749785)
              ·
                refine ⟨4229634631524949422562339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5639512842033265896749785 4229634631524949422562339)
                ·
                  refine ⟨6344451947287424133843509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229634631524949422562339 6344451947287424133843509)
                  ·
                    refine ⟨594792370058196012547829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6344451947287424133843509 594792370058196012547829)
                    ·
                      rfl

theorem cell23_3475062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_3475062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475062 prefixEnd_3475062 := by exact prefixLift 3475062
  have htrace : WordTrace (prefixWord ++ tailWord_3475062) baseStart_3475062 baseEnd_3475062 := by
    simpa [prefixWord, tailWord_3475062, baseEnd_3475062] using wordTrace_append hprefix tailTrace_3475062
  have hstable : (prefixWord ++ tailWord_3475062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475062).length < 2 ^ (prefixWord ++ tailWord_3475062).sum := by decide
  have hdescent : baseEnd_3475062 < baseStart_3475062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475065 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3475065 : Nat := 118140960795 + 3475065 * 2 ^ 59
def prefixEnd_3475065 : Nat := 4983230072969 + 3 ^ 40 * 3475065 * 2
def baseEnd_3475065 : Nat := 1784378650616551525905973

theorem tailTrace_3475065 : CollatzResearch.WordTrace tailWord_3475065 prefixEnd_3475065 1784378650616551525905973 := by
  unfold tailWord_3475065
  simp only [CollatzResearch.WordTrace]
  refine ⟨126746033155440473696650649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84497355436960315797767099 126746033155440473696650649)
  ·
    refine ⟨95059524866580355272487987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126746033155440473696650649 95059524866580355272487987)
    ·
      refine ⟨142589287299870532908731981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95059524866580355272487987 142589287299870532908731981)
      ·
        refine ⟨53470982737451449840774493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142589287299870532908731981 53470982737451449840774493)
        ·
          refine ⟨20051618526544293690290435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53470982737451449840774493 20051618526544293690290435)
          ·
            refine ⟨30077427789816440535435653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20051618526544293690290435 30077427789816440535435653)
            ·
              refine ⟨5639517710590582600394185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30077427789816440535435653 5639517710590582600394185)
              ·
                refine ⟨4229638282942936950295639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5639517710590582600394185 4229638282942936950295639)
                ·
                  refine ⟨6344457424414405425443459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229638282942936950295639 6344457424414405425443459)
                  ·
                    refine ⟨9516686136621608138165189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6344457424414405425443459 9516686136621608138165189)
                    ·
                      refine ⟨1784378650616551525905973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9516686136621608138165189 1784378650616551525905973)
                      ·
                        rfl

theorem cell23_3475065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3475065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475065 prefixEnd_3475065 := by exact prefixLift 3475065
  have htrace : WordTrace (prefixWord ++ tailWord_3475065) baseStart_3475065 baseEnd_3475065 := by
    simpa [prefixWord, tailWord_3475065, baseEnd_3475065] using wordTrace_append hprefix tailTrace_3475065
  have hstable : (prefixWord ++ tailWord_3475065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475065).length < 2 ^ (prefixWord ++ tailWord_3475065).sum := by decide
  have hdescent : baseEnd_3475065 < baseStart_3475065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475076 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_3475076 : Nat := 118140960795 + 3475076 * 2 ^ 59
def prefixEnd_3475076 : Nat := 4983230072969 + 3 ^ 40 * 3475076 * 2
def baseEnd_3475076 : Nat := 1784384298903750982868423

theorem tailTrace_3475076 : CollatzResearch.WordTrace tailWord_3475076 prefixEnd_3475076 1784384298903750982868423 := by
  unfold tailWord_3475076
  simp only [CollatzResearch.WordTrace]
  refine ⟨63373217179200311287650541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84497622905600415050200721 63373217179200311287650541)
  ·
    refine ⟨23764956442200116732868953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63373217179200311287650541 23764956442200116732868953)
    ·
      refine ⟨17823717331650087549651715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23764956442200116732868953 17823717331650087549651715)
      ·
        refine ⟨26735575997475131324477573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17823717331650087549651715 26735575997475131324477573)
        ·
          refine ⟨5012920499526587123339545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26735575997475131324477573 5012920499526587123339545)
          ·
            refine ⟨3759690374644940342504659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5012920499526587123339545 3759690374644940342504659)
            ·
              refine ⟨5639535561967410513756989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759690374644940342504659 5639535561967410513756989)
              ·
                refine ⟨2114825835737778942658871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5639535561967410513756989 2114825835737778942658871)
                ·
                  refine ⟨3172238753606668413988307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114825835737778942658871 3172238753606668413988307)
                  ·
                    refine ⟨4758358130410002620982461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3172238753606668413988307 4758358130410002620982461)
                    ·
                      refine ⟨1784384298903750982868423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4758358130410002620982461 1784384298903750982868423)
                      ·
                        rfl

theorem cell23_3475076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_3475076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475076 prefixEnd_3475076 := by exact prefixLift 3475076
  have htrace : WordTrace (prefixWord ++ tailWord_3475076) baseStart_3475076 baseEnd_3475076 := by
    simpa [prefixWord, tailWord_3475076, baseEnd_3475076] using wordTrace_append hprefix tailTrace_3475076
  have hstable : (prefixWord ++ tailWord_3475076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475076).length < 2 ^ (prefixWord ++ tailWord_3475076).sum := by decide
  have hdescent : baseEnd_3475076 < baseStart_3475076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475091 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_3475091 : Nat := 118140960795 + 3475091 * 2 ^ 59
def prefixEnd_3475091 : Nat := 4983230072969 + 3 ^ 40 * 3475091 * 2
def baseEnd_3475091 : Nat := 1784392001113568424180853

theorem tailTrace_3475091 : CollatzResearch.WordTrace tailWord_3475091 prefixEnd_3475091 1784392001113568424180853 := by
  unfold tailWord_3475091
  simp only [CollatzResearch.WordTrace]
  refine ⟨126746981453346280137097127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84497987635564186758064751 126746981453346280137097127)
  ·
    refine ⟨190120472180019420205645691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126746981453346280137097127 190120472180019420205645691)
    ·
      refine ⟨285180708270029130308468537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190120472180019420205645691 285180708270029130308468537)
      ·
        refine ⟨213885531202521847731351403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285180708270029130308468537 213885531202521847731351403)
        ·
          refine ⟨320828296803782771597027105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213885531202521847731351403 320828296803782771597027105)
          ·
            refine ⟨240621222602837078697770329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320828296803782771597027105 240621222602837078697770329)
            ·
              refine ⟨180465916952127809023327747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240621222602837078697770329 180465916952127809023327747)
              ·
                refine ⟨270698875428191713534991621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180465916952127809023327747 270698875428191713534991621)
                ·
                  refine ⟨50756039142785946287810929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270698875428191713534991621 50756039142785946287810929)
                  ·
                    refine ⟨38067029357089459715858197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50756039142785946287810929 38067029357089459715858197)
                    ·
                      refine ⟨1784392001113568424180853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38067029357089459715858197 1784392001113568424180853)
                      ·
                        rfl

theorem cell23_3475091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_3475091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475091 prefixEnd_3475091 := by exact prefixLift 3475091
  have htrace : WordTrace (prefixWord ++ tailWord_3475091) baseStart_3475091 baseEnd_3475091 := by
    simpa [prefixWord, tailWord_3475091, baseEnd_3475091] using wordTrace_append hprefix tailTrace_3475091
  have hstable : (prefixWord ++ tailWord_3475091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475091).length < 2 ^ (prefixWord ++ tailWord_3475091).sum := by decide
  have hdescent : baseEnd_3475091 < baseStart_3475091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475168 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_3475168 : Nat := 118140960795 + 3475168 * 2 ^ 59
def prefixEnd_3475168 : Nat := 4983230072969 + 3 ^ 40 * 3475168 * 2
def baseEnd_3475168 : Nat := 1784431539123964622917999

theorem tailTrace_3475168 : CollatzResearch.WordTrace tailWord_3475168 prefixEnd_3475168 1784431539123964622917999 := by
  unfold tailWord_3475168
  simp only [CollatzResearch.WordTrace]
  refine ⟨63374894937033661143825079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84499859916044881525100105 63374894937033661143825079)
  ·
    refine ⟨95062342405550491715737619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63374894937033661143825079 95062342405550491715737619)
    ·
      refine ⟨142593513608325737573606429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95062342405550491715737619 142593513608325737573606429)
      ·
        refine ⟨53472567603122151590102411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142593513608325737573606429 53472567603122151590102411)
        ·
          refine ⟨80208851404683227385153617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53472567603122151590102411 80208851404683227385153617)
          ·
            refine ⟨60156638553512420538865213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80208851404683227385153617 60156638553512420538865213)
            ·
              refine ⟨22558739457567157702074455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60156638553512420538865213 22558739457567157702074455)
              ·
                refine ⟨33838109186350736553111683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22558739457567157702074455 33838109186350736553111683)
                ·
                  refine ⟨50757163779526104829667525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33838109186350736553111683 50757163779526104829667525)
                  ·
                    refine ⟨9516968208661144655562661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50757163779526104829667525 9516968208661144655562661)
                    ·
                      refine ⟨1784431539123964622917999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9516968208661144655562661 1784431539123964622917999)
                      ·
                        rfl

theorem cell23_3475168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_3475168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475168 prefixEnd_3475168 := by exact prefixLift 3475168
  have htrace : WordTrace (prefixWord ++ tailWord_3475168) baseStart_3475168 baseEnd_3475168 := by
    simpa [prefixWord, tailWord_3475168, baseEnd_3475168] using wordTrace_append hprefix tailTrace_3475168
  have hstable : (prefixWord ++ tailWord_3475168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475168).length < 2 ^ (prefixWord ++ tailWord_3475168).sum := by decide
  have hdescent : baseEnd_3475168 < baseStart_3475168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475172 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_3475172 : Nat := 118140960795 + 3475172 * 2 ^ 59
def prefixEnd_3475172 : Nat := 4983230072969 + 3 ^ 40 * 3475172 * 2
def baseEnd_3475172 : Nat := 1784433593046582607267981

theorem tailTrace_3475172 : CollatzResearch.WordTrace tailWord_3475172 prefixEnd_3475172 1784433593046582607267981 := by
  unfold tailWord_3475172
  simp only [CollatzResearch.WordTrace]
  refine ⟨63374967883026415485397885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84499957177368553980530513 63374967883026415485397885)
  ·
    refine ⟨23765612956134905807024207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63374967883026415485397885 23765612956134905807024207)
    ·
      refine ⟨35648419434202358710536311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23765612956134905807024207 35648419434202358710536311)
      ·
        refine ⟨53472629151303538065804467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35648419434202358710536311 53472629151303538065804467)
        ·
          refine ⟨80208943726955307098706701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53472629151303538065804467 80208943726955307098706701)
          ·
            refine ⟨30078353897608240162015013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80208943726955307098706701 30078353897608240162015013)
            ·
              refine ⟨5639691355801545030377815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30078353897608240162015013 5639691355801545030377815)
              ·
                refine ⟨8459537033702317545566723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639691355801545030377815 8459537033702317545566723)
                ·
                  refine ⟨12689305550553476318350085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459537033702317545566723 12689305550553476318350085)
                  ·
                    refine ⟨2379244790728776809690641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12689305550553476318350085 2379244790728776809690641)
                    ·
                      refine ⟨1784433593046582607267981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379244790728776809690641 1784433593046582607267981)
                      ·
                        rfl

theorem cell23_3475172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_3475172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475172 prefixEnd_3475172 := by exact prefixLift 3475172
  have htrace : WordTrace (prefixWord ++ tailWord_3475172) baseStart_3475172 baseEnd_3475172 := by
    simpa [prefixWord, tailWord_3475172, baseEnd_3475172] using wordTrace_append hprefix tailTrace_3475172
  have hstable : (prefixWord ++ tailWord_3475172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475172).length < 2 ^ (prefixWord ++ tailWord_3475172).sum := by decide
  have hdescent : baseEnd_3475172 < baseStart_3475172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475178 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_3475178 : Nat := 118140960795 + 3475178 * 2 ^ 59
def prefixEnd_3475178 : Nat := 4983230072969 + 3 ^ 40 * 3475178 * 2
def baseEnd_3475178 : Nat := 198270741547834398199217

theorem tailTrace_3475178 : CollatzResearch.WordTrace tailWord_3475178 prefixEnd_3475178 198270741547834398199217 := by
  unfold tailWord_3475178
  simp only [CollatzResearch.WordTrace]
  refine ⟨31687538651007773498878547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84500103069354062663676125 31687538651007773498878547)
  ·
    refine ⟨47531307976511660248317821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31687538651007773498878547 47531307976511660248317821)
    ·
      refine ⟨17824240491191872593119183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47531307976511660248317821 17824240491191872593119183)
      ·
        refine ⟨26736360736787808889678775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17824240491191872593119183 26736360736787808889678775)
        ·
          refine ⟨40104541105181713334518163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26736360736787808889678775 40104541105181713334518163)
          ·
            refine ⟨60156811657772570001777245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40104541105181713334518163 60156811657772570001777245)
            ·
              refine ⟨22558804371664713750666467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60156811657772570001777245 22558804371664713750666467)
              ·
                refine ⟨33838206557497070625999701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22558804371664713750666467 33838206557497070625999701)
                ·
                  refine ⟨198270741547834398199217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33838206557497070625999701 198270741547834398199217)
                  ·
                    rfl

theorem cell23_3475178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_3475178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475178 prefixEnd_3475178 := by exact prefixLift 3475178
  have htrace : WordTrace (prefixWord ++ tailWord_3475178) baseStart_3475178 baseEnd_3475178 := by
    simpa [prefixWord, tailWord_3475178, baseEnd_3475178] using wordTrace_append hprefix tailTrace_3475178
  have hstable : (prefixWord ++ tailWord_3475178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475178).length < 2 ^ (prefixWord ++ tailWord_3475178).sum := by decide
  have hdescent : baseEnd_3475178 < baseStart_3475178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475215 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 2, 5, 2]
def baseStart_3475215 : Nat := 118140960795 + 3475215 * 2 ^ 59
def prefixEnd_3475215 : Nat := 4983230072969 + 3 ^ 40 * 3475215 * 2
def baseEnd_3475215 : Nat := 1784455672714725939030283

theorem tailTrace_3475215 : CollatzResearch.WordTrace tailWord_3475215 prefixEnd_3475215 1784455672714725939030283 := by
  unfold tailWord_3475215
  simp only [CollatzResearch.WordTrace]
  refine ⟨126751504104897049314611099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84501002736598032876407399 126751504104897049314611099)
  ·
    refine ⟨190127256157345573971916649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126751504104897049314611099 190127256157345573971916649)
    ·
      refine ⟨142595442118009180478937487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190127256157345573971916649 142595442118009180478937487)
      ·
        refine ⟨213893163177013770718406231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142595442118009180478937487 213893163177013770718406231)
        ·
          refine ⟨320839744765520656077609347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213893163177013770718406231 320839744765520656077609347)
          ·
            refine ⟨481259617148280984116414021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320839744765520656077609347 481259617148280984116414021)
            ·
              refine ⟨90236178215302684521827629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 481259617148280984116414021 90236178215302684521827629)
              ·
                refine ⟨33838566830738506695685361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90236178215302684521827629 33838566830738506695685361)
                ·
                  refine ⟨25378925123053880021764021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33838566830738506695685361 25378925123053880021764021)
                  ·
                    refine ⟨2379274230286301252040377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25378925123053880021764021 2379274230286301252040377)
                    ·
                      refine ⟨1784455672714725939030283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379274230286301252040377 1784455672714725939030283)
                      ·
                        rfl

theorem cell23_3475215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5, 2].length) (baseStart_3475215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475215 prefixEnd_3475215 := by exact prefixLift 3475215
  have htrace : WordTrace (prefixWord ++ tailWord_3475215) baseStart_3475215 baseEnd_3475215 := by
    simpa [prefixWord, tailWord_3475215, baseEnd_3475215] using wordTrace_append hprefix tailTrace_3475215
  have hstable : (prefixWord ++ tailWord_3475215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475215).length < 2 ^ (prefixWord ++ tailWord_3475215).sum := by decide
  have hdescent : baseEnd_3475215 < baseStart_3475215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475246 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_3475246 : Nat := 118140960795 + 3475246 * 2 ^ 59
def prefixEnd_3475246 : Nat := 4983230072969 + 3 ^ 40 * 3475246 * 2
def baseEnd_3475246 : Nat := 198274621179446146415849

theorem tailTrace_3475246 : CollatzResearch.WordTrace tailWord_3475246 prefixEnd_3475246 198274621179446146415849 := by
  unfold tailWord_3475246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844079345973092701123699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84501756511856494405993061 15844079345973092701123699)
  ·
    refine ⟨23766119018959639051685549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15844079345973092701123699 23766119018959639051685549)
    ·
      refine ⟨8912294632109864644382081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23766119018959639051685549 8912294632109864644382081)
      ·
        refine ⟨6684220974082398483286561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912294632109864644382081 6684220974082398483286561)
        ·
          refine ⟨5013165730561798862464921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6684220974082398483286561 5013165730561798862464921)
          ·
            refine ⟨3759874297921349146848691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5013165730561798862464921 3759874297921349146848691)
            ·
              refine ⟨5639811446882023720273037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759874297921349146848691 5639811446882023720273037)
              ·
                refine ⟨2114929292580758895102389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5639811446882023720273037 2114929292580758895102389)
                ·
                  refine ⟨198274621179446146415849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2114929292580758895102389 198274621179446146415849)
                  ·
                    rfl

theorem cell23_3475246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_3475246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475246 prefixEnd_3475246 := by exact prefixLift 3475246
  have htrace : WordTrace (prefixWord ++ tailWord_3475246) baseStart_3475246 baseEnd_3475246 := by
    simpa [prefixWord, tailWord_3475246, baseEnd_3475246] using wordTrace_append hprefix tailTrace_3475246
  have hstable : (prefixWord ++ tailWord_3475246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475246).length < 2 ^ (prefixWord ++ tailWord_3475246).sum := by decide
  have hdescent : baseEnd_3475246 < baseStart_3475246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475248 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_3475248 : Nat := 118140960795 + 3475248 * 2 ^ 59
def prefixEnd_3475248 : Nat := 4983230072969 + 3 ^ 40 * 3475248 * 2
def baseEnd_3475248 : Nat := 1784472617576324309917631

theorem tailTrace_3475248 : CollatzResearch.WordTrace tailWord_3475248 prefixEnd_3475248 1784472617576324309917631 := by
  unfold tailWord_3475248
  simp only [CollatzResearch.WordTrace]
  refine ⟨63376353856888747975281199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84501805142518330633708265 63376353856888747975281199)
  ·
    refine ⟨95064530785333121962921799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63376353856888747975281199 95064530785333121962921799)
    ·
      refine ⟨142596796177999682944382699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95064530785333121962921799 142596796177999682944382699)
      ·
        refine ⟨213895194266999524416574049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142596796177999682944382699 213895194266999524416574049)
        ·
          refine ⟨160421395700249643312430537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213895194266999524416574049 160421395700249643312430537)
          ·
            refine ⟨120316046775187232484322903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160421395700249643312430537 120316046775187232484322903)
            ·
              refine ⟨180474070162780848726484355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120316046775187232484322903 180474070162780848726484355)
              ·
                refine ⟨270711105244171273089726533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180474070162780848726484355 270711105244171273089726533)
                ·
                  refine ⟨50758332233282113704323725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270711105244171273089726533 50758332233282113704323725)
                  ·
                    refine ⟨19034374587480792639121397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50758332233282113704323725 19034374587480792639121397)
                    ·
                      refine ⟨1784472617576324309917631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19034374587480792639121397 1784472617576324309917631)
                      ·
                        rfl

theorem cell23_3475248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_3475248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475248 prefixEnd_3475248 := by exact prefixLift 3475248
  have htrace : WordTrace (prefixWord ++ tailWord_3475248) baseStart_3475248 baseEnd_3475248 := by
    simpa [prefixWord, tailWord_3475248, baseEnd_3475248] using wordTrace_append hprefix tailTrace_3475248
  have hstable : (prefixWord ++ tailWord_3475248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475248).length < 2 ^ (prefixWord ++ tailWord_3475248).sum := by decide
  have hdescent : baseEnd_3475248 < baseStart_3475248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475262 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3475262 : Nat := 118140960795 + 3475262 * 2 ^ 59
def prefixEnd_3475262 : Nat := 4983230072969 + 3 ^ 40 * 3475262 * 2
def baseEnd_3475262 : Nat := 1784479806305487255142567

theorem tailTrace_3475262 : CollatzResearch.WordTrace tailWord_3475262 prefixEnd_3475262 1784479806305487255142567 := by
  unfold tailWord_3475262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844152291965847042696505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84502145557151184227714693 15844152291965847042696505)
  ·
    refine ⟨11883114218974385282022379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15844152291965847042696505 11883114218974385282022379)
    ·
      refine ⟨17824671328461577923033569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11883114218974385282022379 17824671328461577923033569)
      ·
        refine ⟨13368503496346183442275177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17824671328461577923033569 13368503496346183442275177)
        ·
          refine ⟨10026377622259637581706383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13368503496346183442275177 10026377622259637581706383)
          ·
            refine ⟨15039566433389456372559575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026377622259637581706383 15039566433389456372559575)
            ·
              refine ⟨22559349650084184558839363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15039566433389456372559575 22559349650084184558839363)
              ·
                refine ⟨33839024475126276838259045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22559349650084184558839363 33839024475126276838259045)
                ·
                  refine ⟨6344817089086176907173571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33839024475126276838259045 6344817089086176907173571)
                  ·
                    refine ⟨9517225633629265360760357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6344817089086176907173571 9517225633629265360760357)
                    ·
                      refine ⟨1784479806305487255142567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9517225633629265360760357 1784479806305487255142567)
                      ·
                        rfl

theorem cell23_3475262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3475262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475262 prefixEnd_3475262 := by exact prefixLift 3475262
  have htrace : WordTrace (prefixWord ++ tailWord_3475262) baseStart_3475262 baseEnd_3475262 := by
    simpa [prefixWord, tailWord_3475262, baseEnd_3475262] using wordTrace_append hprefix tailTrace_3475262
  have hstable : (prefixWord ++ tailWord_3475262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475262).length < 2 ^ (prefixWord ++ tailWord_3475262).sum := by decide
  have hdescent : baseEnd_3475262 < baseStart_3475262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475272 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 3, 4]
def baseStart_3475272 : Nat := 118140960795 + 3475272 * 2 ^ 59
def prefixEnd_3475272 : Nat := 4983230072969 + 3 ^ 40 * 3475272 * 2
def baseEnd_3475272 : Nat := 594828313704010738672507

theorem tailTrace_3475272 : CollatzResearch.WordTrace tailWord_3475272 prefixEnd_3475272 594828313704010738672507 := by
  unfold tailWord_3475272
  simp only [CollatzResearch.WordTrace]
  refine ⟨63376791532845274024718035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84502388710460365366290713 63376791532845274024718035)
  ·
    refine ⟨95065187299267911037077053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63376791532845274024718035 95065187299267911037077053)
    ·
      refine ⟨35649445237225466638903895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95065187299267911037077053 35649445237225466638903895)
      ·
        refine ⟨53474167855838199958355843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35649445237225466638903895 53474167855838199958355843)
        ·
          refine ⟨80211251783757299937533765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53474167855838199958355843 80211251783757299937533765)
          ·
            refine ⟨15039609709454493738287581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80211251783757299937533765 15039609709454493738287581)
            ·
              refine ⟨5639853641045435151857843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15039609709454493738287581 5639853641045435151857843)
              ·
                refine ⟨8459780461568152727786765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639853641045435151857843 8459780461568152727786765)
                ·
                  refine ⟨3172417673088057272920037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8459780461568152727786765 3172417673088057272920037)
                  ·
                    refine ⟨594828313704010738672507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3172417673088057272920037 594828313704010738672507)
                    ·
                      rfl

theorem cell23_3475272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_3475272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475272 prefixEnd_3475272 := by exact prefixLift 3475272
  have htrace : WordTrace (prefixWord ++ tailWord_3475272) baseStart_3475272 baseEnd_3475272 := by
    simpa [prefixWord, tailWord_3475272, baseEnd_3475272] using wordTrace_append hprefix tailTrace_3475272
  have hstable : (prefixWord ++ tailWord_3475272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475272).length < 2 ^ (prefixWord ++ tailWord_3475272).sum := by decide
  have hdescent : baseEnd_3475272 < baseStart_3475272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475299 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 3]
def baseStart_3475299 : Nat := 118140960795 + 3475299 * 2 ^ 59
def prefixEnd_3475299 : Nat := 4983230072969 + 3 ^ 40 * 3475299 * 2
def baseEnd_3475299 : Nat := 1784498805089703610379897

theorem tailTrace_3475299 : CollatzResearch.WordTrace tailWord_3475299 prefixEnd_3475299 1784498805089703610379897 := by
  unfold tailWord_3475299
  simp only [CollatzResearch.WordTrace]
  refine ⟨126754567836592731660668951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84503045224395154440445967 126754567836592731660668951)
  ·
    refine ⟨190131851754889097491003427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126754567836592731660668951 190131851754889097491003427)
    ·
      refine ⟨285197777632333646236505141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190131851754889097491003427 285197777632333646236505141)
      ·
        refine ⟨26737291653031279334672357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285197777632333646236505141 26737291653031279334672357)
        ·
          refine ⟨5013242184943364875251067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26737291653031279334672357 5013242184943364875251067)
          ·
            refine ⟨7519863277415047312876601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013242184943364875251067 7519863277415047312876601)
            ·
              refine ⟨5639897458061285484657451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7519863277415047312876601 5639897458061285484657451)
              ·
                refine ⟨8459846187091928226986177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639897458061285484657451 8459846187091928226986177)
                ·
                  refine ⟨6344884640318946170239633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8459846187091928226986177 6344884640318946170239633)
                  ·
                    refine ⟨4758663480239209627679725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6344884640318946170239633 4758663480239209627679725)
                    ·
                      refine ⟨1784498805089703610379897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4758663480239209627679725 1784498805089703610379897)
                      ·
                        rfl

theorem cell23_3475299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_3475299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475299 prefixEnd_3475299 := by exact prefixLift 3475299
  have htrace : WordTrace (prefixWord ++ tailWord_3475299) baseStart_3475299 baseEnd_3475299 := by
    simpa [prefixWord, tailWord_3475299, baseEnd_3475299] using wordTrace_append hprefix tailTrace_3475299
  have hstable : (prefixWord ++ tailWord_3475299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475299).length < 2 ^ (prefixWord ++ tailWord_3475299).sum := by decide
  have hdescent : baseEnd_3475299 < baseStart_3475299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475345 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_3475345 : Nat := 118140960795 + 3475345 * 2 ^ 59
def prefixEnd_3475345 : Nat := 4983230072969 + 3 ^ 40 * 3475345 * 2
def baseEnd_3475345 : Nat := 594840808399936810134895

theorem tailTrace_3475345 : CollatzResearch.WordTrace tailWord_3475345 prefixEnd_3475345 594840808399936810134895 := by
  unfold tailWord_3475345
  simp only [CollatzResearch.WordTrace]
  refine ⟨126756245594426081516843489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84504163729617387677895659 126756245594426081516843489)
  ·
    refine ⟨95067184195819561137632617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126756245594426081516843489 95067184195819561137632617)
    ·
      refine ⟨71300388146864670853224463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95067184195819561137632617 71300388146864670853224463)
      ·
        refine ⟨106950582220297006279836695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71300388146864670853224463 106950582220297006279836695)
        ·
          refine ⟨160425873330445509419755043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106950582220297006279836695 160425873330445509419755043)
          ·
            refine ⟨240638809995668264129632565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160425873330445509419755043 240638809995668264129632565)
            ·
              refine ⟨22559888437093899762153053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240638809995668264129632565 22559888437093899762153053)
              ·
                refine ⟨8459958163910212410807395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22559888437093899762153053 8459958163910212410807395)
                ·
                  refine ⟨12689937245865318616211093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459958163910212410807395 12689937245865318616211093)
                  ·
                    refine ⟨594840808399936810134895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12689937245865318616211093 594840808399936810134895)
                    ·
                      rfl

theorem cell23_3475345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_3475345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475345 prefixEnd_3475345 := by exact prefixLift 3475345
  have htrace : WordTrace (prefixWord ++ tailWord_3475345) baseStart_3475345 baseEnd_3475345 := by
    simpa [prefixWord, tailWord_3475345, baseEnd_3475345] using wordTrace_append hprefix tailTrace_3475345
  have hstable : (prefixWord ++ tailWord_3475345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475345).length < 2 ^ (prefixWord ++ tailWord_3475345).sum := by decide
  have hdescent : baseEnd_3475345 < baseStart_3475345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475346 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3475346 : Nat := 118140960795 + 3475346 * 2 ^ 59
def prefixEnd_3475346 : Nat := 4983230072969 + 3 ^ 40 * 3475346 * 2
def baseEnd_3475346 : Nat := 1784522938680464926492181

theorem tailTrace_3475346 : CollatzResearch.WordTrace tailWord_3475346 prefixEnd_3475346 1784522938680464926492181 := by
  unfold tailWord_3475346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31689070516855614671907473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84504188044948305791753261 31689070516855614671907473)
  ·
    refine ⟨23766802887641711003930605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31689070516855614671907473 23766802887641711003930605)
    ·
      refine ⟨8912551082865641626473977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23766802887641711003930605 8912551082865641626473977)
      ·
        refine ⟨6684413312149231219855483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912551082865641626473977 6684413312149231219855483)
        ·
          refine ⟨10026619968223846829783225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684413312149231219855483 10026619968223846829783225)
          ·
            refine ⟨7519964976167885122337419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10026619968223846829783225 7519964976167885122337419)
            ·
              refine ⟨11279947464251827683506129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7519964976167885122337419 11279947464251827683506129)
              ·
                refine ⟨8459960598188870762629597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11279947464251827683506129 8459960598188870762629597)
                ·
                  refine ⟨3172485224320826535986099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8459960598188870762629597 3172485224320826535986099)
                  ·
                    refine ⟨4758727836481239803979149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3172485224320826535986099 4758727836481239803979149)
                    ·
                      refine ⟨1784522938680464926492181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4758727836481239803979149 1784522938680464926492181)
                      ·
                        rfl

theorem cell23_3475346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3475346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475346 prefixEnd_3475346 := by exact prefixLift 3475346
  have htrace : WordTrace (prefixWord ++ tailWord_3475346) baseStart_3475346 baseEnd_3475346 := by
    simpa [prefixWord, tailWord_3475346, baseEnd_3475346] using wordTrace_append hprefix tailTrace_3475346
  have hstable : (prefixWord ++ tailWord_3475346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475346).length < 2 ^ (prefixWord ++ tailWord_3475346).sum := by decide
  have hdescent : baseEnd_3475346 < baseStart_3475346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475350 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3475350 : Nat := 118140960795 + 3475350 * 2 ^ 59
def prefixEnd_3475350 : Nat := 4983230072969 + 3 ^ 40 * 3475350 * 2
def baseEnd_3475350 : Nat := 1784524992603082910842163

theorem tailTrace_3475350 : CollatzResearch.WordTrace tailWord_3475350 prefixEnd_3475350 1784524992603082910842163 := by
  unfold tailWord_3475350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7922276747462997960673469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84504285306271978247183669 7922276747462997960673469)
  ·
    refine ⟨2970853780298624235252551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7922276747462997960673469 2970853780298624235252551)
    ·
      refine ⟨4456280670447936352878827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970853780298624235252551 4456280670447936352878827)
      ·
        refine ⟨6684421005671904529318241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456280670447936352878827 6684421005671904529318241)
        ·
          refine ⟨5013315754253928396988681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6684421005671904529318241 5013315754253928396988681)
          ·
            refine ⟨3759986815690446297741511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5013315754253928396988681 3759986815690446297741511)
            ·
              refine ⟨5639980223535669446612267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759986815690446297741511 5639980223535669446612267)
              ·
                refine ⟨8459970335303504169918401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639980223535669446612267 8459970335303504169918401)
                ·
                  refine ⟨6344977751477628127438801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8459970335303504169918401 6344977751477628127438801)
                  ·
                    refine ⟨4758733313608221095579101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6344977751477628127438801 4758733313608221095579101)
                    ·
                      refine ⟨1784524992603082910842163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4758733313608221095579101 1784524992603082910842163)
                      ·
                        rfl

theorem cell23_3475350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3475350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475350 prefixEnd_3475350 := by exact prefixLift 3475350
  have htrace : WordTrace (prefixWord ++ tailWord_3475350) baseStart_3475350 baseEnd_3475350 := by
    simpa [prefixWord, tailWord_3475350, baseEnd_3475350] using wordTrace_append hprefix tailTrace_3475350
  have hstable : (prefixWord ++ tailWord_3475350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475350).length < 2 ^ (prefixWord ++ tailWord_3475350).sum := by decide
  have hdescent : baseEnd_3475350 < baseStart_3475350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475356 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3475356 : Nat := 118140960795 + 3475356 * 2 ^ 59
def prefixEnd_3475356 : Nat := 4983230072969 + 3 ^ 40 * 3475356 * 2
def baseEnd_3475356 : Nat := 1784528073487009887367135

theorem tailTrace_3475356 : CollatzResearch.WordTrace tailWord_3475356 prefixEnd_3475356 1784528073487009887367135 := by
  unfold tailWord_3475356
  simp only [CollatzResearch.WordTrace]
  refine ⟨63378323398693115197746961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84504431198257486930329281 63378323398693115197746961)
  ·
    refine ⟨47533742549019836398310221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63378323398693115197746961 47533742549019836398310221)
    ·
      refine ⟨17825153455882438649366333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47533742549019836398310221 17825153455882438649366333)
      ·
        refine ⟨6684432545955914493512375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17825153455882438649366333 6684432545955914493512375)
        ·
          refine ⟨10026648818933871740268563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684432545955914493512375 10026648818933871740268563)
          ·
            refine ⟨15039973228400807610402845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026648818933871740268563 15039973228400807610402845)
            ·
              refine ⟨5639989960650302853901067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15039973228400807610402845 5639989960650302853901067)
              ·
                refine ⟨8459984940975454280851601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639989960650302853901067 8459984940975454280851601)
                ·
                  refine ⟨6344988705731590710638701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8459984940975454280851601 6344988705731590710638701)
                  ·
                    refine ⟨2379370764649346516489513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6344988705731590710638701 2379370764649346516489513)
                    ·
                      refine ⟨1784528073487009887367135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379370764649346516489513 1784528073487009887367135)
                      ·
                        rfl

theorem cell23_3475356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3475356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475356 prefixEnd_3475356 := by exact prefixLift 3475356
  have htrace : WordTrace (prefixWord ++ tailWord_3475356) baseStart_3475356 baseEnd_3475356 := by
    simpa [prefixWord, tailWord_3475356, baseEnd_3475356] using wordTrace_append hprefix tailTrace_3475356
  have hstable : (prefixWord ++ tailWord_3475356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475356).length < 2 ^ (prefixWord ++ tailWord_3475356).sum := by decide
  have hdescent : baseEnd_3475356 < baseStart_3475356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475415 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_3475415 : Nat := 118140960795 + 3475415 * 2 ^ 59
def prefixEnd_3475415 : Nat := 4983230072969 + 3 ^ 40 * 3475415 * 2
def baseEnd_3475415 : Nat := 1784558368845625156529363

theorem tailTrace_3475415 : CollatzResearch.WordTrace tailWord_3475415 prefixEnd_3475415 1784558368845625156529363 := by
  unfold tailWord_3475415
  simp only [CollatzResearch.WordTrace]
  refine ⟨126758798704172483471891699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84505865802781655647927799 126758798704172483471891699)
  ·
    refine ⟨190138198056258725207837549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126758798704172483471891699 190138198056258725207837549)
    ·
      refine ⟨71301824271097021952939081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190138198056258725207837549 71301824271097021952939081)
      ·
        refine ⟨53476368203322766464704311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71301824271097021952939081 53476368203322766464704311)
        ·
          refine ⟨80214552304984149697056467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53476368203322766464704311 80214552304984149697056467)
          ·
            refine ⟨120321828457476224545584701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80214552304984149697056467 120321828457476224545584701)
            ·
              refine ⟨45120685671553584204594263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120321828457476224545584701 45120685671553584204594263)
              ·
                refine ⟨67681028507330376306891395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45120685671553584204594263 67681028507330376306891395)
                ·
                  refine ⟨101521542760995564460337093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67681028507330376306891395 101521542760995564460337093)
                  ·
                    refine ⟨19035289267686668336313205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101521542760995564460337093 19035289267686668336313205)
                    ·
                      refine ⟨1784558368845625156529363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19035289267686668336313205 1784558368845625156529363)
                      ·
                        rfl

theorem cell23_3475415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_3475415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475415 prefixEnd_3475415 := by exact prefixLift 3475415
  have htrace : WordTrace (prefixWord ++ tailWord_3475415) baseStart_3475415 baseEnd_3475415 := by
    simpa [prefixWord, tailWord_3475415, baseEnd_3475415] using wordTrace_append hprefix tailTrace_3475415
  have hstable : (prefixWord ++ tailWord_3475415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475415).length < 2 ^ (prefixWord ++ tailWord_3475415).sum := by decide
  have hdescent : baseEnd_3475415 < baseStart_3475415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475426 : List Nat := [3, 3, 3, 1, 3, 1, 9]
def baseStart_3475426 : Nat := 118140960795 + 3475426 * 2 ^ 59
def prefixEnd_3475426 : Nat := 4983230072969 + 3 ^ 40 * 3475426 * 2
def baseEnd_3475426 : Nat := 22031654532504007573973

theorem tailTrace_3475426 : CollatzResearch.WordTrace tailWord_3475426 prefixEnd_3475426 22031654532504007573973 := by
  unfold tailWord_3475426
  simp only [CollatzResearch.WordTrace]
  refine ⟨31689799976783158087635533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84506133271421754900361421 31689799976783158087635533)
  ·
    refine ⟨11883674991293684282863325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31689799976783158087635533 11883674991293684282863325)
    ·
      refine ⟨4456378121735131606073747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11883674991293684282863325 4456378121735131606073747)
      ·
        refine ⟨6684567182602697409110621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456378121735131606073747 6684567182602697409110621)
        ·
          refine ⟨2506712693476011528416483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6684567182602697409110621 2506712693476011528416483)
          ·
            refine ⟨3760069040214017292624725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506712693476011528416483 3760069040214017292624725)
            ·
              refine ⟨22031654532504007573973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3760069040214017292624725 22031654532504007573973)
              ·
                rfl

theorem cell23_3475426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 9].length) (baseStart_3475426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475426 prefixEnd_3475426 := by exact prefixLift 3475426
  have htrace : WordTrace (prefixWord ++ tailWord_3475426) baseStart_3475426 baseEnd_3475426 := by
    simpa [prefixWord, tailWord_3475426, baseEnd_3475426] using wordTrace_append hprefix tailTrace_3475426
  have hstable : (prefixWord ++ tailWord_3475426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475426).length < 2 ^ (prefixWord ++ tailWord_3475426).sum := by decide
  have hdescent : baseEnd_3475426 < baseStart_3475426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475435 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 4, 6]
def baseStart_3475435 : Nat := 118140960795 + 3475435 * 2 ^ 59
def prefixEnd_3475435 : Nat := 4983230072969 + 3 ^ 40 * 3475435 * 2
def baseEnd_3475435 : Nat := 594856212819571692759757

theorem tailTrace_3475435 : CollatzResearch.WordTrace tailWord_3475435 prefixEnd_3475435 594856212819571692759757 := by
  unfold tailWord_3475435
  simp only [CollatzResearch.WordTrace]
  refine ⟨126759528164100026887619759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84506352109400017925079839 126759528164100026887619759)
  ·
    refine ⟨190139292246150040331429639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126759528164100026887619759 190139292246150040331429639)
    ·
      refine ⟨285208938369225060497144459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190139292246150040331429639 285208938369225060497144459)
      ·
        refine ⟨427813407553837590745716689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285208938369225060497144459 427813407553837590745716689)
        ·
          refine ⟨320860055665378193059287517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427813407553837590745716689 320860055665378193059287517)
          ·
            refine ⟨120322520874516822397232819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320860055665378193059287517 120322520874516822397232819)
            ·
              refine ⟨180483781311775233595849229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120322520874516822397232819 180483781311775233595849229)
              ·
                refine ⟨67681417991915712598443461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180483781311775233595849229 67681417991915712598443461)
                ·
                  refine ⟨12690265873484196112208149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67681417991915712598443461 12690265873484196112208149)
                  ·
                    refine ⟨594856212819571692759757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12690265873484196112208149 594856212819571692759757)
                    ·
                      rfl

theorem cell23_3475435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_3475435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475435 prefixEnd_3475435 := by exact prefixLift 3475435
  have htrace : WordTrace (prefixWord ++ tailWord_3475435) baseStart_3475435 baseEnd_3475435 := by
    simpa [prefixWord, tailWord_3475435, baseEnd_3475435] using wordTrace_append hprefix tailTrace_3475435
  have hstable : (prefixWord ++ tailWord_3475435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475435).length < 2 ^ (prefixWord ++ tailWord_3475435).sum := by decide
  have hdescent : baseEnd_3475435 < baseStart_3475435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475437 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3475437 : Nat := 118140960795 + 3475437 * 2 ^ 59
def prefixEnd_3475437 : Nat := 4983230072969 + 3 ^ 40 * 3475437 * 2
def baseEnd_3475437 : Nat := 1784569665420024070454263

theorem tailTrace_3475437 : CollatzResearch.WordTrace tailWord_3475437 prefixEnd_3475437 1784569665420024070454263 := by
  unfold tailWord_3475437
  simp only [CollatzResearch.WordTrace]
  refine ⟨126759601110092781229192565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84506400740061854152795043 126759601110092781229192565)
  ·
    refine ⟨11883712604071198240236803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126759601110092781229192565 11883712604071198240236803)
    ·
      refine ⟨17825568906106797360355205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11883712604071198240236803 17825568906106797360355205)
      ·
        refine ⟨3342294169895024505066601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17825568906106797360355205 3342294169895024505066601)
        ·
          refine ⟨2506720627421268378799951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3342294169895024505066601 2506720627421268378799951)
          ·
            refine ⟨3760080941131902568199927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506720627421268378799951 3760080941131902568199927)
            ·
              refine ⟨5640121411697853852299891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760080941131902568199927 5640121411697853852299891)
              ·
                refine ⟨8460182117546780778449837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640121411697853852299891 8460182117546780778449837)
                ·
                  refine ⟨3172568294080042791918689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8460182117546780778449837 3172568294080042791918689)
                  ·
                    refine ⟨2379426220560032093939017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3172568294080042791918689 2379426220560032093939017)
                    ·
                      refine ⟨1784569665420024070454263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379426220560032093939017 1784569665420024070454263)
                      ·
                        rfl

theorem cell23_3475437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3475437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475437 prefixEnd_3475437 := by exact prefixLift 3475437
  have htrace : WordTrace (prefixWord ++ tailWord_3475437) baseStart_3475437 baseEnd_3475437 := by
    simpa [prefixWord, tailWord_3475437, baseEnd_3475437] using wordTrace_append hprefix tailTrace_3475437
  have hstable : (prefixWord ++ tailWord_3475437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475437).length < 2 ^ (prefixWord ++ tailWord_3475437).sum := by decide
  have hdescent : baseEnd_3475437 < baseStart_3475437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475455 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_3475455 : Nat := 118140960795 + 3475455 * 2 ^ 59
def prefixEnd_3475455 : Nat := 4983230072969 + 3 ^ 40 * 3475455 * 2
def baseEnd_3475455 : Nat := 1784578908071805000029179

theorem tailTrace_3475455 : CollatzResearch.WordTrace tailWord_3475455 prefixEnd_3475455 1784578908071805000029179 := by
  unfold tailWord_3475455
  simp only [CollatzResearch.WordTrace]
  refine ⟨126760257624027570303347819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84506838416018380202231879 126760257624027570303347819)
  ·
    refine ⟨190140386436041355455021729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126760257624027570303347819 190140386436041355455021729)
    ·
      refine ⟨142605289827031016591266297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190140386436041355455021729 142605289827031016591266297)
      ·
        refine ⟨106953967370273262443449723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142605289827031016591266297 106953967370273262443449723)
        ·
          refine ⟨160430951055409893665174585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106953967370273262443449723 160430951055409893665174585)
          ·
            refine ⟨120323213291557420248880939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160430951055409893665174585 120323213291557420248880939)
            ·
              refine ⟨180484819937336130373321409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120323213291557420248880939 180484819937336130373321409)
              ·
                refine ⟨135363614953002097779991057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180484819937336130373321409 135363614953002097779991057)
                ·
                  refine ⟨101522711214751573334993293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135363614953002097779991057 101522711214751573334993293)
                  ·
                    refine ⟨38071016705531840000622485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101522711214751573334993293 38071016705531840000622485)
                    ·
                      refine ⟨1784578908071805000029179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38071016705531840000622485 1784578908071805000029179)
                      ·
                        rfl

theorem cell23_3475455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_3475455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475455 prefixEnd_3475455 := by exact prefixLift 3475455
  have htrace : WordTrace (prefixWord ++ tailWord_3475455) baseStart_3475455 baseEnd_3475455 := by
    simpa [prefixWord, tailWord_3475455, baseEnd_3475455] using wordTrace_append hprefix tailTrace_3475455
  have hstable : (prefixWord ++ tailWord_3475455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475455).length < 2 ^ (prefixWord ++ tailWord_3475455).sum := by decide
  have hdescent : baseEnd_3475455 < baseStart_3475455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475463 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_3475463 : Nat := 118140960795 + 3475463 * 2 ^ 59
def prefixEnd_3475463 : Nat := 4983230072969 + 3 ^ 40 * 3475463 * 2
def baseEnd_3475463 : Nat := 1784583015917040968729143

theorem tailTrace_3475463 : CollatzResearch.WordTrace tailWord_3475463 prefixEnd_3475463 1784583015917040968729143 := by
  unfold tailWord_3475463
  simp only [CollatzResearch.WordTrace]
  refine ⟨126760549407998587669639043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84507032938665725113092695 126760549407998587669639043)
  ·
    refine ⟨190140824111997881504458565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126760549407998587669639043 190140824111997881504458565)
    ·
      refine ⟨35651404520999602782085981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190140824111997881504458565 35651404520999602782085981)
      ·
        refine ⟨13369276695374851043282243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35651404520999602782085981 13369276695374851043282243)
        ·
          refine ⟨20053915043062276564923365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13369276695374851043282243 20053915043062276564923365)
          ·
            refine ⟨3760109070574176855923131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20053915043062276564923365 3760109070574176855923131)
            ·
              refine ⟨5640163605861265283884697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760109070574176855923131 5640163605861265283884697)
              ·
                refine ⟨4230122704395948962913523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5640163605861265283884697 4230122704395948962913523)
                ·
                  refine ⟨6345184056593923444370285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230122704395948962913523 6345184056593923444370285)
                  ·
                    refine ⟨2379444021222721291638857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6345184056593923444370285 2379444021222721291638857)
                    ·
                      refine ⟨1784583015917040968729143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379444021222721291638857 1784583015917040968729143)
                      ·
                        rfl

theorem cell23_3475463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_3475463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475463 prefixEnd_3475463 := by exact prefixLift 3475463
  have htrace : WordTrace (prefixWord ++ tailWord_3475463) baseStart_3475463 baseEnd_3475463 := by
    simpa [prefixWord, tailWord_3475463, baseEnd_3475463] using wordTrace_append hprefix tailTrace_3475463
  have hstable : (prefixWord ++ tailWord_3475463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475463).length < 2 ^ (prefixWord ++ tailWord_3475463).sum := by decide
  have hdescent : baseEnd_3475463 < baseStart_3475463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475493 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 2, 2, 2]
def baseStart_3475493 : Nat := 118140960795 + 3475493 * 2 ^ 59
def prefixEnd_3475493 : Nat := 4983230072969 + 3 ^ 40 * 3475493 * 2
def baseEnd_3475493 : Nat := 1784598420336675851354005

theorem tailTrace_3475493 : CollatzResearch.WordTrace tailWord_3475493 prefixEnd_3475493 1784598420336675851354005 := by
  unfold tailWord_3475493
  simp only [CollatzResearch.WordTrace]
  refine ⟨126761643597889902793231133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84507762398593268528820755 126761643597889902793231133)
  ·
    refine ⟨47535616349208713547461675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126761643597889902793231133 47535616349208713547461675)
    ·
      refine ⟨71303424523813070321192513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47535616349208713547461675 71303424523813070321192513)
      ·
        refine ⟨53477568392859802740894385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71303424523813070321192513 53477568392859802740894385)
        ·
          refine ⟨40108176294644852055670789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53477568392859802740894385 40108176294644852055670789)
          ·
            refine ⟨7520283055245909760438273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40108176294644852055670789 7520283055245909760438273)
            ·
              refine ⟨5640212291434432320328705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520283055245909760438273 5640212291434432320328705)
              ·
                refine ⟨4230159218575824240246529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5640212291434432320328705 4230159218575824240246529)
                ·
                  refine ⟨3172619413931868180184897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4230159218575824240246529 3172619413931868180184897)
                  ·
                    refine ⟨2379464560448901135138673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3172619413931868180184897 2379464560448901135138673)
                    ·
                      refine ⟨1784598420336675851354005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379464560448901135138673 1784598420336675851354005)
                      ·
                        rfl

theorem cell23_3475493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_3475493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475493 prefixEnd_3475493 := by exact prefixLift 3475493
  have htrace : WordTrace (prefixWord ++ tailWord_3475493) baseStart_3475493 baseEnd_3475493 := by
    simpa [prefixWord, tailWord_3475493, baseEnd_3475493] using wordTrace_append hprefix tailTrace_3475493
  have hstable : (prefixWord ++ tailWord_3475493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475493).length < 2 ^ (prefixWord ++ tailWord_3475493).sum := by decide
  have hdescent : baseEnd_3475493 < baseStart_3475493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475526 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3475526 : Nat := 118140960795 + 3475526 * 2 ^ 59
def prefixEnd_3475526 : Nat := 4983230072969 + 3 ^ 40 * 3475526 * 2
def baseEnd_3475526 : Nat := 1784615365198274222241353

theorem tailTrace_3475526 : CollatzResearch.WordTrace tailWord_3475526 prefixEnd_3475526 1784615365198274222241353 := by
  unfold tailWord_3475526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961338975211573419661951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84508564804513566286121621 3961338975211573419661951)
  ·
    refine ⟨5942008462817360129492927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3961338975211573419661951 5942008462817360129492927)
    ·
      refine ⟨8913012694226040194239391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5942008462817360129492927 8913012694226040194239391)
      ·
        refine ⟨13369519041339060291359087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8913012694226040194239391 13369519041339060291359087)
        ·
          refine ⟨20054278562008590437038631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13369519041339060291359087 20054278562008590437038631)
          ·
            refine ⟨30081417843012885655557947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20054278562008590437038631 30081417843012885655557947)
            ·
              refine ⟨45122126764519328483336921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30081417843012885655557947 45122126764519328483336921)
              ·
                refine ⟨33841595073389496362502691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45122126764519328483336921 33841595073389496362502691)
                ·
                  refine ⟨50762392610084244543754037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33841595073389496362502691 50762392610084244543754037)
                  ·
                    refine ⟨4758974307195397925976941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50762392610084244543754037 4758974307195397925976941)
                    ·
                      refine ⟨1784615365198274222241353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4758974307195397925976941 1784615365198274222241353)
                      ·
                        rfl

theorem cell23_3475526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3475526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475526 prefixEnd_3475526 := by exact prefixLift 3475526
  have htrace : WordTrace (prefixWord ++ tailWord_3475526) baseStart_3475526 baseEnd_3475526 := by
    simpa [prefixWord, tailWord_3475526, baseEnd_3475526] using wordTrace_append hprefix tailTrace_3475526
  have hstable : (prefixWord ++ tailWord_3475526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475526).length < 2 ^ (prefixWord ++ tailWord_3475526).sum := by decide
  have hdescent : baseEnd_3475526 < baseStart_3475526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475566 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_3475566 : Nat := 118140960795 + 3475566 * 2 ^ 59
def prefixEnd_3475566 : Nat := 4983230072969 + 3 ^ 40 * 3475566 * 2
def baseEnd_3475566 : Nat := 1784635904424454065741169

theorem tailTrace_3475566 : CollatzResearch.WordTrace tailWord_3475566 prefixEnd_3475566 1784635904424454065741169 := by
  unfold tailWord_3475566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845538265828179532579819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84509537417750290840425701 15845538265828179532579819)
  ·
    refine ⟨23768307398742269298869729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15845538265828179532579819 23768307398742269298869729)
    ·
      refine ⟨17826230549056701974152297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23768307398742269298869729 17826230549056701974152297)
      ·
        refine ⟨13369672911792526480614223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17826230549056701974152297 13369672911792526480614223)
        ·
          refine ⟨20054509367688789720921335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13369672911792526480614223 20054509367688789720921335)
          ·
            refine ⟨30081764051533184581382003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20054509367688789720921335 30081764051533184581382003)
            ·
              refine ⟨45122646077299776872073005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30081764051533184581382003 45122646077299776872073005)
              ·
                refine ⟨16920992278987416327027377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45122646077299776872073005 16920992278987416327027377)
                ·
                  refine ⟨12690744209240562245270533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16920992278987416327027377 12690744209240562245270533)
                  ·
                    refine ⟨2379514539232605420988225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12690744209240562245270533 2379514539232605420988225)
                    ·
                      refine ⟨1784635904424454065741169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379514539232605420988225 1784635904424454065741169)
                      ·
                        rfl

theorem cell23_3475566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_3475566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475566 prefixEnd_3475566 := by exact prefixLift 3475566
  have htrace : WordTrace (prefixWord ++ tailWord_3475566) baseStart_3475566 baseEnd_3475566 := by
    simpa [prefixWord, tailWord_3475566, baseEnd_3475566] using wordTrace_append hprefix tailTrace_3475566
  have hstable : (prefixWord ++ tailWord_3475566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475566).length < 2 ^ (prefixWord ++ tailWord_3475566).sum := by decide
  have hdescent : baseEnd_3475566 < baseStart_3475566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475610 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_3475610 : Nat := 118140960795 + 3475610 * 2 ^ 59
def prefixEnd_3475610 : Nat := 4983230072969 + 3 ^ 40 * 3475610 * 2
def baseEnd_3475610 : Nat := 594886165857750631196989

theorem tailTrace_3475610 : CollatzResearch.WordTrace tailWord_3475610 prefixEnd_3475610 594886165857750631196989 := by
  unfold tailWord_3475610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31691477734616507943810071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84510607292310687850160189 31691477734616507943810071)
  ·
    refine ⟨47537216601924761915715107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31691477734616507943810071 47537216601924761915715107)
    ·
      refine ⟨71305824902887142873572661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47537216601924761915715107 71305824902887142873572661)
      ·
        refine ⟨6684921084645669644397437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71305824902887142873572661 6684921084645669644397437)
        ·
          refine ⟨2506845406742126116649039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6684921084645669644397437 2506845406742126116649039)
          ·
            refine ⟨3760268110113189174973559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506845406742126116649039 3760268110113189174973559)
            ·
              refine ⟨5640402165169783762460339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760268110113189174973559 5640402165169783762460339)
              ·
                refine ⟨8460603247754675643690509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640402165169783762460339 8460603247754675643690509)
                ·
                  refine ⟨3172726217908003366383941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8460603247754675643690509 3172726217908003366383941)
                  ·
                    refine ⟨594886165857750631196989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3172726217908003366383941 594886165857750631196989)
                    ·
                      rfl

theorem cell23_3475610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_3475610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475610 prefixEnd_3475610 := by exact prefixLift 3475610
  have htrace : WordTrace (prefixWord ++ tailWord_3475610) baseStart_3475610 baseEnd_3475610 := by
    simpa [prefixWord, tailWord_3475610, baseEnd_3475610] using wordTrace_append hprefix tailTrace_3475610
  have hstable : (prefixWord ++ tailWord_3475610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475610).length < 2 ^ (prefixWord ++ tailWord_3475610).sum := by decide
  have hdescent : baseEnd_3475610 < baseStart_3475610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475683 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 1, 6]
def baseStart_3475683 : Nat := 118140960795 + 3475683 * 2 ^ 59
def prefixEnd_3475683 : Nat := 4983230072969 + 3 ^ 40 * 3475683 * 2
def baseEnd_3475683 : Nat := 594898660553676702659377

theorem tailTrace_3475683 : CollatzResearch.WordTrace tailWord_3475683 prefixEnd_3475683 594898660553676702659377 := by
  unfold tailWord_3475683
  simp only [CollatzResearch.WordTrace]
  refine ⟨126768573467201565242647703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84512382311467710161765135 126768573467201565242647703)
  ·
    refine ⟨190152860200802347863971555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126768573467201565242647703 190152860200802347863971555)
    ·
      refine ⟨285229290301203521795957333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190152860200802347863971555 285229290301203521795957333)
      ·
        refine ⟨3342530745717228771046375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 285229290301203521795957333 3342530745717228771046375)
        ·
          refine ⟨5013796118575843156569563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342530745717228771046375 5013796118575843156569563)
          ·
            refine ⟨7520694177863764734854345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013796118575843156569563 7520694177863764734854345)
            ·
              refine ⟨5640520633397823551140759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520694177863764734854345 5640520633397823551140759)
              ·
                refine ⟨8460780950096735326711139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640520633397823551140759 8460780950096735326711139)
                ·
                  refine ⟨12691171425145102990066709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460780950096735326711139 12691171425145102990066709)
                  ·
                    refine ⟨594898660553676702659377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12691171425145102990066709 594898660553676702659377)
                    ·
                      rfl

theorem cell23_3475683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 6].length) (baseStart_3475683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475683 prefixEnd_3475683 := by exact prefixLift 3475683
  have htrace : WordTrace (prefixWord ++ tailWord_3475683) baseStart_3475683 baseEnd_3475683 := by
    simpa [prefixWord, tailWord_3475683, baseEnd_3475683] using wordTrace_append hprefix tailTrace_3475683
  have hstable : (prefixWord ++ tailWord_3475683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475683).length < 2 ^ (prefixWord ++ tailWord_3475683).sum := by decide
  have hdescent : baseEnd_3475683 < baseStart_3475683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475689 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_3475689 : Nat := 118140960795 + 3475689 * 2 ^ 59
def prefixEnd_3475689 : Nat := 4983230072969 + 3 ^ 40 * 3475689 * 2
def baseEnd_3475689 : Nat := 1784699062544957084503103

theorem tailTrace_3475689 : CollatzResearch.WordTrace tailWord_3475689 prefixEnd_3475689 1784699062544957084503103 := by
  unfold tailWord_3475689
  simp only [CollatzResearch.WordTrace]
  refine ⟨126768792305179828267366121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84512528203453218844910747 126768792305179828267366121)
  ·
    refine ⟨95076594228884871200524591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126768792305179828267366121 95076594228884871200524591)
    ·
      refine ⟨142614891343327306800786887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95076594228884871200524591 142614891343327306800786887)
      ·
        refine ⟨213922337014990960201180331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142614891343327306800786887 213922337014990960201180331)
        ·
          refine ⟨320883505522486440301770497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213922337014990960201180331 320883505522486440301770497)
          ·
            refine ⟨240662629141864830226327873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320883505522486440301770497 240662629141864830226327873)
            ·
              refine ⟨180496971856398622669745905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240662629141864830226327873 180496971856398622669745905)
              ·
                refine ⟨135372728892298967002309429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180496971856398622669745905 135372728892298967002309429)
                ·
                  refine ⟨12691193333653028156466509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135372728892298967002309429 12691193333653028156466509)
                  ·
                    refine ⟨4759197500119885558674941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12691193333653028156466509 4759197500119885558674941)
                    ·
                      refine ⟨1784699062544957084503103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759197500119885558674941 1784699062544957084503103)
                      ·
                        rfl

theorem cell23_3475689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_3475689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475689 prefixEnd_3475689 := by exact prefixLift 3475689
  have htrace : WordTrace (prefixWord ++ tailWord_3475689) baseStart_3475689 baseEnd_3475689 := by
    simpa [prefixWord, tailWord_3475689, baseEnd_3475689] using wordTrace_append hprefix tailTrace_3475689
  have hstable : (prefixWord ++ tailWord_3475689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475689).length < 2 ^ (prefixWord ++ tailWord_3475689).sum := by decide
  have hdescent : baseEnd_3475689 < baseStart_3475689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475706 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_3475706 : Nat := 118140960795 + 3475706 * 2 ^ 59
def prefixEnd_3475706 : Nat := 4983230072969 + 3 ^ 40 * 3475706 * 2
def baseEnd_3475706 : Nat := 1784707791716083517990525

theorem tailTrace_3475706 : CollatzResearch.WordTrace tailWord_3475706 prefixEnd_3475706 1784707791716083517990525 := by
  unfold tailWord_3475706
  simp only [CollatzResearch.WordTrace]
  refine ⟨31692353086529560042683743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84512941564078826780489981 31692353086529560042683743)
  ·
    refine ⟨47538529629794340064025615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31692353086529560042683743 47538529629794340064025615)
    ·
      refine ⟨71307794444691510096038423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47538529629794340064025615 71307794444691510096038423)
      ·
        refine ⟨106961691667037265144057635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71307794444691510096038423 106961691667037265144057635)
        ·
          refine ⟨160442537500555897716086453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106961691667037265144057635 160442537500555897716086453)
          ·
            refine ⟨15041487890677115410883105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160442537500555897716086453 15041487890677115410883105)
            ·
              refine ⟨11281115918007836558162329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15041487890677115410883105 11281115918007836558162329)
              ·
                refine ⟨8460836938505877418621747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11281115918007836558162329 8460836938505877418621747)
                ·
                  refine ⟨12691255407758816127932621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460836938505877418621747 12691255407758816127932621)
                  ·
                    refine ⟨4759220777909556047974733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12691255407758816127932621 4759220777909556047974733)
                    ·
                      refine ⟨1784707791716083517990525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759220777909556047974733 1784707791716083517990525)
                      ·
                        rfl

theorem cell23_3475706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_3475706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475706 prefixEnd_3475706 := by exact prefixLift 3475706
  have htrace : WordTrace (prefixWord ++ tailWord_3475706) baseStart_3475706 baseEnd_3475706 := by
    simpa [prefixWord, tailWord_3475706, baseEnd_3475706] using wordTrace_append hprefix tailTrace_3475706
  have hstable : (prefixWord ++ tailWord_3475706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475706).length < 2 ^ (prefixWord ++ tailWord_3475706).sum := by decide
  have hdescent : baseEnd_3475706 < baseStart_3475706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475739 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 2, 6]
def baseStart_3475739 : Nat := 118140960795 + 3475739 * 2 ^ 59
def prefixEnd_3475739 : Nat := 4983230072969 + 3 ^ 40 * 3475739 * 2
def baseEnd_3475739 : Nat := 594908245525893962959291

theorem tailTrace_3475739 : CollatzResearch.WordTrace tailWord_3475739 prefixEnd_3475739 594908245525893962959291 := by
  unfold tailWord_3475739
  simp only [CollatzResearch.WordTrace]
  refine ⟨126770615954998686806686271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84513743969999124537790847 126770615954998686806686271)
  ·
    refine ⟨190155923932498030210029407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126770615954998686806686271 190155923932498030210029407)
    ·
      refine ⟨285233885898747045315044111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190155923932498030210029407 285233885898747045315044111)
      ·
        refine ⟨427850828848120567972566167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285233885898747045315044111 427850828848120567972566167)
        ·
          refine ⟨641776243272180851958849251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427850828848120567972566167 641776243272180851958849251)
          ·
            refine ⟨962664364908271277938273877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641776243272180851958849251 962664364908271277938273877)
            ·
              refine ⟨11281223026268804038339147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 962664364908271277938273877 11281223026268804038339147)
              ·
                refine ⟨16921834539403206057508721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281223026268804038339147 16921834539403206057508721)
                ·
                  refine ⟨12691375904552404543131541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16921834539403206057508721 12691375904552404543131541)
                  ·
                    refine ⟨594908245525893962959291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12691375904552404543131541 594908245525893962959291)
                    ·
                      rfl

theorem cell23_3475739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_3475739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475739 prefixEnd_3475739 := by exact prefixLift 3475739
  have htrace : WordTrace (prefixWord ++ tailWord_3475739) baseStart_3475739 baseEnd_3475739 := by
    simpa [prefixWord, tailWord_3475739, baseEnd_3475739] using wordTrace_append hprefix tailTrace_3475739
  have hstable : (prefixWord ++ tailWord_3475739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475739).length < 2 ^ (prefixWord ++ tailWord_3475739).sum := by decide
  have hdescent : baseEnd_3475739 < baseStart_3475739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475758 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3475758 : Nat := 118140960795 + 3475758 * 2 ^ 59
def prefixEnd_3475758 : Nat := 4983230072969 + 3 ^ 40 * 3475758 * 2
def baseEnd_3475758 : Nat := 1784734492710117314540287

theorem tailTrace_3475758 : CollatzResearch.WordTrace tailWord_3475758 prefixEnd_3475758 1784734492710117314540287 := by
  unfold tailWord_3475758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846413617741231631453491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84514205961286568701085285 15846413617741231631453491)
  ·
    refine ⟨23769620426611847447180237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15846413617741231631453491 23769620426611847447180237)
    ·
      refine ⟨8913607659979442792692589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23769620426611847447180237 8913607659979442792692589)
      ·
        refine ⟨3342602872492291047259721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8913607659979442792692589 3342602872492291047259721)
        ·
          refine ⟨2506952154369218285444791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3342602872492291047259721 2506952154369218285444791)
          ·
            refine ⟨3760428231553827428167187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506952154369218285444791 3760428231553827428167187)
            ·
              refine ⟨5640642347330741142250781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760428231553827428167187 5640642347330741142250781)
              ·
                refine ⟨2115240880249027928344043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5640642347330741142250781 2115240880249027928344043)
                ·
                  refine ⟨3172861320373541892516065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115240880249027928344043 3172861320373541892516065)
                  ·
                    refine ⟨2379645990280156419387049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3172861320373541892516065 2379645990280156419387049)
                    ·
                      refine ⟨1784734492710117314540287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379645990280156419387049 1784734492710117314540287)
                      ·
                        rfl

theorem cell23_3475758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3475758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475758 prefixEnd_3475758 := by exact prefixLift 3475758
  have htrace : WordTrace (prefixWord ++ tailWord_3475758) baseStart_3475758 baseEnd_3475758 := by
    simpa [prefixWord, tailWord_3475758, baseEnd_3475758] using wordTrace_append hprefix tailTrace_3475758
  have hstable : (prefixWord ++ tailWord_3475758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475758).length < 2 ^ (prefixWord ++ tailWord_3475758).sum := by decide
  have hdescent : baseEnd_3475758 < baseStart_3475758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475759 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_3475759 : Nat := 118140960795 + 3475759 * 2 ^ 59
def prefixEnd_3475759 : Nat := 4983230072969 + 3 ^ 40 * 3475759 * 2
def baseEnd_3475759 : Nat := 1784735006190771810627781

theorem tailTrace_3475759 : CollatzResearch.WordTrace tailWord_3475759 prefixEnd_3475759 1784735006190771810627781 := by
  unfold tailWord_3475759
  simp only [CollatzResearch.WordTrace]
  refine ⟨126771345414926230222414331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84514230276617486814942887 126771345414926230222414331)
  ·
    refine ⟨190157018122389345333621497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126771345414926230222414331 190157018122389345333621497)
    ·
      refine ⟨142617763591792009000216123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190157018122389345333621497 142617763591792009000216123)
      ·
        refine ⟨213926645387688013500324185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142617763591792009000216123 213926645387688013500324185)
        ·
          refine ⟨160444984040766010125243139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213926645387688013500324185 160444984040766010125243139)
          ·
            refine ⟨240667476061149015187864709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160444984040766010125243139 240667476061149015187864709)
            ·
              refine ⟨45125151761465440347724633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240667476061149015187864709 45125151761465440347724633)
              ·
                refine ⟨33843863821099080260793475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45125151761465440347724633 33843863821099080260793475)
                ·
                  refine ⟨50765795731648620391190213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33843863821099080260793475 50765795731648620391190213)
                  ·
                    refine ⟨9518586699684116323348165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50765795731648620391190213 9518586699684116323348165)
                    ·
                      refine ⟨1784735006190771810627781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9518586699684116323348165 1784735006190771810627781)
                      ·
                        rfl

theorem cell23_3475759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_3475759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475759 prefixEnd_3475759 := by exact prefixLift 3475759
  have htrace : WordTrace (prefixWord ++ tailWord_3475759) baseStart_3475759 baseEnd_3475759 := by
    simpa [prefixWord, tailWord_3475759, baseEnd_3475759] using wordTrace_append hprefix tailTrace_3475759
  have hstable : (prefixWord ++ tailWord_3475759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475759).length < 2 ^ (prefixWord ++ tailWord_3475759).sum := by decide
  have hdescent : baseEnd_3475759 < baseStart_3475759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475763 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 6, 2, 2]
def baseStart_3475763 : Nat := 118140960795 + 3475763 * 2 ^ 59
def prefixEnd_3475763 : Nat := 4983230072969 + 3 ^ 40 * 3475763 * 2
def baseEnd_3475763 : Nat := 1784737060113389794977763

theorem tailTrace_3475763 : CollatzResearch.WordTrace tailWord_3475763 prefixEnd_3475763 1784737060113389794977763 := by
  unfold tailWord_3475763
  simp only [CollatzResearch.WordTrace]
  refine ⟨126771491306911738905559943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84514327537941159270373295 126771491306911738905559943)
  ·
    refine ⟨190157236960367608358339915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126771491306911738905559943 190157236960367608358339915)
    ·
      refine ⟨285235855440551412537509873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190157236960367608358339915 285235855440551412537509873)
      ·
        refine ⟨213926891580413559403132405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285235855440551412537509873 213926891580413559403132405)
        ·
          refine ⟨20055646085663771194043663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213926891580413559403132405 20055646085663771194043663)
          ·
            refine ⟨30083469128495656791065495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20055646085663771194043663 30083469128495656791065495)
            ·
              refine ⟨45125203692743485186598243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30083469128495656791065495 45125203692743485186598243)
              ·
                refine ⟨67687805539115227779897365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45125203692743485186598243 67687805539115227779897365)
                ·
                  refine ⟨3172865884646026302182689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67687805539115227779897365 3172865884646026302182689)
                  ·
                    refine ⟨2379649413484519726637017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3172865884646026302182689 2379649413484519726637017)
                    ·
                      refine ⟨1784737060113389794977763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379649413484519726637017 1784737060113389794977763)
                      ·
                        rfl

theorem cell23_3475763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 2, 2].length) (baseStart_3475763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475763 prefixEnd_3475763 := by exact prefixLift 3475763
  have htrace : WordTrace (prefixWord ++ tailWord_3475763) baseStart_3475763 baseEnd_3475763 := by
    simpa [prefixWord, tailWord_3475763, baseEnd_3475763] using wordTrace_append hprefix tailTrace_3475763
  have hstable : (prefixWord ++ tailWord_3475763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475763).length < 2 ^ (prefixWord ++ tailWord_3475763).sum := by decide
  have hdescent : baseEnd_3475763 < baseStart_3475763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475797 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_3475797 : Nat := 118140960795 + 3475797 * 2 ^ 59
def prefixEnd_3475797 : Nat := 4983230072969 + 3 ^ 40 * 3475797 * 2
def baseEnd_3475797 : Nat := 1784754518455642661952607

theorem tailTrace_3475797 : CollatzResearch.WordTrace tailWord_3475797 prefixEnd_3475797 1784754518455642661952607 := by
  unfold tailWord_3475797
  simp only [CollatzResearch.WordTrace]
  refine ⟨126772731388788562712297645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84515154259192375141531763 126772731388788562712297645)
  ·
    refine ⟨47539774270795711017111617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126772731388788562712297645 47539774270795711017111617)
    ·
      refine ⟨35654830703096783262833713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47539774270795711017111617 35654830703096783262833713)
      ·
        refine ⟨26741123027322587447125285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35654830703096783262833713 26741123027322587447125285)
        ·
          refine ⟨5013960567622985146335991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26741123027322587447125285 5013960567622985146335991)
          ·
            refine ⟨7520940851434477719503987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013960567622985146335991 7520940851434477719503987)
            ·
              refine ⟨11281411277151716579255981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520940851434477719503987 11281411277151716579255981)
              ·
                refine ⟨4230529228931893717220993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11281411277151716579255981 4230529228931893717220993)
                ·
                  refine ⟨3172896921698920287915745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4230529228931893717220993 3172896921698920287915745)
                  ·
                    refine ⟨2379672691274190215936809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3172896921698920287915745 2379672691274190215936809)
                    ·
                      refine ⟨1784754518455642661952607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379672691274190215936809 1784754518455642661952607)
                      ·
                        rfl

theorem cell23_3475797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_3475797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475797 prefixEnd_3475797 := by exact prefixLift 3475797
  have htrace : WordTrace (prefixWord ++ tailWord_3475797) baseStart_3475797 baseEnd_3475797 := by
    simpa [prefixWord, tailWord_3475797, baseEnd_3475797] using wordTrace_append hprefix tailTrace_3475797
  have hstable : (prefixWord ++ tailWord_3475797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475797).length < 2 ^ (prefixWord ++ tailWord_3475797).sum := by decide
  have hdescent : baseEnd_3475797 < baseStart_3475797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475826 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3475826 : Nat := 118140960795 + 3475826 * 2 ^ 59
def prefixEnd_3475826 : Nat := 4983230072969 + 3 ^ 40 * 3475826 * 2
def baseEnd_3475826 : Nat := 1784769409394623048489973

theorem tailTrace_3475826 : CollatzResearch.WordTrace tailWord_3475826 prefixEnd_3475826 1784769409394623048489973 := by
  unfold tailWord_3475826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31693447276420875166275833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84515859403789000443402221 31693447276420875166275833)
  ·
    refine ⟨23770085457315656374706875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31693447276420875166275833 23770085457315656374706875)
    ·
      refine ⟨35655128185973484562060313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23770085457315656374706875 35655128185973484562060313)
      ·
        refine ⟨26741346139480113421545235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35655128185973484562060313 26741346139480113421545235)
        ·
          refine ⟨40112019209220170132317853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26741346139480113421545235 40112019209220170132317853)
          ·
            refine ⟨15042007203457563799619195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40112019209220170132317853 15042007203457563799619195)
            ·
              refine ⟨22563010805186345699428793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15042007203457563799619195 22563010805186345699428793)
              ·
                refine ⟨16922258103889759274571595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22563010805186345699428793 16922258103889759274571595)
                ·
                  refine ⟨25383387155834638911857393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16922258103889759274571595 25383387155834638911857393)
                  ·
                    refine ⟨19037540366875979183893045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25383387155834638911857393 19037540366875979183893045)
                    ·
                      refine ⟨1784769409394623048489973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19037540366875979183893045 1784769409394623048489973)
                      ·
                        rfl

theorem cell23_3475826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3475826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475826 prefixEnd_3475826 := by exact prefixLift 3475826
  have htrace : WordTrace (prefixWord ++ tailWord_3475826) baseStart_3475826 baseEnd_3475826 := by
    simpa [prefixWord, tailWord_3475826, baseEnd_3475826] using wordTrace_append hprefix tailTrace_3475826
  have hstable : (prefixWord ++ tailWord_3475826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475826).length < 2 ^ (prefixWord ++ tailWord_3475826).sum := by decide
  have hdescent : baseEnd_3475826 < baseStart_3475826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475836 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3475836 : Nat := 118140960795 + 3475836 * 2 ^ 59
def prefixEnd_3475836 : Nat := 4983230072969 + 3 ^ 40 * 3475836 * 2
def baseEnd_3475836 : Nat := 1784774544201168009364927

theorem tailTrace_3475836 : CollatzResearch.WordTrace tailWord_3475836 prefixEnd_3475836 1784774544201168009364927 := by
  unfold tailWord_3475836
  simp only [CollatzResearch.WordTrace]
  refine ⟨63387076917823636186483681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84516102557098181581978241 63387076917823636186483681)
  ·
    refine ⟨47540307688367727139862761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63387076917823636186483681 47540307688367727139862761)
    ·
      refine ⟨35655230766275795354897071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47540307688367727139862761 35655230766275795354897071)
      ·
        refine ⟨53482846149413693032345607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35655230766275795354897071 53482846149413693032345607)
        ·
          refine ⟨80224269224120539548518411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53482846149413693032345607 80224269224120539548518411)
          ·
            refine ⟨120336403836180809322777617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80224269224120539548518411 120336403836180809322777617)
            ·
              refine ⟨90252302877135606992083213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120336403836180809322777617 90252302877135606992083213)
              ·
                refine ⟨33844613578925852622031205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90252302877135606992083213 33844613578925852622031205)
                ·
                  refine ⟨6345865046048597366630851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33844613578925852622031205 6345865046048597366630851)
                  ·
                    refine ⟨9518797569072896049946277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345865046048597366630851 9518797569072896049946277)
                    ·
                      refine ⟨1784774544201168009364927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9518797569072896049946277 1784774544201168009364927)
                      ·
                        rfl

theorem cell23_3475836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3475836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475836 prefixEnd_3475836 := by exact prefixLift 3475836
  have htrace : WordTrace (prefixWord ++ tailWord_3475836) baseStart_3475836 baseEnd_3475836 := by
    simpa [prefixWord, tailWord_3475836, baseEnd_3475836] using wordTrace_append hprefix tailTrace_3475836
  have hstable : (prefixWord ++ tailWord_3475836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475836).length < 2 ^ (prefixWord ++ tailWord_3475836).sum := by decide
  have hdescent : baseEnd_3475836 < baseStart_3475836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475870 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3475870 : Nat := 118140960795 + 3475870 * 2 ^ 59
def prefixEnd_3475870 : Nat := 4983230072969 + 3 ^ 40 * 3475870 * 2
def baseEnd_3475870 : Nat := 1784792002543420876339771

theorem tailTrace_3475870 : CollatzResearch.WordTrace tailWord_3475870 prefixEnd_3475870 1784792002543420876339771 := by
  unfold tailWord_3475870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846924239690512022463133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84516929278349397453136709 15846924239690512022463133)
  ·
    refine ⟨5942596589883942008423675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15846924239690512022463133 5942596589883942008423675)
    ·
      refine ⟨8913894884825913012635513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5942596589883942008423675 8913894884825913012635513)
      ·
        refine ⟨6685421163619434759476635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8913894884825913012635513 6685421163619434759476635)
        ·
          refine ⟨10028131745429152139214953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685421163619434759476635 10028131745429152139214953)
          ·
            refine ⟨7521098809071864104411215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028131745429152139214953 7521098809071864104411215)
            ·
              refine ⟨11281648213607796156616823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521098809071864104411215 11281648213607796156616823)
              ·
                refine ⟨16922472320411694234925235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281648213607796156616823 16922472320411694234925235)
                ·
                  refine ⟨25383708480617541352387853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16922472320411694234925235 25383708480617541352387853)
                  ·
                    refine ⟨9518890680231578007145445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25383708480617541352387853 9518890680231578007145445)
                    ·
                      refine ⟨1784792002543420876339771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9518890680231578007145445 1784792002543420876339771)
                      ·
                        rfl

theorem cell23_3475870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3475870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475870 prefixEnd_3475870 := by exact prefixLift 3475870
  have htrace : WordTrace (prefixWord ++ tailWord_3475870) baseStart_3475870 baseEnd_3475870 := by
    simpa [prefixWord, tailWord_3475870, baseEnd_3475870] using wordTrace_append hprefix tailTrace_3475870
  have hstable : (prefixWord ++ tailWord_3475870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475870).length < 2 ^ (prefixWord ++ tailWord_3475870).sum := by decide
  have hdescent : baseEnd_3475870 < baseStart_3475870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475893 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 8]
def baseStart_3475893 : Nat := 118140960795 + 3475893 * 2 ^ 59
def prefixEnd_3475893 : Nat := 4983230072969 + 3 ^ 40 * 3475893 * 2
def baseEnd_3475893 : Nat := 198311534733163809594685

theorem tailTrace_3475893 : CollatzResearch.WordTrace tailWord_3475893 prefixEnd_3475893 198311534733163809594685 := by
  unfold tailWord_3475893
  simp only [CollatzResearch.WordTrace]
  refine ⟨126776232796440771107792333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84517488530960514071861555 126776232796440771107792333)
  ·
    refine ⟨47541087298665289165422125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126776232796440771107792333 47541087298665289165422125)
    ·
      refine ⟨17827907736999483437033297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47541087298665289165422125 17827907736999483437033297)
      ·
        refine ⟨13370930802749612577774973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17827907736999483437033297 13370930802749612577774973)
        ·
          refine ⟨5014099051031104716665615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13370930802749612577774973 5014099051031104716665615)
          ·
            refine ⟨7521148576546657074998423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014099051031104716665615 7521148576546657074998423)
            ·
              refine ⟨11281722864819985612497635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521148576546657074998423 11281722864819985612497635)
              ·
                refine ⟨16922584297229978418746453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281722864819985612497635 16922584297229978418746453)
                ·
                  refine ⟨198311534733163809594685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16922584297229978418746453 198311534733163809594685)
                  ·
                    rfl

theorem cell23_3475893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_3475893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475893 prefixEnd_3475893 := by exact prefixLift 3475893
  have htrace : WordTrace (prefixWord ++ tailWord_3475893) baseStart_3475893 baseEnd_3475893 := by
    simpa [prefixWord, tailWord_3475893, baseEnd_3475893] using wordTrace_append hprefix tailTrace_3475893
  have hstable : (prefixWord ++ tailWord_3475893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475893).length < 2 ^ (prefixWord ++ tailWord_3475893).sum := by decide
  have hdescent : baseEnd_3475893 < baseStart_3475893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475913 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 1, 5, 2]
def baseStart_3475913 : Nat := 118140960795 + 3475913 * 2 ^ 59
def prefixEnd_3475913 : Nat := 4983230072969 + 3 ^ 40 * 3475913 * 2
def baseEnd_3475913 : Nat := 1784814082211564208102073

theorem tailTrace_3475913 : CollatzResearch.WordTrace tailWord_3475913 prefixEnd_3475913 1784814082211564208102073 := by
  unfold tailWord_3475913
  simp only [CollatzResearch.WordTrace]
  refine ⟨126776962256368314523520393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84517974837578876349013595 126776962256368314523520393)
  ·
    refine ⟨95082721692276235892640295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126776962256368314523520393 95082721692276235892640295)
    ·
      refine ⟨142624082538414353838960443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95082721692276235892640295 142624082538414353838960443)
      ·
        refine ⟨213936123807621530758440665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142624082538414353838960443 213936123807621530758440665)
        ·
          refine ⟨160452092855716148068830499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213936123807621530758440665 160452092855716148068830499)
          ·
            refine ⟨240678139283574222103245749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160452092855716148068830499 240678139283574222103245749)
            ·
              refine ⟨22563575557835083322179289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240678139283574222103245749 22563575557835083322179289)
              ·
                refine ⟨16922681668376312491634467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22563575557835083322179289 16922681668376312491634467)
                ·
                  refine ⟨25384022502564468737451701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16922681668376312491634467 25384022502564468737451701)
                  ·
                    refine ⟨2379752109615418944136097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25384022502564468737451701 2379752109615418944136097)
                    ·
                      refine ⟨1784814082211564208102073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379752109615418944136097 1784814082211564208102073)
                      ·
                        rfl

theorem cell23_3475913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 5, 2].length) (baseStart_3475913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475913 prefixEnd_3475913 := by exact prefixLift 3475913
  have htrace : WordTrace (prefixWord ++ tailWord_3475913) baseStart_3475913 baseEnd_3475913 := by
    simpa [prefixWord, tailWord_3475913, baseEnd_3475913] using wordTrace_append hprefix tailTrace_3475913
  have hstable : (prefixWord ++ tailWord_3475913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475913).length < 2 ^ (prefixWord ++ tailWord_3475913).sum := by decide
  have hdescent : baseEnd_3475913 < baseStart_3475913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475930 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2]
def baseStart_3475930 : Nat := 118140960795 + 3475930 * 2 ^ 59
def prefixEnd_3475930 : Nat := 4983230072969 + 3 ^ 40 * 3475930 * 2
def baseEnd_3475930 : Nat := 1784822811382690641589495

theorem tailTrace_3475930 : CollatzResearch.WordTrace tailWord_3475930 prefixEnd_3475930 1784822811382690641589495 := by
  unfold tailWord_3475930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31694395574326681606722311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84518388198204484284592829 31694395574326681606722311)
  ·
    refine ⟨47541593361490022410083467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31694395574326681606722311 47541593361490022410083467)
    ·
      refine ⟨71312390042235033615125201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47541593361490022410083467 71312390042235033615125201)
      ·
        refine ⟨53484292531676275211343901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71312390042235033615125201 53484292531676275211343901)
        ·
          refine ⟨20056609699378603204253963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53484292531676275211343901 20056609699378603204253963)
          ·
            refine ⟨30084914549067904806380945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056609699378603204253963 30084914549067904806380945)
            ·
              refine ⟨22563685911800928604785709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30084914549067904806380945 22563685911800928604785709)
              ·
                refine ⟨8461382216925348226794641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22563685911800928604785709 8461382216925348226794641)
                ·
                  refine ⟨6346036662694011170095981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8461382216925348226794641 6346036662694011170095981)
                  ·
                    refine ⟨2379763748510254188785993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6346036662694011170095981 2379763748510254188785993)
                    ·
                      refine ⟨1784822811382690641589495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379763748510254188785993 1784822811382690641589495)
                      ·
                        rfl

theorem cell23_3475930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_3475930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475930 prefixEnd_3475930 := by exact prefixLift 3475930
  have htrace : WordTrace (prefixWord ++ tailWord_3475930) baseStart_3475930 baseEnd_3475930 := by
    simpa [prefixWord, tailWord_3475930, baseEnd_3475930] using wordTrace_append hprefix tailTrace_3475930
  have hstable : (prefixWord ++ tailWord_3475930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475930).length < 2 ^ (prefixWord ++ tailWord_3475930).sum := by decide
  have hdescent : baseEnd_3475930 < baseStart_3475930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475936 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_3475936 : Nat := 118140960795 + 3475936 * 2 ^ 59
def prefixEnd_3475936 : Nat := 4983230072969 + 3 ^ 40 * 3475936 * 2
def baseEnd_3475936 : Nat := 594941964088872539371489

theorem tailTrace_3475936 : CollatzResearch.WordTrace tailWord_3475936 prefixEnd_3475936 594941964088872539371489 := by
  unfold tailWord_3475936
  simp only [CollatzResearch.WordTrace]
  refine ⟨63388900567642494725803831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84518534090189992967738441 63388900567642494725803831)
  ·
    refine ⟨95083350851463742088705747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63388900567642494725803831 95083350851463742088705747)
    ·
      refine ⟨142625026277195613133058621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95083350851463742088705747 142625026277195613133058621)
      ·
        refine ⟨53484384853948354924896983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142625026277195613133058621 53484384853948354924896983)
        ·
          refine ⟨80226577280922532387345475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53484384853948354924896983 80226577280922532387345475)
          ·
            refine ⟨120339865921383798581018213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80226577280922532387345475 120339865921383798581018213)
            ·
              refine ⟨22563724860259462233940915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120339865921383798581018213 22563724860259462233940915)
              ·
                refine ⟨33845587290389193350911373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22563724860259462233940915 33845587290389193350911373)
                ·
                  refine ⟨12692095233895947506591765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33845587290389193350911373 12692095233895947506591765)
                  ·
                    refine ⟨594941964088872539371489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12692095233895947506591765 594941964088872539371489)
                    ·
                      rfl

theorem cell23_3475936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_3475936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475936 prefixEnd_3475936 := by exact prefixLift 3475936
  have htrace : WordTrace (prefixWord ++ tailWord_3475936) baseStart_3475936 baseEnd_3475936 := by
    simpa [prefixWord, tailWord_3475936, baseEnd_3475936] using wordTrace_append hprefix tailTrace_3475936
  have hstable : (prefixWord ++ tailWord_3475936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475936).length < 2 ^ (prefixWord ++ tailWord_3475936).sum := by decide
  have hdescent : baseEnd_3475936 < baseStart_3475936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475953 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 4, 4]
def baseStart_3475953 : Nat := 118140960795 + 3475953 * 2 ^ 59
def prefixEnd_3475953 : Nat := 4983230072969 + 3 ^ 40 * 3475953 * 2
def baseEnd_3475953 : Nat := 594944873812581350533963

theorem tailTrace_3475953 : CollatzResearch.WordTrace tailWord_3475953 prefixEnd_3475953 594944873812581350533963 := by
  unfold tailWord_3475953
  simp only [CollatzResearch.WordTrace]
  refine ⟨126778421176223401354976513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84518947450815600903317675 126778421176223401354976513)
  ·
    refine ⟨95083815882167551016232385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126778421176223401354976513 95083815882167551016232385)
    ·
      refine ⟨71312861911625663262174289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95083815882167551016232385 71312861911625663262174289)
      ·
        refine ⟨53484646433719247446630717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71312861911625663262174289 53484646433719247446630717)
        ·
          refine ⟨20056742412644717792486519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53484646433719247446630717 20056742412644717792486519)
          ·
            refine ⟨30085113618967076688729779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056742412644717792486519 30085113618967076688729779)
            ·
              refine ⟨45127670428450615033094669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30085113618967076688729779 45127670428450615033094669)
              ·
                refine ⟨16922876410668980637410501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45127670428450615033094669 16922876410668980637410501)
                ·
                  refine ⟨3173039327000433869514469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16922876410668980637410501 3173039327000433869514469)
                  ·
                    refine ⟨594944873812581350533963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173039327000433869514469 594944873812581350533963)
                    ·
                      rfl

theorem cell23_3475953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_3475953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475953 prefixEnd_3475953 := by exact prefixLift 3475953
  have htrace : WordTrace (prefixWord ++ tailWord_3475953) baseStart_3475953 baseEnd_3475953 := by
    simpa [prefixWord, tailWord_3475953, baseEnd_3475953] using wordTrace_append hprefix tailTrace_3475953
  have hstable : (prefixWord ++ tailWord_3475953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475953).length < 2 ^ (prefixWord ++ tailWord_3475953).sum := by decide
  have hdescent : baseEnd_3475953 < baseStart_3475953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475954 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3475954 : Nat := 118140960795 + 3475954 * 2 ^ 59
def prefixEnd_3475954 : Nat := 4983230072969 + 3 ^ 40 * 3475954 * 2
def baseEnd_3475954 : Nat := 1784835134918398547689385

theorem tailTrace_3475954 : CollatzResearch.WordTrace tailWord_3475954 prefixEnd_3475954 1784835134918398547689385 := by
  unfold tailWord_3475954
  simp only [CollatzResearch.WordTrace]
  refine ⟨31694614412304944631440729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84518971766146519017175277 31694614412304944631440729)
  ·
    refine ⟨23770960809228708473580547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31694614412304944631440729 23770960809228708473580547)
    ·
      refine ⟨35656441213843062710370821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23770960809228708473580547 35656441213843062710370821)
      ·
        refine ⟨6685582727595574258194529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35656441213843062710370821 6685582727595574258194529)
        ·
          refine ⟨5014187045696680693645897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6685582727595574258194529 5014187045696680693645897)
          ·
            refine ⟨3760640284272510520234423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014187045696680693645897 3760640284272510520234423)
            ·
              refine ⟨5640960426408765780351635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760640284272510520234423 5640960426408765780351635)
              ·
                refine ⟨8461440639613148670527453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640960426408765780351635 8461440639613148670527453)
                ·
                  refine ⟨3173040239854930751447795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8461440639613148670527453 3173040239854930751447795)
                  ·
                    refine ⟨4759560359782396127171693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173040239854930751447795 4759560359782396127171693)
                    ·
                      refine ⟨1784835134918398547689385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759560359782396127171693 1784835134918398547689385)
                      ·
                        rfl

theorem cell23_3475954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3475954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475954 prefixEnd_3475954 := by exact prefixLift 3475954
  have htrace : WordTrace (prefixWord ++ tailWord_3475954) baseStart_3475954 baseEnd_3475954 := by
    simpa [prefixWord, tailWord_3475954, baseEnd_3475954] using wordTrace_append hprefix tailTrace_3475954
  have hstable : (prefixWord ++ tailWord_3475954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475954).length < 2 ^ (prefixWord ++ tailWord_3475954).sum := by decide
  have hdescent : baseEnd_3475954 < baseStart_3475954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475974 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3475974 : Nat := 118140960795 + 3475974 * 2 ^ 59
def prefixEnd_3475974 : Nat := 4983230072969 + 3 ^ 40 * 3475974 * 2
def baseEnd_3475974 : Nat := 594948468177162823146431

theorem tailTrace_3475974 : CollatzResearch.WordTrace tailWord_3475974 prefixEnd_3475974 594948468177162823146431 := by
  unfold tailWord_3475974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961849597160853810671593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84519458072764881294327317 3961849597160853810671593)
  ·
    refine ⟨2971387197870640358003695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3961849597160853810671593 2971387197870640358003695)
    ·
      refine ⟨4457080796805960537005543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971387197870640358003695 4457080796805960537005543)
      ·
        refine ⟨6685621195208940805508315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457080796805960537005543 6685621195208940805508315)
        ·
          refine ⟨10028431792813411208262473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685621195208940805508315 10028431792813411208262473)
          ·
            refine ⟨7521323844610058406196855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028431792813411208262473 7521323844610058406196855)
            ·
              refine ⟨11281985766915087609295283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521323844610058406196855 11281985766915087609295283)
              ·
                refine ⟨16922978650372631413942925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281985766915087609295283 16922978650372631413942925)
                ·
                  refine ⟨6346116993889736780228597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16922978650372631413942925 6346116993889736780228597)
                  ·
                    refine ⟨594948468177162823146431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6346116993889736780228597 594948468177162823146431)
                    ·
                      rfl

theorem cell23_3475974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3475974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475974 prefixEnd_3475974 := by exact prefixLift 3475974
  have htrace : WordTrace (prefixWord ++ tailWord_3475974) baseStart_3475974 baseEnd_3475974 := by
    simpa [prefixWord, tailWord_3475974, baseEnd_3475974] using wordTrace_append hprefix tailTrace_3475974
  have hstable : (prefixWord ++ tailWord_3475974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475974).length < 2 ^ (prefixWord ++ tailWord_3475974).sum := by decide
  have hdescent : baseEnd_3475974 < baseStart_3475974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475980 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3475980 : Nat := 118140960795 + 3475980 * 2 ^ 59
def prefixEnd_3475980 : Nat := 4983230072969 + 3 ^ 40 * 3475980 * 2
def baseEnd_3475980 : Nat := 1784848485415415445964265

theorem tailTrace_3475980 : CollatzResearch.WordTrace tailWord_3475980 prefixEnd_3475980 1784848485415415445964265 := by
  unfold tailWord_3475980
  simp only [CollatzResearch.WordTrace]
  refine ⟨63389702973562792483104697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84519603964750389977472929 63389702973562792483104697)
  ·
    refine ⟨47542277230172094362328523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63389702973562792483104697 47542277230172094362328523)
    ·
      refine ⟨71313415845258141543492785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47542277230172094362328523 71313415845258141543492785)
      ·
        refine ⟨53485061883943606157619589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71313415845258141543492785 53485061883943606157619589)
        ·
          refine ⟨10028449103239426154553673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53485061883943606157619589 10028449103239426154553673)
          ·
            refine ⟨7521336827429569615915255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028449103239426154553673 7521336827429569615915255)
            ·
              refine ⟨11282005241144354423872883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521336827429569615915255 11282005241144354423872883)
              ·
                refine ⟨16923007861716531635809325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282005241144354423872883 16923007861716531635809325)
                ·
                  refine ⟨6346127948143699363428497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16923007861716531635809325 6346127948143699363428497)
                  ·
                    refine ⟨4759595961107774522571373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6346127948143699363428497 4759595961107774522571373)
                    ·
                      refine ⟨1784848485415415445964265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759595961107774522571373 1784848485415415445964265)
                      ·
                        rfl

theorem cell23_3475980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3475980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475980 prefixEnd_3475980 := by exact prefixLift 3475980
  have htrace : WordTrace (prefixWord ++ tailWord_3475980) baseStart_3475980 baseEnd_3475980 := by
    simpa [prefixWord, tailWord_3475980, baseEnd_3475980] using wordTrace_append hprefix tailTrace_3475980
  have hstable : (prefixWord ++ tailWord_3475980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475980).length < 2 ^ (prefixWord ++ tailWord_3475980).sum := by decide
  have hdescent : baseEnd_3475980 < baseStart_3475980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475981 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3475981 : Nat := 118140960795 + 3475981 * 2 ^ 59
def prefixEnd_3475981 : Nat := 4983230072969 + 3 ^ 40 * 3475981 * 2
def baseEnd_3475981 : Nat := 1784848998896069942051761

theorem tailTrace_3475981 : CollatzResearch.WordTrace tailWord_3475981 prefixEnd_3475981 1784848998896069942051761 := by
  unfold tailWord_3475981
  simp only [CollatzResearch.WordTrace]
  refine ⟨126779442420121962136995797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84519628280081308091330531 126779442420121962136995797)
  ·
    refine ⟨2971393181721608487585839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 126779442420121962136995797 2971393181721608487585839)
    ·
      refine ⟨4457089772582412731378759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971393181721608487585839 4457089772582412731378759)
      ·
        refine ⟨6685634658873619097068139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457089772582412731378759 6685634658873619097068139)
        ·
          refine ⟨10028451988310428645602209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685634658873619097068139 10028451988310428645602209)
          ·
            refine ⟨7521338991232821484201657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028451988310428645602209 7521338991232821484201657)
            ·
              refine ⟨5641004243424616113151243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7521338991232821484201657 5641004243424616113151243)
              ·
                refine ⟨8461506365136924169726865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641004243424616113151243 8461506365136924169726865)
                ·
                  refine ⟨6346129773852693127295149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8461506365136924169726865 6346129773852693127295149)
                  ·
                    refine ⟨2379798665194759922735681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6346129773852693127295149 2379798665194759922735681)
                    ·
                      refine ⟨1784848998896069942051761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379798665194759922735681 1784848998896069942051761)
                      ·
                        rfl

theorem cell23_3475981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3475981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475981 prefixEnd_3475981 := by exact prefixLift 3475981
  have htrace : WordTrace (prefixWord ++ tailWord_3475981) baseStart_3475981 baseEnd_3475981 := by
    simpa [prefixWord, tailWord_3475981, baseEnd_3475981] using wordTrace_append hprefix tailTrace_3475981
  have hstable : (prefixWord ++ tailWord_3475981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475981).length < 2 ^ (prefixWord ++ tailWord_3475981).sum := by decide
  have hdescent : baseEnd_3475981 < baseStart_3475981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475993 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_3475993 : Nat := 118140960795 + 3475993 * 2 ^ 59
def prefixEnd_3475993 : Nat := 4983230072969 + 3 ^ 40 * 3475993 * 2
def baseEnd_3475993 : Nat := 1784855160663923895101705

theorem tailTrace_3475993 : CollatzResearch.WordTrace tailWord_3475993 prefixEnd_3475993 1784855160663923895101705 := by
  unfold tailWord_3475993
  simp only [CollatzResearch.WordTrace]
  refine ⟨126779880096078488186432633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84519920064052325457621755 126779880096078488186432633)
  ·
    refine ⟨95084910072058866139824475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126779880096078488186432633 95084910072058866139824475)
    ·
      refine ⟨142627365108088299209736713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95084910072058866139824475 142627365108088299209736713)
      ·
        refine ⟨106970523831066224407302535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142627365108088299209736713 106970523831066224407302535)
        ·
          refine ⟨160455785746599336610953803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106970523831066224407302535 160455785746599336610953803)
          ·
            refine ⟨240683678619899004916430705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160455785746599336610953803 240683678619899004916430705)
            ·
              refine ⟨180512758964924253687323029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240683678619899004916430705 180512758964924253687323029)
              ·
                refine ⟨8461535576480824391593267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180512758964924253687323029 8461535576480824391593267)
                ·
                  refine ⟨12692303364721236587389901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8461535576480824391593267 12692303364721236587389901)
                  ·
                    refine ⟨4759613761770463720271213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12692303364721236587389901 4759613761770463720271213)
                    ·
                      refine ⟨1784855160663923895101705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759613761770463720271213 1784855160663923895101705)
                      ·
                        rfl

theorem cell23_3475993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_3475993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3475993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3475993 prefixEnd_3475993 := by exact prefixLift 3475993
  have htrace : WordTrace (prefixWord ++ tailWord_3475993) baseStart_3475993 baseEnd_3475993 := by
    simpa [prefixWord, tailWord_3475993, baseEnd_3475993] using wordTrace_append hprefix tailTrace_3475993
  have hstable : (prefixWord ++ tailWord_3475993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475993).length < 2 ^ (prefixWord ++ tailWord_3475993).sum := by decide
  have hdescent : baseEnd_3475993 < baseStart_3475993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476004 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_3476004 : Nat := 118140960795 + 3476004 * 2 ^ 59
def prefixEnd_3476004 : Nat := 4983230072969 + 3 ^ 40 * 3476004 * 2
def baseEnd_3476004 : Nat := 594953602983707784021385

theorem tailTrace_3476004 : CollatzResearch.WordTrace tailWord_3476004 prefixEnd_3476004 594953602983707784021385 := by
  unfold tailWord_3476004
  simp only [CollatzResearch.WordTrace]
  refine ⟨63390140649519318532541533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84520187532692424710055377 63390140649519318532541533)
  ·
    refine ⟨23771302743569744449703075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63390140649519318532541533 23771302743569744449703075)
    ·
      refine ⟨35656954115354616674554613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23771302743569744449703075 35656954115354616674554613)
      ·
        refine ⟨3342839448314495313239495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35656954115354616674554613 3342839448314495313239495)
        ·
          refine ⟨5014259172471742969859243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342839448314495313239495 5014259172471742969859243)
          ·
            refine ⟨7521388758707614454788865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014259172471742969859243 7521388758707614454788865)
            ·
              refine ⟨5641041569030710841091649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7521388758707614454788865 5641041569030710841091649)
              ·
                refine ⟨4230781176773033130818737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641041569030710841091649 4230781176773033130818737)
                ·
                  refine ⟨3173085882579774848114053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4230781176773033130818737 3173085882579774848114053)
                  ·
                    refine ⟨594953602983707784021385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173085882579774848114053 594953602983707784021385)
                    ·
                      rfl

theorem cell23_3476004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_3476004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476004 prefixEnd_3476004 := by exact prefixLift 3476004
  have htrace : WordTrace (prefixWord ++ tailWord_3476004) baseStart_3476004 baseEnd_3476004 := by
    simpa [prefixWord, tailWord_3476004, baseEnd_3476004] using wordTrace_append hprefix tailTrace_3476004
  have hstable : (prefixWord ++ tailWord_3476004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476004).length < 2 ^ (prefixWord ++ tailWord_3476004).sum := by decide
  have hdescent : baseEnd_3476004 < baseStart_3476004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476053 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3476053 : Nat := 118140960795 + 3476053 * 2 ^ 59
def prefixEnd_3476053 : Nat := 4983230072969 + 3 ^ 40 * 3476053 * 2
def baseEnd_3476053 : Nat := 1784885969503193660351429

theorem tailTrace_3476053 : CollatzResearch.WordTrace tailWord_3476053 prefixEnd_3476053 1784885969503193660351429 := by
  unfold tailWord_3476053
  simp only [CollatzResearch.WordTrace]
  refine ⟨126782068475861118433616813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84521378983907412289077875 126782068475861118433616813)
  ·
    refine ⟨47543275678447919412606305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126782068475861118433616813 47543275678447919412606305)
    ·
      refine ⟨35657456758835939559454729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47543275678447919412606305 35657456758835939559454729)
      ·
        refine ⟨26743092569126954669591047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35657456758835939559454729 26743092569126954669591047)
        ·
          refine ⟨40114638853690432004386571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743092569126954669591047 40114638853690432004386571)
          ·
            refine ⟨60171958280535648006579857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40114638853690432004386571 60171958280535648006579857)
            ·
              refine ⟨45128968710401736004934893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60171958280535648006579857 45128968710401736004934893)
              ·
                refine ⟨16923363266400651001850585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45128968710401736004934893 16923363266400651001850585)
                ·
                  refine ⟨12692522449800488251387939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16923363266400651001850585 12692522449800488251387939)
                  ·
                    refine ⟨19038783674700732377081909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12692522449800488251387939 19038783674700732377081909)
                    ·
                      refine ⟨1784885969503193660351429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19038783674700732377081909 1784885969503193660351429)
                      ·
                        rfl

theorem cell23_3476053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3476053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476053 prefixEnd_3476053 := by exact prefixLift 3476053
  have htrace : WordTrace (prefixWord ++ tailWord_3476053) baseStart_3476053 baseEnd_3476053 := by
    simpa [prefixWord, tailWord_3476053, baseEnd_3476053] using wordTrace_append hprefix tailTrace_3476053
  have hstable : (prefixWord ++ tailWord_3476053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476053).length < 2 ^ (prefixWord ++ tailWord_3476053).sum := by decide
  have hdescent : baseEnd_3476053 < baseStart_3476053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476067 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 4, 2, 2]
def baseStart_3476067 : Nat := 118140960795 + 3476067 * 2 ^ 59
def prefixEnd_3476067 : Nat := 4983230072969 + 3 ^ 40 * 3476067 * 2
def baseEnd_3476067 : Nat := 1784893158232356605576365

theorem tailTrace_3476067 : CollatzResearch.WordTrace tailWord_3476067 prefixEnd_3476067 1784893158232356605576365 := by
  unfold tailWord_3476067
  simp only [CollatzResearch.WordTrace]
  refine ⟨126782579097810398824626455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84521719398540265883084303 126782579097810398824626455)
  ·
    refine ⟨190173868646715598236939683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126782579097810398824626455 190173868646715598236939683)
    ·
      refine ⟨285260802970073397355409525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190173868646715598236939683 285260802970073397355409525)
      ·
        refine ⟨26743200278444381002069643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285260802970073397355409525 26743200278444381002069643)
        ·
          refine ⟨40114800417666571503104465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743200278444381002069643 40114800417666571503104465)
          ·
            refine ⟨30086100313249928627328349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40114800417666571503104465 30086100313249928627328349)
            ·
              refine ⟨11282287617468723235248131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30086100313249928627328349 11282287617468723235248131)
              ·
                refine ⟨16923431426203084852872197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282287617468723235248131 16923431426203084852872197)
                ·
                  refine ⟨3173143392413078409913537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16923431426203084852872197 3173143392413078409913537)
                  ·
                    refine ⟨2379857544309808807435153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173143392413078409913537 2379857544309808807435153)
                    ·
                      refine ⟨1784893158232356605576365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379857544309808807435153 1784893158232356605576365)
                      ·
                        rfl

theorem cell23_3476067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_3476067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476067 prefixEnd_3476067 := by exact prefixLift 3476067
  have htrace : WordTrace (prefixWord ++ tailWord_3476067) baseStart_3476067 baseEnd_3476067 := by
    simpa [prefixWord, tailWord_3476067, baseEnd_3476067] using wordTrace_append hprefix tailTrace_3476067
  have hstable : (prefixWord ++ tailWord_3476067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476067).length < 2 ^ (prefixWord ++ tailWord_3476067).sum := by decide
  have hdescent : baseEnd_3476067 < baseStart_3476067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476083 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 3]
def baseStart_3476083 : Nat := 118140960795 + 3476083 * 2 ^ 59
def prefixEnd_3476083 : Nat := 4983230072969 + 3 ^ 40 * 3476083 * 2
def baseEnd_3476083 : Nat := 1784901373922828542976291

theorem tailTrace_3476083 : CollatzResearch.WordTrace tailWord_3476083 prefixEnd_3476083 1784901373922828542976291 := by
  unfold tailWord_3476083
  simp only [CollatzResearch.WordTrace]
  refine ⟨126783162665752433557208903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84522108443834955704805935 126783162665752433557208903)
  ·
    refine ⟨190174743998628650335813355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126783162665752433557208903 190174743998628650335813355)
    ·
      refine ⟨285262115997942975503720033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190174743998628650335813355 285262115997942975503720033)
      ·
        refine ⟨213946586998457231627790025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285262115997942975503720033 213946586998457231627790025)
        ·
          refine ⟨160459940248842923720842519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213946586998457231627790025 160459940248842923720842519)
          ·
            refine ⟨240689910373264385581263779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160459940248842923720842519 240689910373264385581263779)
            ·
              refine ⟨361034865559896578371895669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240689910373264385581263779 361034865559896578371895669)
              ·
                refine ⟨33847018646240304222365219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361034865559896578371895669 33847018646240304222365219)
                ·
                  refine ⟨50770527969360456333547829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33847018646240304222365219 50770527969360456333547829)
                  ·
                    refine ⟨4759736997127542781270109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50770527969360456333547829 4759736997127542781270109)
                    ·
                      refine ⟨1784901373922828542976291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759736997127542781270109 1784901373922828542976291)
                      ·
                        rfl

theorem cell23_3476083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_3476083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476083 prefixEnd_3476083 := by exact prefixLift 3476083
  have htrace : WordTrace (prefixWord ++ tailWord_3476083) baseStart_3476083 baseEnd_3476083 := by
    simpa [prefixWord, tailWord_3476083, baseEnd_3476083] using wordTrace_append hprefix tailTrace_3476083
  have hstable : (prefixWord ++ tailWord_3476083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476083).length < 2 ^ (prefixWord ++ tailWord_3476083).sum := by decide
  have hdescent : baseEnd_3476083 < baseStart_3476083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476103 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 1, 7]
def baseStart_3476103 : Nat := 118140960795 + 3476103 * 2 ^ 59
def prefixEnd_3476103 : Nat := 4983230072969 + 3 ^ 40 * 3476103 * 2
def baseEnd_3476103 : Nat := 594970547845306154908733

theorem tailTrace_3476103 : CollatzResearch.WordTrace tailWord_3476103 prefixEnd_3476103 594970547845306154908733 := by
  unfold tailWord_3476103
  simp only [CollatzResearch.WordTrace]
  refine ⟨126783892125679976972936963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84522594750453317981957975 126783892125679976972936963)
  ·
    refine ⟨190175838188519965459405445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126783892125679976972936963 190175838188519965459405445)
    ·
      refine ⟨35657969660347493523638521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190175838188519965459405445 35657969660347493523638521)
      ·
        refine ⟨26743477245260620142728891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35657969660347493523638521 26743477245260620142728891)
        ·
          refine ⟨40115215867890930214093337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743477245260620142728891 40115215867890930214093337)
          ·
            refine ⟨30086411900918197660570003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40115215867890930214093337 30086411900918197660570003)
            ·
              refine ⟨45129617851377296490855005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30086411900918197660570003 45129617851377296490855005)
              ·
                refine ⟨16923606694266486184070627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45129617851377296490855005 16923606694266486184070627)
                ·
                  refine ⟨25385410041399729276105941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16923606694266486184070627 25385410041399729276105941)
                  ·
                    refine ⟨594970547845306154908733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25385410041399729276105941 594970547845306154908733)
                    ·
                      rfl

theorem cell23_3476103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_3476103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476103 prefixEnd_3476103 := by exact prefixLift 3476103
  have htrace : WordTrace (prefixWord ++ tailWord_3476103) baseStart_3476103 baseEnd_3476103 := by
    simpa [prefixWord, tailWord_3476103, baseEnd_3476103] using wordTrace_append hprefix tailTrace_3476103
  have hstable : (prefixWord ++ tailWord_3476103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476103).length < 2 ^ (prefixWord ++ tailWord_3476103).sum := by decide
  have hdescent : baseEnd_3476103 < baseStart_3476103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476120 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_3476120 : Nat := 118140960795 + 3476120 * 2 ^ 59
def prefixEnd_3476120 : Nat := 4983230072969 + 3 ^ 40 * 3476120 * 2
def baseEnd_3476120 : Nat := 594973457569014966071207

theorem tailTrace_3476120 : CollatzResearch.WordTrace tailWord_3476120 prefixEnd_3476120 594973457569014966071207 := by
  unfold tailWord_3476120
  simp only [CollatzResearch.WordTrace]
  refine ⟨63392256083309194438152907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84523008111078925917537209 63392256083309194438152907)
  ·
    refine ⟨95088384124963791657229361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63392256083309194438152907 95088384124963791657229361)
    ·
      refine ⟨71316288093722843742922021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95088384124963791657229361 71316288093722843742922021)
      ·
        refine ⟨13371804017573033201797879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71316288093722843742922021 13371804017573033201797879)
        ·
          refine ⟨20057706026359549802696819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13371804017573033201797879 20057706026359549802696819)
          ·
            refine ⟨30086559039539324704045229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20057706026359549802696819 30086559039539324704045229)
            ·
              refine ⟨11282459639827246764016961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30086559039539324704045229 11282459639827246764016961)
              ·
                refine ⟨8461844729870435073012721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11282459639827246764016961 8461844729870435073012721)
                ·
                  refine ⟨6346383547402826304759541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8461844729870435073012721 6346383547402826304759541)
                  ·
                    refine ⟨594973457569014966071207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6346383547402826304759541 594973457569014966071207)
                    ·
                      rfl

theorem cell23_3476120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_3476120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476120 prefixEnd_3476120 := by exact prefixLift 3476120
  have htrace : WordTrace (prefixWord ++ tailWord_3476120) baseStart_3476120 baseEnd_3476120 := by
    simpa [prefixWord, tailWord_3476120, baseEnd_3476120] using wordTrace_append hprefix tailTrace_3476120
  have hstable : (prefixWord ++ tailWord_3476120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476120).length < 2 ^ (prefixWord ++ tailWord_3476120).sum := by decide
  have hdescent : baseEnd_3476120 < baseStart_3476120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476124 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 5]
def baseStart_3476124 : Nat := 118140960795 + 3476124 * 2 ^ 59
def prefixEnd_3476124 : Nat := 4983230072969 + 3 ^ 40 * 3476124 * 2
def baseEnd_3476124 : Nat := 198324714069962542507067

theorem tailTrace_3476124 : CollatzResearch.WordTrace tailWord_3476124 prefixEnd_3476124 198324714069962542507067 := by
  unfold tailWord_3476124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63392329029301948779725713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84523105372402598372967617 63392329029301948779725713)
  ·
    refine ⟨47544246771976461584794285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63392329029301948779725713 47544246771976461584794285)
    ·
      refine ⟨17829092539491173094297857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47544246771976461584794285 17829092539491173094297857)
      ·
        refine ⟨13371819404618379820723393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17829092539491173094297857 13371819404618379820723393)
        ·
          refine ⟨10028864553463784865542545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13371819404618379820723393 10028864553463784865542545)
          ·
            refine ⟨7521648415097838649156909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028864553463784865542545 7521648415097838649156909)
            ·
              refine ⟨2820618155661689493433841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7521648415097838649156909 2820618155661689493433841)
              ·
                refine ⟨2115463616746267120075381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820618155661689493433841 2115463616746267120075381)
                ·
                  refine ⟨198324714069962542507067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2115463616746267120075381 198324714069962542507067)
                  ·
                    rfl

theorem cell23_3476124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_3476124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476124 prefixEnd_3476124 := by exact prefixLift 3476124
  have htrace : WordTrace (prefixWord ++ tailWord_3476124) baseStart_3476124 baseEnd_3476124 := by
    simpa [prefixWord, tailWord_3476124, baseEnd_3476124] using wordTrace_append hprefix tailTrace_3476124
  have hstable : (prefixWord ++ tailWord_3476124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476124).length < 2 ^ (prefixWord ++ tailWord_3476124).sum := by decide
  have hdescent : baseEnd_3476124 < baseStart_3476124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476135 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3476135 : Nat := 118140960795 + 3476135 * 2 ^ 59
def prefixEnd_3476135 : Nat := 4983230072969 + 3 ^ 40 * 3476135 * 2
def baseEnd_3476135 : Nat := 1784928074916862339526053

theorem tailTrace_3476135 : CollatzResearch.WordTrace tailWord_3476135 prefixEnd_3476135 1784928074916862339526053 := by
  unfold tailWord_3476135
  simp only [CollatzResearch.WordTrace]
  refine ⟨126785059261564046438101859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84523372841042697625401239 126785059261564046438101859)
  ·
    refine ⟨190177588892346069657152789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126785059261564046438101859 190177588892346069657152789)
    ·
      refine ⟨8914574479328722015179037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190177588892346069657152789 8914574479328722015179037)
      ·
        refine ⟨3342965429748270755692139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8914574479328722015179037 3342965429748270755692139)
        ·
          refine ⟨5014448144622406133538209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342965429748270755692139 5014448144622406133538209)
          ·
            refine ⟨3760836108466804600153657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014448144622406133538209 3760836108466804600153657)
            ·
              refine ⟨2820627081350103450115243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3760836108466804600153657 2820627081350103450115243)
              ·
                refine ⟨4230940622025155175172865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820627081350103450115243 4230940622025155175172865)
                ·
                  refine ⟨3173205466518866381379649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4230940622025155175172865 3173205466518866381379649)
                  ·
                    refine ⟨2379904099889149786034737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173205466518866381379649 2379904099889149786034737)
                    ·
                      refine ⟨1784928074916862339526053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2379904099889149786034737 1784928074916862339526053)
                      ·
                        rfl

theorem cell23_3476135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3476135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476135 prefixEnd_3476135 := by exact prefixLift 3476135
  have htrace : WordTrace (prefixWord ++ tailWord_3476135) baseStart_3476135 baseEnd_3476135 := by
    simpa [prefixWord, tailWord_3476135, baseEnd_3476135] using wordTrace_append hprefix tailTrace_3476135
  have hstable : (prefixWord ++ tailWord_3476135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476135).length < 2 ^ (prefixWord ++ tailWord_3476135).sum := by decide
  have hdescent : baseEnd_3476135 < baseStart_3476135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476153 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3476153 : Nat := 118140960795 + 3476153 * 2 ^ 59
def prefixEnd_3476153 : Nat := 4983230072969 + 3 ^ 40 * 3476153 * 2
def baseEnd_3476153 : Nat := 1784937317568643269100969

theorem tailTrace_3476153 : CollatzResearch.WordTrace tailWord_3476153 prefixEnd_3476153 1784937317568643269100969 := by
  unfold tailWord_3476153
  simp only [CollatzResearch.WordTrace]
  refine ⟨126785715775498835512257113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84523810516999223674838075 126785715775498835512257113)
  ·
    refine ⟨95089286831624126634192835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126785715775498835512257113 95089286831624126634192835)
    ·
      refine ⟨142633930247436189951289253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95089286831624126634192835 142633930247436189951289253)
      ·
        refine ⟨26743861921394285615866735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142633930247436189951289253 26743861921394285615866735)
        ·
          refine ⟨40115792882091428423800103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743861921394285615866735 40115792882091428423800103)
          ·
            refine ⟨60173689323137142635700155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40115792882091428423800103 60173689323137142635700155)
            ·
              refine ⟨90260533984705713953550233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60173689323137142635700155 90260533984705713953550233)
              ·
                refine ⟨67695400488529285465162675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90260533984705713953550233 67695400488529285465162675)
                ·
                  refine ⟨101543100732793928197744013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67695400488529285465162675 101543100732793928197744013)
                  ·
                    refine ⟨38078662774797723074154005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101543100732793928197744013 38078662774797723074154005)
                    ·
                      refine ⟨1784937317568643269100969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38078662774797723074154005 1784937317568643269100969)
                      ·
                        rfl

theorem cell23_3476153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3476153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476153 prefixEnd_3476153 := by exact prefixLift 3476153
  have htrace : WordTrace (prefixWord ++ tailWord_3476153) baseStart_3476153 baseEnd_3476153 := by
    simpa [prefixWord, tailWord_3476153, baseEnd_3476153] using wordTrace_append hprefix tailTrace_3476153
  have hstable : (prefixWord ++ tailWord_3476153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476153).length < 2 ^ (prefixWord ++ tailWord_3476153).sum := by decide
  have hdescent : baseEnd_3476153 < baseStart_3476153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476157 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3476157 : Nat := 118140960795 + 3476157 * 2 ^ 59
def prefixEnd_3476157 : Nat := 4983230072969 + 3 ^ 40 * 3476157 * 2
def baseEnd_3476157 : Nat := 1784939371491261253450951

theorem tailTrace_3476157 : CollatzResearch.WordTrace tailWord_3476157 prefixEnd_3476157 1784939371491261253450951 := by
  unfold tailWord_3476157
  simp only [CollatzResearch.WordTrace]
  refine ⟨126785861667484344195402725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84523907778322896130268483 126785861667484344195402725)
  ·
    refine ⟨23772349062653314536638011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126785861667484344195402725 23772349062653314536638011)
    ·
      refine ⟨35658523593979971804957017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23772349062653314536638011 35658523593979971804957017)
      ·
        refine ⟨26743892695484978853717763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35658523593979971804957017 26743892695484978853717763)
        ·
          refine ⟨40115839043227468280576645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743892695484978853717763 40115839043227468280576645)
          ·
            refine ⟨7521719820605150302608121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40115839043227468280576645 7521719820605150302608121)
            ·
              refine ⟨5641289865453862726956091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7521719820605150302608121 5641289865453862726956091)
              ·
                refine ⟨8461934798180794090434137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641289865453862726956091 8461934798180794090434137)
                ·
                  refine ⟨6346451098635595567825603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8461934798180794090434137 6346451098635595567825603)
                  ·
                    refine ⟨9519676647953393351738405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6346451098635595567825603 9519676647953393351738405)
                    ·
                      refine ⟨1784939371491261253450951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9519676647953393351738405 1784939371491261253450951)
                      ·
                        rfl

theorem cell23_3476157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3476157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476157 prefixEnd_3476157 := by exact prefixLift 3476157
  have htrace : WordTrace (prefixWord ++ tailWord_3476157) baseStart_3476157 baseEnd_3476157 := by
    simpa [prefixWord, tailWord_3476157, baseEnd_3476157] using wordTrace_append hprefix tailTrace_3476157
  have hstable : (prefixWord ++ tailWord_3476157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476157).length < 2 ^ (prefixWord ++ tailWord_3476157).sum := by decide
  have hdescent : baseEnd_3476157 < baseStart_3476157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476184 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 1, 4]
def baseStart_3476184 : Nat := 118140960795 + 3476184 * 2 ^ 59
def prefixEnd_3476184 : Nat := 4983230072969 + 3 ^ 40 * 3476184 * 2
def baseEnd_3476184 : Nat := 594984411822977549271109

theorem tailTrace_3476184 : CollatzResearch.WordTrace tailWord_3476184 prefixEnd_3476184 594984411822977549271109 := by
  unfold tailWord_3476184
  simp only [CollatzResearch.WordTrace]
  refine ⟨63393423219193263903317803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84524564292257685204423737 63393423219193263903317803)
  ·
    refine ⟨95090134828789895854976705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63393423219193263903317803 95090134828789895854976705)
    ·
      refine ⟨71317601121592421891232529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95090134828789895854976705 71317601121592421891232529)
      ·
        refine ⟨53488200841194316418424397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71317601121592421891232529 53488200841194316418424397)
        ·
          refine ⟨20058075315447868656909149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53488200841194316418424397 20058075315447868656909149)
          ·
            refine ⟨7521778243292950746340931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20058075315447868656909149 7521778243292950746340931)
            ·
              refine ⟨11282667364939426119511397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521778243292950746340931 11282667364939426119511397)
              ·
                refine ⟨2115500130926142397408387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11282667364939426119511397 2115500130926142397408387)
                ·
                  refine ⟨3173250196389213596112581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115500130926142397408387 3173250196389213596112581)
                  ·
                    refine ⟨594984411822977549271109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173250196389213596112581 594984411822977549271109)
                    ·
                      rfl

theorem cell23_3476184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_3476184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476184 prefixEnd_3476184 := by exact prefixLift 3476184
  have htrace : WordTrace (prefixWord ++ tailWord_3476184) baseStart_3476184 baseEnd_3476184 := by
    simpa [prefixWord, tailWord_3476184, baseEnd_3476184] using wordTrace_append hprefix tailTrace_3476184
  have hstable : (prefixWord ++ tailWord_3476184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476184).length < 2 ^ (prefixWord ++ tailWord_3476184).sum := by decide
  have hdescent : baseEnd_3476184 < baseStart_3476184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476203 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_3476203 : Nat := 118140960795 + 3476203 * 2 ^ 59
def prefixEnd_3476203 : Nat := 4983230072969 + 3 ^ 40 * 3476203 * 2
def baseEnd_3476203 : Nat := 1784962991601368073475739

theorem tailTrace_3476203 : CollatzResearch.WordTrace tailWord_3476203 prefixEnd_3476203 1784962991601368073475739 := by
  unfold tailWord_3476203
  simp only [CollatzResearch.WordTrace]
  refine ⟨126787539425317694051577263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84525026283545129367718175 126787539425317694051577263)
  ·
    refine ⟨190181309137976541077365895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126787539425317694051577263 190181309137976541077365895)
    ·
      refine ⟨285271963706964811616048843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190181309137976541077365895 285271963706964811616048843)
      ·
        refine ⟨427907945560447217424073265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285271963706964811616048843 427907945560447217424073265)
        ·
          refine ⟨320930959170335413068054949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427907945560447217424073265 320930959170335413068054949)
          ·
            refine ⟨60174554844437889950260303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320930959170335413068054949 60174554844437889950260303)
            ·
              refine ⟨90261832266656834925390455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60174554844437889950260303 90261832266656834925390455)
              ·
                refine ⟨135392748399985252388085683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90261832266656834925390455 135392748399985252388085683)
                ·
                  refine ⟨203089122599977878582128525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135392748399985252388085683 203089122599977878582128525)
                  ·
                    refine ⟨76158420974991704468298197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203089122599977878582128525 76158420974991704468298197)
                    ·
                      refine ⟨1784962991601368073475739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76158420974991704468298197 1784962991601368073475739)
                      ·
                        rfl

theorem cell23_3476203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_3476203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476203 prefixEnd_3476203 := by exact prefixLift 3476203
  have htrace : WordTrace (prefixWord ++ tailWord_3476203) baseStart_3476203 baseEnd_3476203 := by
    simpa [prefixWord, tailWord_3476203, baseEnd_3476203] using wordTrace_append hprefix tailTrace_3476203
  have hstable : (prefixWord ++ tailWord_3476203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476203).length < 2 ^ (prefixWord ++ tailWord_3476203).sum := by decide
  have hdescent : baseEnd_3476203 < baseStart_3476203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476207 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 3]
def baseStart_3476207 : Nat := 118140960795 + 3476207 * 2 ^ 59
def prefixEnd_3476207 : Nat := 4983230072969 + 3 ^ 40 * 3476207 * 2
def baseEnd_3476207 : Nat := 1784965045523986057825721

theorem tailTrace_3476207 : CollatzResearch.WordTrace tailWord_3476207 prefixEnd_3476207 1784965045523986057825721 := by
  unfold tailWord_3476207
  simp only [CollatzResearch.WordTrace]
  refine ⟨126787685317303202734722875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84525123544868801823148583 126787685317303202734722875)
  ·
    refine ⟨190181527975954804102084313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126787685317303202734722875 190181527975954804102084313)
    ·
      refine ⟨142636145981966103076563235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190181527975954804102084313 142636145981966103076563235)
      ·
        refine ⟨213954218972949154614844853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142636145981966103076563235 213954218972949154614844853)
        ·
          refine ⟨20058208028713983245141705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213954218972949154614844853 20058208028713983245141705)
          ·
            refine ⟨15043656021535487433856279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20058208028713983245141705 15043656021535487433856279)
            ·
              refine ⟨22565484032303231150784419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15043656021535487433856279 22565484032303231150784419)
              ·
                refine ⟨33848226048454846726176629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22565484032303231150784419 33848226048454846726176629)
                ·
                  refine ⟨3173271192042641880579059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33848226048454846726176629 3173271192042641880579059)
                  ·
                    refine ⟨4759906788063962820868589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173271192042641880579059 4759906788063962820868589)
                    ·
                      refine ⟨1784965045523986057825721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759906788063962820868589 1784965045523986057825721)
                      ·
                        rfl

theorem cell23_3476207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_3476207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476207 prefixEnd_3476207 := by exact prefixLift 3476207
  have htrace : WordTrace (prefixWord ++ tailWord_3476207) baseStart_3476207 baseEnd_3476207 := by
    simpa [prefixWord, tailWord_3476207, baseEnd_3476207] using wordTrace_append hprefix tailTrace_3476207
  have hstable : (prefixWord ++ tailWord_3476207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476207).length < 2 ^ (prefixWord ++ tailWord_3476207).sum := by decide
  have hdescent : baseEnd_3476207 < baseStart_3476207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476264 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3476264 : Nat := 118140960795 + 3476264 * 2 ^ 59
def prefixEnd_3476264 : Nat := 4983230072969 + 3 ^ 40 * 3476264 * 2
def baseEnd_3476264 : Nat := 1784994313921292334812959

theorem tailTrace_3476264 : CollatzResearch.WordTrace tailWord_3476264 prefixEnd_3476264 1784994313921292334812959 := by
  unfold tailWord_3476264
  simp only [CollatzResearch.WordTrace]
  refine ⟨63394882139048350734773923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84526509518731134313031897 63394882139048350734773923)
  ·
    refine ⟨95092323208572526102160885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63394882139048350734773923 95092323208572526102160885)
    ·
      refine ⟨8914905300803674322077583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95092323208572526102160885 8914905300803674322077583)
      ·
        refine ⟨13372357951205511483116375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914905300803674322077583 13372357951205511483116375)
        ·
          refine ⟨20058536926808267224674563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13372357951205511483116375 20058536926808267224674563)
          ·
            refine ⟨30087805390212400837011845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20058536926808267224674563 30087805390212400837011845)
            ·
              refine ⟨5641463510664825156939721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30087805390212400837011845 5641463510664825156939721)
              ·
                refine ⟨4231097632998618867704791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641463510664825156939721 4231097632998618867704791)
                ·
                  refine ⟨6346646449497928301557187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231097632998618867704791 6346646449497928301557187)
                  ·
                    refine ⟨9519969674246892452335781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6346646449497928301557187 9519969674246892452335781)
                    ·
                      refine ⟨1784994313921292334812959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9519969674246892452335781 1784994313921292334812959)
                      ·
                        rfl

theorem cell23_3476264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3476264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476264 prefixEnd_3476264 := by exact prefixLift 3476264
  have htrace : WordTrace (prefixWord ++ tailWord_3476264) baseStart_3476264 baseEnd_3476264 := by
    simpa [prefixWord, tailWord_3476264, baseEnd_3476264] using wordTrace_append hprefix tailTrace_3476264
  have hstable : (prefixWord ++ tailWord_3476264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476264).length < 2 ^ (prefixWord ++ tailWord_3476264).sum := by decide
  have hdescent : baseEnd_3476264 < baseStart_3476264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476267 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 3]
def baseStart_3476267 : Nat := 118140960795 + 3476267 * 2 ^ 59
def prefixEnd_3476267 : Nat := 4983230072969 + 3 ^ 40 * 3476267 * 2
def baseEnd_3476267 : Nat := 1784995854363255823075445

theorem tailTrace_3476267 : CollatzResearch.WordTrace tailWord_3476267 prefixEnd_3476267 1784995854363255823075445 := by
  unfold tailWord_3476267
  simp only [CollatzResearch.WordTrace]
  refine ⟨126789873697085832981907055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84526582464723888654604703 126789873697085832981907055)
  ·
    refine ⟨190184810545628749472860583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126789873697085832981907055 190184810545628749472860583)
    ·
      refine ⟨285277215818443124209290875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190184810545628749472860583 285277215818443124209290875)
      ·
        refine ⟨427915823727664686313936313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285277215818443124209290875 427915823727664686313936313)
        ·
          refine ⟨320936867795748514735452235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427915823727664686313936313 320936867795748514735452235)
          ·
            refine ⟨481405301693622772103178353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320936867795748514735452235 481405301693622772103178353)
            ·
              refine ⟨361053976270217079077383765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481405301693622772103178353 361053976270217079077383765)
              ·
                refine ⟨4231101284416606395438091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 361053976270217079077383765 4231101284416606395438091)
                ·
                  refine ⟨6346651926624909593157137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231101284416606395438091 6346651926624909593157137)
                  ·
                    refine ⟨4759988944968682194867853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6346651926624909593157137 4759988944968682194867853)
                    ·
                      refine ⟨1784995854363255823075445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4759988944968682194867853 1784995854363255823075445)
                      ·
                        rfl

theorem cell23_3476267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 3].length) (baseStart_3476267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476267 prefixEnd_3476267 := by exact prefixLift 3476267
  have htrace : WordTrace (prefixWord ++ tailWord_3476267) baseStart_3476267 baseEnd_3476267 := by
    simpa [prefixWord, tailWord_3476267, baseEnd_3476267] using wordTrace_append hprefix tailTrace_3476267
  have hstable : (prefixWord ++ tailWord_3476267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476267).length < 2 ^ (prefixWord ++ tailWord_3476267).sum := by decide
  have hdescent : baseEnd_3476267 < baseStart_3476267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476292 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3476292 : Nat := 118140960795 + 3476292 * 2 ^ 59
def prefixEnd_3476292 : Nat := 4983230072969 + 3 ^ 40 * 3476292 * 2
def baseEnd_3476292 : Nat := 1785008691379618225262831

theorem tailTrace_3476292 : CollatzResearch.WordTrace tailWord_3476292 prefixEnd_3476292 1785008691379618225262831 := by
  unfold tailWord_3476292
  simp only [CollatzResearch.WordTrace]
  refine ⟨63395392760997631125783565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84527190347996841501044753 63395392760997631125783565)
  ·
    refine ⟨23773272285374111672168837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63395392760997631125783565 23773272285374111672168837)
    ·
      refine ⟨4457488553507645938531657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23773272285374111672168837 4457488553507645938531657)
      ·
        refine ⟨3343116415130734453898743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4457488553507645938531657 3343116415130734453898743)
        ·
          refine ⟨5014674622696101680848115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343116415130734453898743 5014674622696101680848115)
          ·
            refine ⟨7522011934044152521272173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014674622696101680848115 7522011934044152521272173)
            ·
              refine ⟨2820754475266557195477065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7522011934044152521272173 2820754475266557195477065)
              ·
                refine ⟨2115565856449917896607799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820754475266557195477065 2115565856449917896607799)
                ·
                  refine ⟨3173348784674876844911699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115565856449917896607799 3173348784674876844911699)
                  ·
                    refine ⟨4760023177012315267367549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173348784674876844911699 4760023177012315267367549)
                    ·
                      refine ⟨1785008691379618225262831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4760023177012315267367549 1785008691379618225262831)
                      ·
                        rfl

theorem cell23_3476292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3476292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476292 prefixEnd_3476292 := by exact prefixLift 3476292
  have htrace : WordTrace (prefixWord ++ tailWord_3476292) baseStart_3476292 baseEnd_3476292 := by
    simpa [prefixWord, tailWord_3476292, baseEnd_3476292] using wordTrace_append hprefix tailTrace_3476292
  have hstable : (prefixWord ++ tailWord_3476292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476292).length < 2 ^ (prefixWord ++ tailWord_3476292).sum := by decide
  have hdescent : baseEnd_3476292 < baseStart_3476292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476308 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_3476308 : Nat := 118140960795 + 3476308 * 2 ^ 59
def prefixEnd_3476308 : Nat := 4983230072969 + 3 ^ 40 * 3476308 * 2
def baseEnd_3476308 : Nat := 595005635690030054220919

theorem tailTrace_3476308 : CollatzResearch.WordTrace tailWord_3476308 prefixEnd_3476308 595005635690030054220919 := by
  unfold tailWord_3476308
  simp only [CollatzResearch.WordTrace]
  refine ⟨63395684544968648492074789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84527579393291531322766385 63395684544968648492074789)
  ·
    refine ⟨11886690852181621592264023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63395684544968648492074789 11886690852181621592264023)
    ·
      refine ⟨17830036278272432388396035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11886690852181621592264023 17830036278272432388396035)
      ·
        refine ⟨26745054417408648582594053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17830036278272432388396035 26745054417408648582594053)
        ·
          refine ⟨5014697703264121609236385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26745054417408648582594053 5014697703264121609236385)
          ·
            refine ⟨3761023277448091206927289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014697703264121609236385 3761023277448091206927289)
            ·
              refine ⟨2820767458086068405195467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761023277448091206927289 2820767458086068405195467)
              ·
                refine ⟨4231151187129102607793201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820767458086068405195467 4231151187129102607793201)
                ·
                  refine ⟨3173363390346826955844901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231151187129102607793201 3173363390346826955844901)
                  ·
                    refine ⟨595005635690030054220919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173363390346826955844901 595005635690030054220919)
                    ·
                      rfl

theorem cell23_3476308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_3476308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476308 prefixEnd_3476308 := by exact prefixLift 3476308
  have htrace : WordTrace (prefixWord ++ tailWord_3476308) baseStart_3476308 baseEnd_3476308 := by
    simpa [prefixWord, tailWord_3476308, baseEnd_3476308] using wordTrace_append hprefix tailTrace_3476308
  have hstable : (prefixWord ++ tailWord_3476308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476308).length < 2 ^ (prefixWord ++ tailWord_3476308).sum := by decide
  have hdescent : baseEnd_3476308 < baseStart_3476308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476357 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_3476357 : Nat := 118140960795 + 3476357 * 2 ^ 59
def prefixEnd_3476357 : Nat := 4983230072969 + 3 ^ 40 * 3476357 * 2
def baseEnd_3476357 : Nat := 1785042067622160470950031

theorem tailTrace_3476357 : CollatzResearch.WordTrace tailWord_3476357 prefixEnd_3476357 1785042067622160470950031 := by
  unfold tailWord_3476357
  simp only [CollatzResearch.WordTrace]
  refine ⟨126793156266759778352683325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84528770844506518901788883 126793156266759778352683325)
  ·
    refine ⟨47547433600034916882256247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126793156266759778352683325 47547433600034916882256247)
    ·
      refine ⟨71321150400052375323384371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47547433600034916882256247 71321150400052375323384371)
      ·
        refine ⟨106981725600078562985076557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71321150400052375323384371 106981725600078562985076557)
        ·
          refine ⟨40118147100029461119403709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106981725600078562985076557 40118147100029461119403709)
          ·
            refine ⟨15044305162511047919776391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40118147100029461119403709 15044305162511047919776391)
            ·
              refine ⟨22566457743766571879664587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15044305162511047919776391 22566457743766571879664587)
              ·
                refine ⟨33849686615649857819496881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22566457743766571879664587 33849686615649857819496881)
                ·
                  refine ⟨25387264961737393364622661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33849686615649857819496881 25387264961737393364622661)
                  ·
                    refine ⟨4760112180325761255866749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25387264961737393364622661 4760112180325761255866749)
                    ·
                      refine ⟨1785042067622160470950031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4760112180325761255866749 1785042067622160470950031)
                      ·
                        rfl

theorem cell23_3476357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_3476357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476357 prefixEnd_3476357 := by exact prefixLift 3476357
  have htrace : WordTrace (prefixWord ++ tailWord_3476357) baseStart_3476357 baseEnd_3476357 := by
    simpa [prefixWord, tailWord_3476357, baseEnd_3476357] using wordTrace_append hprefix tailTrace_3476357
  have hstable : (prefixWord ++ tailWord_3476357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476357).length < 2 ^ (prefixWord ++ tailWord_3476357).sum := by decide
  have hdescent : baseEnd_3476357 < baseStart_3476357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476407 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 2, 5]
def baseStart_3476407 : Nat := 118140960795 + 3476407 * 2 ^ 59
def prefixEnd_3476407 : Nat := 4983230072969 + 3 ^ 40 * 3476407 * 2
def baseEnd_3476407 : Nat := 595022580551628425108267

theorem tailTrace_3476407 : CollatzResearch.WordTrace tailWord_3476407 prefixEnd_3476407 595022580551628425108267 := by
  unfold tailWord_3476407
  simp only [CollatzResearch.WordTrace]
  refine ⟨126794979916578636892003475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84529986611052424594668983 126794979916578636892003475)
  ·
    refine ⟨190192469874867955338005213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126794979916578636892003475 190192469874867955338005213)
    ·
      refine ⟨71322176203075483251751955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190192469874867955338005213 71322176203075483251751955)
      ·
        refine ⟨106983264304613224877627933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71322176203075483251751955 106983264304613224877627933)
        ·
          refine ⟨40118724114229959329110475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106983264304613224877627933 40118724114229959329110475)
          ·
            refine ⟨60178086171344938993665713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40118724114229959329110475 60178086171344938993665713)
            ·
              refine ⟨45133564628508704245249285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60178086171344938993665713 45133564628508704245249285)
              ·
                refine ⟨8462543367845382045984241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45133564628508704245249285 8462543367845382045984241)
                ·
                  refine ⟨6346907525884036534488181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8462543367845382045984241 6346907525884036534488181)
                  ·
                    refine ⟨595022580551628425108267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6346907525884036534488181 595022580551628425108267)
                    ·
                      rfl

theorem cell23_3476407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_3476407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476407 prefixEnd_3476407 := by exact prefixLift 3476407
  have htrace : WordTrace (prefixWord ++ tailWord_3476407) baseStart_3476407 baseEnd_3476407 := by
    simpa [prefixWord, tailWord_3476407, baseEnd_3476407] using wordTrace_append hprefix tailTrace_3476407
  have hstable : (prefixWord ++ tailWord_3476407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476407).length < 2 ^ (prefixWord ++ tailWord_3476407).sum := by decide
  have hdescent : baseEnd_3476407 < baseStart_3476407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476427 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4]
def baseStart_3476427 : Nat := 118140960795 + 3476427 * 2 ^ 59
def prefixEnd_3476427 : Nat := 4983230072969 + 3 ^ 40 * 3476427 * 2
def baseEnd_3476427 : Nat := 1785078011267975197074709

theorem tailTrace_3476427 : CollatzResearch.WordTrace tailWord_3476427 prefixEnd_3476427 1785078011267975197074709 := by
  unfold tailWord_3476427
  simp only [CollatzResearch.WordTrace]
  refine ⟨126795709376506180307731535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84530472917670786871821023 126795709376506180307731535)
  ·
    refine ⟨190193564064759270461597303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126795709376506180307731535 190193564064759270461597303)
    ·
      refine ⟨285290346097138905692395955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190193564064759270461597303 285290346097138905692395955)
      ·
        refine ⟨427935519145708358538593933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285290346097138905692395955 427935519145708358538593933)
        ·
          refine ⟨160475819679640634451972725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427935519145708358538593933 160475819679640634451972725)
          ·
            refine ⟨15044608094966309479872443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160475819679640634451972725 15044608094966309479872443)
            ·
              refine ⟨22566912142449464219808665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15044608094966309479872443 22566912142449464219808665)
              ·
                refine ⟨16925184106837098164856499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22566912142449464219808665 16925184106837098164856499)
                ·
                  refine ⟨25387776160255647247284749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16925184106837098164856499 25387776160255647247284749)
                  ·
                    refine ⟨9520416060095867717731781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25387776160255647247284749 9520416060095867717731781)
                    ·
                      refine ⟨1785078011267975197074709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9520416060095867717731781 1785078011267975197074709)
                      ·
                        rfl

theorem cell23_3476427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_3476427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476427 prefixEnd_3476427 := by exact prefixLift 3476427
  have htrace : WordTrace (prefixWord ++ tailWord_3476427) baseStart_3476427 baseEnd_3476427 := by
    simpa [prefixWord, tailWord_3476427, baseEnd_3476427] using wordTrace_append hprefix tailTrace_3476427
  have hstable : (prefixWord ++ tailWord_3476427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476427).length < 2 ^ (prefixWord ++ tailWord_3476427).sum := by decide
  have hdescent : baseEnd_3476427 < baseStart_3476427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476522 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3476522 : Nat := 118140960795 + 3476522 * 2 ^ 59
def prefixEnd_3476522 : Nat := 4983230072969 + 3 ^ 40 * 3476522 * 2
def baseEnd_3476522 : Nat := 595042263976717441795591

theorem tailTrace_3476522 : CollatzResearch.WordTrace tailWord_3476522 prefixEnd_3476522 595042263976717441795591 := by
  unfold tailWord_3476522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31699793577790502883109955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84532782874108007688293213 31699793577790502883109955)
  ·
    refine ⟨47549690366685754324664933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31699793577790502883109955 47549690366685754324664933)
    ·
      refine ⟨8915566943753578935874675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47549690366685754324664933 8915566943753578935874675)
      ·
        refine ⟨13373350415630368403812013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8915566943753578935874675 13373350415630368403812013)
        ·
          refine ⟨5015006405861388151429505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13373350415630368403812013 5015006405861388151429505)
          ·
            refine ⟨3761254804396041113572129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5015006405861388151429505 3761254804396041113572129)
            ·
              refine ⟨2820941103297030835179097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761254804396041113572129 2820941103297030835179097)
              ·
                refine ⟨2115705827472773126384323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820941103297030835179097 2115705827472773126384323)
                ·
                  refine ⟨3173558741209159689576485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115705827472773126384323 3173558741209159689576485)
                  ·
                    refine ⟨595042263976717441795591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173558741209159689576485 595042263976717441795591)
                    ·
                      rfl

theorem cell23_3476522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3476522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476522 prefixEnd_3476522 := by exact prefixLift 3476522
  have htrace : WordTrace (prefixWord ++ tailWord_3476522) baseStart_3476522 baseEnd_3476522 := by
    simpa [prefixWord, tailWord_3476522, baseEnd_3476522] using wordTrace_append hprefix tailTrace_3476522
  have hstable : (prefixWord ++ tailWord_3476522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476522).length < 2 ^ (prefixWord ++ tailWord_3476522).sum := by decide
  have hdescent : baseEnd_3476522 < baseStart_3476522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476528 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 1, 1, 3]
def baseStart_3476528 : Nat := 118140960795 + 3476528 * 2 ^ 59
def prefixEnd_3476528 : Nat := 4983230072969 + 3 ^ 40 * 3476528 * 2
def baseEnd_3476528 : Nat := 1785129872814079301911745

theorem tailTrace_3476528 : CollatzResearch.WordTrace tailWord_3476528 prefixEnd_3476528 1785129872814079301911745 := by
  unfold tailWord_3476528
  simp only [CollatzResearch.WordTrace]
  refine ⟨63399696574570137278579119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84532928766093516371438825 63399696574570137278579119)
  ·
    refine ⟨95099544861855205917868679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63399696574570137278579119 95099544861855205917868679)
    ·
      refine ⟨142649317292782808876803019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95099544861855205917868679 142649317292782808876803019)
      ·
        refine ⟨213973975939174213315204529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142649317292782808876803019 213973975939174213315204529)
        ·
          refine ⟨160480481954380659986403397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213973975939174213315204529 160480481954380659986403397)
          ·
            refine ⟨30090090366446373747450637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160480481954380659986403397 30090090366446373747450637)
            ·
              refine ⟨11283783887417390155293989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30090090366446373747450637 11283783887417390155293989)
              ·
                refine ⟨2115709478890760654117623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11283783887417390155293989 2115709478890760654117623)
                ·
                  refine ⟨3173564218336140981176435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115709478890760654117623 3173564218336140981176435)
                  ·
                    refine ⟨4760346327504211471764653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173564218336140981176435 4760346327504211471764653)
                    ·
                      refine ⟨1785129872814079301911745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4760346327504211471764653 1785129872814079301911745)
                      ·
                        rfl

theorem cell23_3476528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 1, 3].length) (baseStart_3476528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476528 prefixEnd_3476528 := by exact prefixLift 3476528
  have htrace : WordTrace (prefixWord ++ tailWord_3476528) baseStart_3476528 baseEnd_3476528 := by
    simpa [prefixWord, tailWord_3476528, baseEnd_3476528] using wordTrace_append hprefix tailTrace_3476528
  have hstable : (prefixWord ++ tailWord_3476528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476528).length < 2 ^ (prefixWord ++ tailWord_3476528).sum := by decide
  have hdescent : baseEnd_3476528 < baseStart_3476528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476544 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 1, 6]
def baseStart_3476544 : Nat := 118140960795 + 3476544 * 2 ^ 59
def prefixEnd_3476544 : Nat := 4983230072969 + 3 ^ 40 * 3476544 * 2
def baseEnd_3476544 : Nat := 595046029501517079770557

theorem tailTrace_3476544 : CollatzResearch.WordTrace tailWord_3476544 prefixEnd_3476544 595046029501517079770557 := by
  unfold tailWord_3476544
  simp only [CollatzResearch.WordTrace]
  refine ⟨63399988358541154644870343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84533317811388206193160457 63399988358541154644870343)
  ·
    refine ⟨95099982537811731967305515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63399988358541154644870343 95099982537811731967305515)
    ·
      refine ⟨142649973806717597950958273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95099982537811731967305515 142649973806717597950958273)
      ·
        refine ⟨106987480355038198463218705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142649973806717597950958273 106987480355038198463218705)
        ·
          refine ⟨80240610266278648847414029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106987480355038198463218705 80240610266278648847414029)
          ·
            refine ⟨30090228849854493317780261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80240610266278648847414029 30090228849854493317780261)
            ·
              refine ⟨5641917909347717497083799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30090228849854493317780261 5641917909347717497083799)
              ·
                refine ⟨8462876864021576245625699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641917909347717497083799 8462876864021576245625699)
                ·
                  refine ⟨12694315296032364368438549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8462876864021576245625699 12694315296032364368438549)
                  ·
                    refine ⟨595046029501517079770557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12694315296032364368438549 595046029501517079770557)
                    ·
                      rfl

theorem cell23_3476544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_3476544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476544 prefixEnd_3476544 := by exact prefixLift 3476544
  have htrace : WordTrace (prefixWord ++ tailWord_3476544) baseStart_3476544 baseEnd_3476544 := by
    simpa [prefixWord, tailWord_3476544, baseEnd_3476544] using wordTrace_append hprefix tailTrace_3476544
  have hstable : (prefixWord ++ tailWord_3476544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476544).length < 2 ^ (prefixWord ++ tailWord_3476544).sum := by decide
  have hdescent : baseEnd_3476544 < baseStart_3476544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476578 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3476578 : Nat := 118140960795 + 3476578 * 2 ^ 59
def prefixEnd_3476578 : Nat := 4983230072969 + 3 ^ 40 * 3476578 * 2
def baseEnd_3476578 : Nat := 595051848948934702095505

theorem tailTrace_3476578 : CollatzResearch.WordTrace tailWord_3476578 prefixEnd_3476578 595051848948934702095505 := by
  unfold tailWord_3476578
  simp only [CollatzResearch.WordTrace]
  refine ⟨31700304199739783274119597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84534144532639422064318925 31700304199739783274119597)
  ·
    refine ⟨11887614074902418727794849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31700304199739783274119597 11887614074902418727794849)
    ·
      refine ⟨8915710556176814045846137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11887614074902418727794849 8915710556176814045846137)
      ·
        refine ⟨6686782917132610534384603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8915710556176814045846137 6686782917132610534384603)
        ·
          refine ⟨10030174375698915801576905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686782917132610534384603 10030174375698915801576905)
          ·
            refine ⟨7522630781774186851182679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10030174375698915801576905 7522630781774186851182679)
            ·
              refine ⟨11283946172661280276774019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7522630781774186851182679 11283946172661280276774019)
              ·
                refine ⟨16925919258991920415161029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11283946172661280276774019 16925919258991920415161029)
                ·
                  refine ⟨3173609861060985077842693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16925919258991920415161029 3173609861060985077842693)
                  ·
                    refine ⟨595051848948934702095505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173609861060985077842693 595051848948934702095505)
                    ·
                      rfl

theorem cell23_3476578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3476578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476578 prefixEnd_3476578 := by exact prefixLift 3476578
  have htrace : WordTrace (prefixWord ++ tailWord_3476578) baseStart_3476578 baseEnd_3476578 := by
    simpa [prefixWord, tailWord_3476578, baseEnd_3476578] using wordTrace_append hprefix tailTrace_3476578
  have hstable : (prefixWord ++ tailWord_3476578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476578).length < 2 ^ (prefixWord ++ tailWord_3476578).sum := by decide
  have hdescent : baseEnd_3476578 < baseStart_3476578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476585 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 1, 2, 2]
def baseStart_3476585 : Nat := 118140960795 + 3476585 * 2 ^ 59
def prefixEnd_3476585 : Nat := 4983230072969 + 3 ^ 40 * 3476585 * 2
def baseEnd_3476585 : Nat := 1785159141211385578898983

theorem tailTrace_3476585 : CollatzResearch.WordTrace tailWord_3476585 prefixEnd_3476585 1785159141211385578898983 := by
  unfold tailWord_3476585
  simp only [CollatzResearch.WordTrace]
  refine ⟨126801472109933773291983209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84534314739955848861322139 126801472109933773291983209)
  ·
    refine ⟨95101104082450329968987407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126801472109933773291983209 95101104082450329968987407)
    ·
      refine ⟨142651656123675494953481111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95101104082450329968987407 142651656123675494953481111)
      ·
        refine ⟨213977484185513242430221667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142651656123675494953481111 213977484185513242430221667)
        ·
          refine ⟨320966226278269863645332501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213977484185513242430221667 320966226278269863645332501)
          ·
            refine ⟨15045291856793899858374961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 320966226278269863645332501 15045291856793899858374961)
            ·
              refine ⟨11283968892595424893781221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15045291856793899858374961 11283968892595424893781221)
              ·
                refine ⟨2115744167361642167583979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11283968892595424893781221 2115744167361642167583979)
                ·
                  refine ⟨3173616251042463251375969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115744167361642167583979 3173616251042463251375969)
                  ·
                    refine ⟨2380212188281847438531977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173616251042463251375969 2380212188281847438531977)
                    ·
                      refine ⟨1785159141211385578898983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380212188281847438531977 1785159141211385578898983)
                      ·
                        rfl

theorem cell23_3476585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 2, 2].length) (baseStart_3476585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476585 prefixEnd_3476585 := by exact prefixLift 3476585
  have htrace : WordTrace (prefixWord ++ tailWord_3476585) baseStart_3476585 baseEnd_3476585 := by
    simpa [prefixWord, tailWord_3476585, baseEnd_3476585] using wordTrace_append hprefix tailTrace_3476585
  have hstable : (prefixWord ++ tailWord_3476585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476585).length < 2 ^ (prefixWord ++ tailWord_3476585).sum := by decide
  have hdescent : baseEnd_3476585 < baseStart_3476585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476741 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_3476741 : Nat := 118140960795 + 3476741 * 2 ^ 59
def prefixEnd_3476741 : Nat := 4983230072969 + 3 ^ 40 * 3476741 * 2
def baseEnd_3476741 : Nat := 595079748064495656182755

theorem tailTrace_3476741 : CollatzResearch.WordTrace tailWord_3476741 prefixEnd_3476741 595079748064495656182755 := by
  unfold tailWord_3476741
  simp only [CollatzResearch.WordTrace]
  refine ⟨126807161897368611934662077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84538107931579074623108051 126807161897368611934662077)
  ·
    refine ⟨47552685711513229475498279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126807161897368611934662077 47552685711513229475498279)
    ·
      refine ⟨71329028567269844213247419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47552685711513229475498279 71329028567269844213247419)
      ·
        refine ⟨106993542850904766319871129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71329028567269844213247419 106993542850904766319871129)
        ·
          refine ⟨80245157138178574739903347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106993542850904766319871129 80245157138178574739903347)
          ·
            refine ⟨120367735707267862109855021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80245157138178574739903347 120367735707267862109855021)
            ·
              refine ⟨45137900890225448291195633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120367735707267862109855021 45137900890225448291195633)
              ·
                refine ⟨33853425667669086218396725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45137900890225448291195633 33853425667669086218396725)
                ·
                  refine ⟨3173758656343976832974693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33853425667669086218396725 3173758656343976832974693)
                  ·
                    refine ⟨595079748064495656182755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173758656343976832974693 595079748064495656182755)
                    ·
                      rfl

theorem cell23_3476741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_3476741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476741 prefixEnd_3476741 := by exact prefixLift 3476741
  have htrace : WordTrace (prefixWord ++ tailWord_3476741) baseStart_3476741 baseEnd_3476741 := by
    simpa [prefixWord, tailWord_3476741, baseEnd_3476741] using wordTrace_append hprefix tailTrace_3476741
  have hstable : (prefixWord ++ tailWord_3476741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476741).length < 2 ^ (prefixWord ++ tailWord_3476741).sum := by decide
  have hdescent : baseEnd_3476741 < baseStart_3476741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476748 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 2, 4, 2]
def baseStart_3476748 : Nat := 118140960795 + 3476748 * 2 ^ 59
def prefixEnd_3476748 : Nat := 4983230072969 + 3 ^ 40 * 3476748 * 2
def baseEnd_3476748 : Nat := 1785242838558068441160733

theorem tailTrace_3476748 : CollatzResearch.WordTrace tailWord_3476748 prefixEnd_3476748 1785242838558068441160733 := by
  unfold tailWord_3476748
  simp only [CollatzResearch.WordTrace]
  refine ⟨63403708604171626065083449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84538278138895501420111265 63403708604171626065083449)
  ·
    refine ⟨47552781453128719548812587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63403708604171626065083449 47552781453128719548812587)
    ·
      refine ⟨71329172179693079323218881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47552781453128719548812587 71329172179693079323218881)
      ·
        refine ⟨53496879134769809492414161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71329172179693079323218881 53496879134769809492414161)
        ·
          refine ⟨40122659351077357119310621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53496879134769809492414161 40122659351077357119310621)
          ·
            refine ⟨15045997256654008919741483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40122659351077357119310621 15045997256654008919741483)
            ·
              refine ⟨22568995884981013379612225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15045997256654008919741483 22568995884981013379612225)
              ·
                refine ⟨16926746913735760034709169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22568995884981013379612225 16926746913735760034709169)
                ·
                  refine ⟨12695060185301820026031877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16926746913735760034709169 12695060185301820026031877)
                  ·
                    refine ⟨2380323784744091254880977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12695060185301820026031877 2380323784744091254880977)
                    ·
                      refine ⟨1785242838558068441160733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380323784744091254880977 1785242838558068441160733)
                      ·
                        rfl

theorem cell23_3476748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_3476748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476748 prefixEnd_3476748 := by exact prefixLift 3476748
  have htrace : WordTrace (prefixWord ++ tailWord_3476748) baseStart_3476748 baseEnd_3476748 := by
    simpa [prefixWord, tailWord_3476748, baseEnd_3476748] using wordTrace_append hprefix tailTrace_3476748
  have hstable : (prefixWord ++ tailWord_3476748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476748).length < 2 ^ (prefixWord ++ tailWord_3476748).sum := by decide
  have hdescent : baseEnd_3476748 < baseStart_3476748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476765 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3476765 : Nat := 118140960795 + 3476765 * 2 ^ 59
def prefixEnd_3476765 : Nat := 4983230072969 + 3 ^ 40 * 3476765 * 2
def baseEnd_3476765 : Nat := 1785251567729194874648155

theorem tailTrace_3476765 : CollatzResearch.WordTrace tailWord_3476765 prefixEnd_3476765 1785251567729194874648155 := by
  unfold tailWord_3476765
  simp only [CollatzResearch.WordTrace]
  refine ⟨126808037249281664033535749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84538691499521109355690499 126808037249281664033535749)
  ·
    refine ⟨23776506984240312006287953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126808037249281664033535749 23776506984240312006287953)
    ·
      refine ⟨17832380238180234004715965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23776506984240312006287953 17832380238180234004715965)
      ·
        refine ⟨6687142589317587751768487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17832380238180234004715965 6687142589317587751768487)
        ·
          refine ⟨10030713883976381627652731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6687142589317587751768487 10030713883976381627652731)
          ·
            refine ⟨15046070825964572441479097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10030713883976381627652731 15046070825964572441479097)
            ·
              refine ⟨11284553119473429331109323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15046070825964572441479097 11284553119473429331109323)
              ·
                refine ⟨16926829679210143996663985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11284553119473429331109323 16926829679210143996663985)
                ·
                  refine ⟨12695122259407607997497989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16926829679210143996663985 12695122259407607997497989)
                  ·
                    refine ⟨2380335423638926499530873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12695122259407607997497989 2380335423638926499530873)
                    ·
                      refine ⟨1785251567729194874648155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380335423638926499530873 1785251567729194874648155)
                      ·
                        rfl

theorem cell23_3476765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3476765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476765 prefixEnd_3476765 := by exact prefixLift 3476765
  have htrace : WordTrace (prefixWord ++ tailWord_3476765) baseStart_3476765 baseEnd_3476765 := by
    simpa [prefixWord, tailWord_3476765, baseEnd_3476765] using wordTrace_append hprefix tailTrace_3476765
  have hstable : (prefixWord ++ tailWord_3476765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476765).length < 2 ^ (prefixWord ++ tailWord_3476765).sum := by decide
  have hdescent : baseEnd_3476765 < baseStart_3476765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476831 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 1, 6]
def baseStart_3476831 : Nat := 118140960795 + 3476831 * 2 ^ 59
def prefixEnd_3476831 : Nat := 4983230072969 + 3 ^ 40 * 3476831 * 2
def baseEnd_3476831 : Nat := 595095152484130538807617

theorem tailTrace_3476831 : CollatzResearch.WordTrace tailWord_3476831 prefixEnd_3476831 595095152484130538807617 := by
  unfold tailWord_3476831
  simp only [CollatzResearch.WordTrace]
  refine ⟨126810444467042557305438347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84540296311361704870292231 126810444467042557305438347)
  ·
    refine ⟨190215666700563835958157521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126810444467042557305438347 190215666700563835958157521)
    ·
      refine ⟨142661750025422876968618141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190215666700563835958157521 142661750025422876968618141)
      ·
        refine ⟨53498156259533578863231803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142661750025422876968618141 53498156259533578863231803)
        ·
          refine ⟨80247234389300368294847705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53498156259533578863231803 80247234389300368294847705)
          ·
            refine ⟨60185425791975276221135779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80247234389300368294847705 60185425791975276221135779)
            ·
              refine ⟨90278138687962914331703669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60185425791975276221135779 90278138687962914331703669)
              ·
                refine ⟨8463575501996523218597219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90278138687962914331703669 8463575501996523218597219)
                ·
                  refine ⟨12695363252994784827895829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8463575501996523218597219 12695363252994784827895829)
                  ·
                    refine ⟨595095152484130538807617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12695363252994784827895829 595095152484130538807617)
                    ·
                      rfl

theorem cell23_3476831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_3476831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476831 prefixEnd_3476831 := by exact prefixLift 3476831
  have htrace : WordTrace (prefixWord ++ tailWord_3476831) baseStart_3476831 baseEnd_3476831 := by
    simpa [prefixWord, tailWord_3476831, baseEnd_3476831] using wordTrace_append hprefix tailTrace_3476831
  have hstable : (prefixWord ++ tailWord_3476831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476831).length < 2 ^ (prefixWord ++ tailWord_3476831).sum := by decide
  have hdescent : baseEnd_3476831 < baseStart_3476831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476835 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 1, 5]
def baseStart_3476835 : Nat := 118140960795 + 3476835 * 2 ^ 59
def prefixEnd_3476835 : Nat := 4983230072969 + 3 ^ 40 * 3476835 * 2
def baseEnd_3476835 : Nat := 595095837125003200257611

theorem tailTrace_3476835 : CollatzResearch.WordTrace tailWord_3476835 prefixEnd_3476835 595095837125003200257611 := by
  unfold tailWord_3476835
  simp only [CollatzResearch.WordTrace]
  refine ⟨126810590359028065988583959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84540393572685377325722639 126810590359028065988583959)
  ·
    refine ⟨190215885538542098982875939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126810590359028065988583959 190215885538542098982875939)
    ·
      refine ⟨285323828307813148474313909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190215885538542098982875939 285323828307813148474313909)
      ·
        refine ⟨26749108903857482669466929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285323828307813148474313909 26749108903857482669466929)
        ·
          refine ⟨20061831677893112002100197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26749108903857482669466929 20061831677893112002100197)
          ·
            refine ⟨3761593439604958500393787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20061831677893112002100197 3761593439604958500393787)
            ·
              refine ⟨5642390159407437750590681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761593439604958500393787 5642390159407437750590681)
              ·
                refine ⟨4231792619555578312943011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5642390159407437750590681 4231792619555578312943011)
                ·
                  refine ⟨6347688929333367469414517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231792619555578312943011 6347688929333367469414517)
                  ·
                    refine ⟨595095837125003200257611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6347688929333367469414517 595095837125003200257611)
                    ·
                      rfl

theorem cell23_3476835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 5].length) (baseStart_3476835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476835 prefixEnd_3476835 := by exact prefixLift 3476835
  have htrace : WordTrace (prefixWord ++ tailWord_3476835) baseStart_3476835 baseEnd_3476835 := by
    simpa [prefixWord, tailWord_3476835, baseEnd_3476835] using wordTrace_append hprefix tailTrace_3476835
  have hstable : (prefixWord ++ tailWord_3476835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476835).length < 2 ^ (prefixWord ++ tailWord_3476835).sum := by decide
  have hdescent : baseEnd_3476835 < baseStart_3476835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476855 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 1, 1, 4]
def baseStart_3476855 : Nat := 118140960795 + 3476855 * 2 ^ 59
def prefixEnd_3476855 : Nat := 4983230072969 + 3 ^ 40 * 3476855 * 2
def baseEnd_3476855 : Nat := 1785297780988099522522741

theorem tailTrace_3476855 : CollatzResearch.WordTrace tailWord_3476855 prefixEnd_3476855 1785297780988099522522741 := by
  unfold tailWord_3476855
  simp only [CollatzResearch.WordTrace]
  refine ⟨126811319818955609404312019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84540879879303739602874679 126811319818955609404312019)
  ·
    refine ⟨190216979728433414106468029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126811319818955609404312019 190216979728433414106468029)
    ·
      refine ⟨71331367398162530289925511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190216979728433414106468029 71331367398162530289925511)
      ·
        refine ⟨106997051097243795434888267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71331367398162530289925511 106997051097243795434888267)
        ·
          refine ⟨160495576645865693152332401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106997051097243795434888267 160495576645865693152332401)
          ·
            refine ⟨120371682484399269864249301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160495576645865693152332401 120371682484399269864249301)
            ·
              refine ⟨2821211308228107887443343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 120371682484399269864249301 2821211308228107887443343)
              ·
                refine ⟨4231816962342161831165015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821211308228107887443343 4231816962342161831165015)
                ·
                  refine ⟨6347725443513242746747523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231816962342161831165015 6347725443513242746747523)
                  ·
                    refine ⟨9521588165269864120121285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6347725443513242746747523 9521588165269864120121285)
                    ·
                      refine ⟨1785297780988099522522741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9521588165269864120121285 1785297780988099522522741)
                      ·
                        rfl

theorem cell23_3476855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_3476855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476855 prefixEnd_3476855 := by exact prefixLift 3476855
  have htrace : WordTrace (prefixWord ++ tailWord_3476855) baseStart_3476855 baseEnd_3476855 := by
    simpa [prefixWord, tailWord_3476855, baseEnd_3476855] using wordTrace_append hprefix tailTrace_3476855
  have hstable : (prefixWord ++ tailWord_3476855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476855).length < 2 ^ (prefixWord ++ tailWord_3476855).sum := by decide
  have hdescent : baseEnd_3476855 < baseStart_3476855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476866 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3476866 : Nat := 118140960795 + 3476866 * 2 ^ 59
def prefixEnd_3476866 : Nat := 4983230072969 + 3 ^ 40 * 3476866 * 2
def baseEnd_3476866 : Nat := 1785303429275298979485191

theorem tailTrace_3476866 : CollatzResearch.WordTrace tailWord_3476866 prefixEnd_3476866 1785303429275298979485191 := by
  unfold tailWord_3476866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31702930255478939570740613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84541147347943838855308301 31702930255478939570740613)
  ·
    refine ⟨5944299422902301169513865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31702930255478939570740613 5944299422902301169513865)
    ·
      refine ⟨4458224567176725877135399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5944299422902301169513865 4458224567176725877135399)
      ·
        refine ⟨6687336850765088815703099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458224567176725877135399 6687336850765088815703099)
        ·
          refine ⟨10031005276147633223554649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6687336850765088815703099 10031005276147633223554649)
          ·
            refine ⟨7523253957110724917665987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10031005276147633223554649 7523253957110724917665987)
            ·
              refine ⟨11284880935666087376498981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523253957110724917665987 11284880935666087376498981)
              ·
                refine ⟨2115915175437391383093559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11284880935666087376498981 2115915175437391383093559)
                ·
                  refine ⟨3173872763156087074640339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115915175437391383093559 3173872763156087074640339)
                  ·
                    refine ⟨4760809144734130611960509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173872763156087074640339 4760809144734130611960509)
                    ·
                      refine ⟨1785303429275298979485191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4760809144734130611960509 1785303429275298979485191)
                      ·
                        rfl

theorem cell23_3476866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3476866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476866 prefixEnd_3476866 := by exact prefixLift 3476866
  have htrace : WordTrace (prefixWord ++ tailWord_3476866) baseStart_3476866 baseEnd_3476866 := by
    simpa [prefixWord, tailWord_3476866, baseEnd_3476866] using wordTrace_append hprefix tailTrace_3476866
  have hstable : (prefixWord ++ tailWord_3476866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476866).length < 2 ^ (prefixWord ++ tailWord_3476866).sum := by decide
  have hdescent : baseEnd_3476866 < baseStart_3476866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476882 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3476882 : Nat := 118140960795 + 3476882 * 2 ^ 59
def prefixEnd_3476882 : Nat := 4983230072969 + 3 ^ 40 * 3476882 * 2
def baseEnd_3476882 : Nat := 595103881655256972295039

theorem tailTrace_3476882 : CollatzResearch.WordTrace tailWord_3476882 prefixEnd_3476882 595103881655256972295039 := by
  unfold tailWord_3476882
  simp only [CollatzResearch.WordTrace]
  refine ⟨31703076147464448253886225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84541536393238528677029933 31703076147464448253886225)
  ·
    refine ⟨23777307110598336190414669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31703076147464448253886225 23777307110598336190414669)
    ·
      refine ⟨8916490166474376071405501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23777307110598336190414669 8916490166474376071405501)
      ·
        refine ⟨3343683812427891026777063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8916490166474376071405501 3343683812427891026777063)
        ·
          refine ⟨5015525718641836540165595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343683812427891026777063 5015525718641836540165595)
          ·
            refine ⟨7523288577962754810248393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015525718641836540165595 7523288577962754810248393)
            ·
              refine ⟨5642466433472066107686295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7523288577962754810248393 5642466433472066107686295)
              ·
                refine ⟨8463699650208099161529443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642466433472066107686295 8463699650208099161529443)
                ·
                  refine ⟨12695549475312148742294165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8463699650208099161529443 12695549475312148742294165)
                  ·
                    refine ⟨595103881655256972295039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12695549475312148742294165 595103881655256972295039)
                    ·
                      rfl

theorem cell23_3476882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3476882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476882 prefixEnd_3476882 := by exact prefixLift 3476882
  have htrace : WordTrace (prefixWord ++ tailWord_3476882) baseStart_3476882 baseEnd_3476882 := by
    simpa [prefixWord, tailWord_3476882, baseEnd_3476882] using wordTrace_append hprefix tailTrace_3476882
  have hstable : (prefixWord ++ tailWord_3476882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476882).length < 2 ^ (prefixWord ++ tailWord_3476882).sum := by decide
  have hdescent : baseEnd_3476882 < baseStart_3476882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476909 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3476909 : Nat := 118140960795 + 3476909 * 2 ^ 59
def prefixEnd_3476909 : Nat := 4983230072969 + 3 ^ 40 * 3476909 * 2
def baseEnd_3476909 : Nat := 1785325508943442311247493

theorem tailTrace_3476909 : CollatzResearch.WordTrace tailWord_3476909 prefixEnd_3476909 1785325508943442311247493 := by
  unfold tailWord_3476909
  simp only [CollatzResearch.WordTrace]
  refine ⟨126813289360759976626777781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84542192907173317751185187 126813289360759976626777781)
  ·
    refine ⟨11888745877571247808760417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126813289360759976626777781 11888745877571247808760417)
    ·
      refine ⟨8916559408178435856570313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11888745877571247808760417 8916559408178435856570313)
      ·
        refine ⟨6687419556133826892427735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8916559408178435856570313 6687419556133826892427735)
        ·
          refine ⟨10031129334200740338641603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6687419556133826892427735 10031129334200740338641603)
          ·
            refine ⟨15046694001301110507962405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031129334200740338641603 15046694001301110507962405)
            ·
              refine ⟨2821255125243958220242951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15046694001301110507962405 2821255125243958220242951)
              ·
                refine ⟨4231882687865937330364427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821255125243958220242951 4231882687865937330364427)
                ·
                  refine ⟨6347824031798905995546641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231882687865937330364427 6347824031798905995546641)
                  ·
                    refine ⟨4760868023849179496659981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6347824031798905995546641 4760868023849179496659981)
                    ·
                      refine ⟨1785325508943442311247493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4760868023849179496659981 1785325508943442311247493)
                      ·
                        rfl

theorem cell23_3476909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3476909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476909 prefixEnd_3476909 := by exact prefixLift 3476909
  have htrace : WordTrace (prefixWord ++ tailWord_3476909) baseStart_3476909 baseEnd_3476909 := by
    simpa [prefixWord, tailWord_3476909, baseEnd_3476909] using wordTrace_append hprefix tailTrace_3476909
  have hstable : (prefixWord ++ tailWord_3476909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476909).length < 2 ^ (prefixWord ++ tailWord_3476909).sum := by decide
  have hdescent : baseEnd_3476909 < baseStart_3476909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476938 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3476938 : Nat := 118140960795 + 3476938 * 2 ^ 59
def prefixEnd_3476938 : Nat := 4983230072969 + 3 ^ 40 * 3476938 * 2
def baseEnd_3476938 : Nat := 595113466627474232594953

theorem tailTrace_3476938 : CollatzResearch.WordTrace tailWord_3476938 prefixEnd_3476938 595113466627474232594953 := by
  unfold tailWord_3476938
  simp only [CollatzResearch.WordTrace]
  refine ⟨31703586769413728644895867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84542898051769943053055645 31703586769413728644895867)
  ·
    refine ⟨47555380154120592967343801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31703586769413728644895867 47555380154120592967343801)
    ·
      refine ⟨35666535115590444725507851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47555380154120592967343801 35666535115590444725507851)
      ·
        refine ⟨53499802673385667088261777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35666535115590444725507851 53499802673385667088261777)
        ·
          refine ⟨40124852005039250316196333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53499802673385667088261777 40124852005039250316196333)
          ·
            refine ⟨15046819501889718868573625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40124852005039250316196333 15046819501889718868573625)
            ·
              refine ⟨11285114626417289151430219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15046819501889718868573625 11285114626417289151430219)
              ·
                refine ⟨16927671939625933727145329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285114626417289151430219 16927671939625933727145329)
                ·
                  refine ⟨12695753954719450295358997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16927671939625933727145329 12695753954719450295358997)
                  ·
                    refine ⟨595113466627474232594953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12695753954719450295358997 595113466627474232594953)
                    ·
                      rfl

theorem cell23_3476938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3476938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476938 prefixEnd_3476938 := by exact prefixLift 3476938
  have htrace : WordTrace (prefixWord ++ tailWord_3476938) baseStart_3476938 baseEnd_3476938 := by
    simpa [prefixWord, tailWord_3476938, baseEnd_3476938] using wordTrace_append hprefix tailTrace_3476938
  have hstable : (prefixWord ++ tailWord_3476938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476938).length < 2 ^ (prefixWord ++ tailWord_3476938).sum := by decide
  have hdescent : baseEnd_3476938 < baseStart_3476938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476965 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3476965 : Nat := 118140960795 + 3476965 * 2 ^ 59
def prefixEnd_3476965 : Nat := 4983230072969 + 3 ^ 40 * 3476965 * 2
def baseEnd_3476965 : Nat := 1785354263860094092147235

theorem tailTrace_3476965 : CollatzResearch.WordTrace tailWord_3476965 prefixEnd_3476965 1785354263860094092147235 := by
  unfold tailWord_3476965
  simp only [CollatzResearch.WordTrace]
  refine ⟨126815331848557098190816349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84543554565704732127210899 126815331848557098190816349)
  ·
    refine ⟨47555749443208911821556131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126815331848557098190816349 47555749443208911821556131)
    ·
      refine ⟨71333624164813367732334197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47555749443208911821556131 71333624164813367732334197)
      ·
        refine ⟨6687527265451253224906331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71333624164813367732334197 6687527265451253224906331)
        ·
          refine ⟨10031290898176879837359497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6687527265451253224906331 10031290898176879837359497)
          ·
            refine ⟨7523468173632659878019623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10031290898176879837359497 7523468173632659878019623)
            ·
              refine ⟨11285202260448989817029435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523468173632659878019623 11285202260448989817029435)
              ·
                refine ⟨16927803390673484725544153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285202260448989817029435 16927803390673484725544153)
                ·
                  refine ⟨12695852543005113544158115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16927803390673484725544153 12695852543005113544158115)
                  ·
                    refine ⟨19043778814507670316237173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12695852543005113544158115 19043778814507670316237173)
                    ·
                      refine ⟨1785354263860094092147235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19043778814507670316237173 1785354263860094092147235)
                      ·
                        rfl

theorem cell23_3476965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3476965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476965 prefixEnd_3476965 := by exact prefixLift 3476965
  have htrace : WordTrace (prefixWord ++ tailWord_3476965) baseStart_3476965 baseEnd_3476965 := by
    simpa [prefixWord, tailWord_3476965, baseEnd_3476965] using wordTrace_append hprefix tailTrace_3476965
  have hstable : (prefixWord ++ tailWord_3476965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476965).length < 2 ^ (prefixWord ++ tailWord_3476965).sum := by decide
  have hdescent : baseEnd_3476965 < baseStart_3476965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476990 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3476990 : Nat := 118140960795 + 3476990 * 2 ^ 59
def prefixEnd_3476990 : Nat := 4983230072969 + 3 ^ 40 * 3476990 * 2
def baseEnd_3476990 : Nat := 1785367100876456494334621

theorem tailTrace_3476990 : CollatzResearch.WordTrace tailWord_3476990 prefixEnd_3476990 1785367100876456494334621 := by
  unfold tailWord_3476990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852030459183315932559553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84544162448977684973650949 15852030459183315932559553)
  ·
    refine ⟨11889022844387486949419665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15852030459183315932559553 11889022844387486949419665)
    ·
      refine ⟨8916767133290615212064749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11889022844387486949419665 8916767133290615212064749)
      ·
        refine ⟨3343787674983980704524281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8916767133290615212064749 3343787674983980704524281)
        ·
          refine ⟨2507840756237985528393211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3343787674983980704524281 2507840756237985528393211)
          ·
            refine ⟨3761761134356978292589817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507840756237985528393211 3761761134356978292589817)
            ·
              refine ⟨2821320850767733719442363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761761134356978292589817 2821320850767733719442363)
              ·
                refine ⟨4231981276151600579163545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821320850767733719442363 4231981276151600579163545)
                ·
                  refine ⟨3173985957113700434372659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231981276151600579163545 3173985957113700434372659)
                  ·
                    refine ⟨4760978935670550651558989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173985957113700434372659 4760978935670550651558989)
                    ·
                      refine ⟨1785367100876456494334621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4760978935670550651558989 1785367100876456494334621)
                      ·
                        rfl

theorem cell23_3476990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3476990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476990 prefixEnd_3476990 := by exact prefixLift 3476990
  have htrace : WordTrace (prefixWord ++ tailWord_3476990) baseStart_3476990 baseEnd_3476990 := by
    simpa [prefixWord, tailWord_3476990, baseEnd_3476990] using wordTrace_append hprefix tailTrace_3476990
  have hstable : (prefixWord ++ tailWord_3476990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476990).length < 2 ^ (prefixWord ++ tailWord_3476990).sum := by decide
  have hdescent : baseEnd_3476990 < baseStart_3476990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476996 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3476996 : Nat := 118140960795 + 3476996 * 2 ^ 59
def prefixEnd_3476996 : Nat := 4983230072969 + 3 ^ 40 * 3476996 * 2
def baseEnd_3476996 : Nat := 1785370181760383470859593

theorem tailTrace_3476996 : CollatzResearch.WordTrace tailWord_3476996 prefixEnd_3476996 1785370181760383470859593 := by
  unfold tailWord_3476996
  simp only [CollatzResearch.WordTrace]
  refine ⟨63408231255722395242597421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84544308340963193656796561 63408231255722395242597421)
  ·
    refine ⟨23778086720895898215974033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63408231255722395242597421 23778086720895898215974033)
    ·
      refine ⟨17833565040671923661980525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23778086720895898215974033 17833565040671923661980525)
      ·
        refine ⟨6687586890251971373242697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17833565040671923661980525 6687586890251971373242697)
        ·
          refine ⟨5015690167688978529932023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6687586890251971373242697 5015690167688978529932023)
          ·
            refine ⟨7523535251533467794898035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015690167688978529932023 7523535251533467794898035)
            ·
              refine ⟨11285302877300201692347053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523535251533467794898035 11285302877300201692347053)
              ·
                refine ⟨4231988578987575634630145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11285302877300201692347053 4231988578987575634630145)
                ·
                  refine ⟨3173991434240681725972609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231988578987575634630145 3173991434240681725972609)
                  ·
                    refine ⟨2380493575680511294479457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173991434240681725972609 2380493575680511294479457)
                    ·
                      refine ⟨1785370181760383470859593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380493575680511294479457 1785370181760383470859593)
                      ·
                        rfl

theorem cell23_3476996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3476996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3476996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3476996 prefixEnd_3476996 := by exact prefixLift 3476996
  have htrace : WordTrace (prefixWord ++ tailWord_3476996) baseStart_3476996 baseEnd_3476996 := by
    simpa [prefixWord, tailWord_3476996, baseEnd_3476996] using wordTrace_append hprefix tailTrace_3476996
  have hstable : (prefixWord ++ tailWord_3476996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476996).length < 2 ^ (prefixWord ++ tailWord_3476996).sum := by decide
  have hdescent : baseEnd_3476996 < baseStart_3476996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477079 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 1, 4]
def baseStart_3477079 : Nat := 118140960795 + 3477079 * 2 ^ 59
def prefixEnd_3477079 : Nat := 4983230072969 + 3 ^ 40 * 3477079 * 2
def baseEnd_3477079 : Nat := 595137600218235548707237

theorem tailTrace_3477079 : CollatzResearch.WordTrace tailWord_3477079 prefixEnd_3477079 595137600218235548707237 := by
  unfold tailWord_3477079
  simp only [CollatzResearch.WordTrace]
  refine ⟨126819489770144095660466291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84546326513429397106977527 126819489770144095660466291)
  ·
    refine ⟨190229234655216143490699437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126819489770144095660466291 190229234655216143490699437)
    ·
      refine ⟨71335962995706053809012289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190229234655216143490699437 71335962995706053809012289)
      ·
        refine ⟨53501972246779540356759217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71335962995706053809012289 53501972246779540356759217)
        ·
          refine ⟨40126479185084655267569413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53501972246779540356759217 40126479185084655267569413)
          ·
            refine ⟨7523714847203372862669265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40126479185084655267569413 7523714847203372862669265)
            ·
              refine ⟨5642786135402529647001949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7523714847203372862669265 5642786135402529647001949)
              ·
                refine ⟨2116044800775948617625731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5642786135402529647001949 2116044800775948617625731)
                ·
                  refine ⟨3174067201163922926438597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116044800775948617625731 3174067201163922926438597)
                  ·
                    refine ⟨595137600218235548707237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174067201163922926438597 595137600218235548707237)
                    ·
                      rfl

theorem cell23_3477079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_3477079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477079 prefixEnd_3477079 := by exact prefixLift 3477079
  have htrace : WordTrace (prefixWord ++ tailWord_3477079) baseStart_3477079 baseEnd_3477079 := by
    simpa [prefixWord, tailWord_3477079, baseEnd_3477079] using wordTrace_append hprefix tailTrace_3477079
  have hstable : (prefixWord ++ tailWord_3477079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477079).length < 2 ^ (prefixWord ++ tailWord_3477079).sum := by decide
  have hdescent : baseEnd_3477079 < baseStart_3477079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477092 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 6]
def baseStart_3477092 : Nat := 118140960795 + 3477092 * 2 ^ 59
def prefixEnd_3477092 : Nat := 4983230072969 + 3 ^ 40 * 3477092 * 2
def baseEnd_3477092 : Nat := 198379941767023899473239

theorem tailTrace_3477092 : CollatzResearch.WordTrace tailWord_3477092 prefixEnd_3477092 198379941767023899473239 := by
  unfold tailWord_3477092
  simp only [CollatzResearch.WordTrace]
  refine ⟨63409981959548499440344765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84546642612731332587126353 63409981959548499440344765)
  ·
    refine ⟨23778743234830687290129287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63409981959548499440344765 23778743234830687290129287)
    ·
      refine ⟨35668114852246030935193931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23778743234830687290129287 35668114852246030935193931)
      ·
        refine ⟨53502172278369046402790897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35668114852246030935193931 53502172278369046402790897)
        ·
          refine ⟨40126629208776784802093173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53502172278369046402790897 40126629208776784802093173)
          ·
            refine ⟨3761871488322823575196235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40126629208776784802093173 3761871488322823575196235)
            ·
              refine ⟨5642807232484235362794353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761871488322823575196235 5642807232484235362794353)
              ·
                refine ⟨4232105424363176522095765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5642807232484235362794353 4232105424363176522095765)
                ·
                  refine ⟨198379941767023899473239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4232105424363176522095765 198379941767023899473239)
                  ·
                    rfl

theorem cell23_3477092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_3477092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477092 prefixEnd_3477092 := by exact prefixLift 3477092
  have htrace : WordTrace (prefixWord ++ tailWord_3477092) baseStart_3477092 baseEnd_3477092 := by
    simpa [prefixWord, tailWord_3477092, baseEnd_3477092] using wordTrace_append hprefix tailTrace_3477092
  have hstable : (prefixWord ++ tailWord_3477092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477092).length < 2 ^ (prefixWord ++ tailWord_3477092).sum := by decide
  have hdescent : baseEnd_3477092 < baseStart_3477092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477109 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 6]
def baseStart_3477109 : Nat := 118140960795 + 3477109 * 2 ^ 59
def prefixEnd_3477109 : Nat := 4983230072969 + 3 ^ 40 * 3477109 * 2
def baseEnd_3477109 : Nat := 198380911674926836527397

theorem tailTrace_3477109 : CollatzResearch.WordTrace tailWord_3477109 prefixEnd_3477109 198380911674926836527397 := by
  unfold tailWord_3477109
  simp only [CollatzResearch.WordTrace]
  refine ⟨126820583960035410784058381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84547055973356940522705587 126820583960035410784058381)
  ·
    refine ⟨47557718985013279044021893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126820583960035410784058381 47557718985013279044021893)
    ·
      refine ⟨8917072309689989820754105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47557718985013279044021893 8917072309689989820754105)
      ·
        refine ⟨6687804232267492365565579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8917072309689989820754105 6687804232267492365565579)
        ·
          refine ⟨10031706348401238548348369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6687804232267492365565579 10031706348401238548348369)
          ·
            refine ⟨7523779761300928911261277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10031706348401238548348369 7523779761300928911261277)
            ·
              refine ⟨2821417410487848341722979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7523779761300928911261277 2821417410487848341722979)
              ·
                refine ⟨4232126115731772512584469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821417410487848341722979 4232126115731772512584469)
                ·
                  refine ⟨198380911674926836527397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4232126115731772512584469 198380911674926836527397)
                  ·
                    rfl

theorem cell23_3477109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_3477109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477109 prefixEnd_3477109 := by exact prefixLift 3477109
  have htrace : WordTrace (prefixWord ++ tailWord_3477109) baseStart_3477109 baseEnd_3477109 := by
    simpa [prefixWord, tailWord_3477109, baseEnd_3477109] using wordTrace_append hprefix tailTrace_3477109
  have hstable : (prefixWord ++ tailWord_3477109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477109).length < 2 ^ (prefixWord ++ tailWord_3477109).sum := by decide
  have hdescent : baseEnd_3477109 < baseStart_3477109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477152 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 4, 4]
def baseStart_3477152 : Nat := 118140960795 + 3477152 * 2 ^ 59
def prefixEnd_3477152 : Nat := 4983230072969 + 3 ^ 40 * 3477152 * 2
def baseEnd_3477152 : Nat := 595150094914161620169625

theorem tailTrace_3477152 : CollatzResearch.WordTrace tailWord_3477152 prefixEnd_3477152 595150094914161620169625 := by
  unfold tailWord_3477152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411076149439814563936855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84548101532586419418582473 63411076149439814563936855)
  ·
    refine ⟨95116614224159721845905283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63411076149439814563936855 95116614224159721845905283)
    ·
      refine ⟨142674921336239582768857925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95116614224159721845905283 142674921336239582768857925)
      ·
        refine ⟨26751547750544921769160861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142674921336239582768857925 26751547750544921769160861)
        ·
          refine ⟨10031830406454345663435323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26751547750544921769160861 10031830406454345663435323)
          ·
            refine ⟨15047745609681518495152985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031830406454345663435323 15047745609681518495152985)
            ·
              refine ⟨11285809207261138871364739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15047745609681518495152985 11285809207261138871364739)
              ·
                refine ⟨16928713810891708307047109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285809207261138871364739 16928713810891708307047109)
                ·
                  refine ⟨3174133839542195307571333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16928713810891708307047109 3174133839542195307571333)
                  ·
                    refine ⟨595150094914161620169625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174133839542195307571333 595150094914161620169625)
                    ·
                      rfl

theorem cell23_3477152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_3477152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477152 prefixEnd_3477152 := by exact prefixLift 3477152
  have htrace : WordTrace (prefixWord ++ tailWord_3477152) baseStart_3477152 baseEnd_3477152 := by
    simpa [prefixWord, tailWord_3477152, baseEnd_3477152] using wordTrace_append hprefix tailTrace_3477152
  have hstable : (prefixWord ++ tailWord_3477152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477152).length < 2 ^ (prefixWord ++ tailWord_3477152).sum := by decide
  have hdescent : baseEnd_3477152 < baseStart_3477152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477153 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3477153 : Nat := 118140960795 + 3477153 * 2 ^ 59
def prefixEnd_3477153 : Nat := 4983230072969 + 3 ^ 40 * 3477153 * 2
def baseEnd_3477153 : Nat := 1785450798223139356596371

theorem tailTrace_3477153 : CollatzResearch.WordTrace tailWord_3477153 prefixEnd_3477153 1785450798223139356596371 := by
  unfold tailWord_3477153
  simp only [CollatzResearch.WordTrace]
  refine ⟨126822188771876006298660113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84548125847917337532440075 126822188771876006298660113)
  ·
    refine ⟨95116641578907004723995085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126822188771876006298660113 95116641578907004723995085)
    ·
      refine ⟨35668740592090126771498157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95116641578907004723995085 35668740592090126771498157)
      ·
        refine ⟨13375777722033797539311809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35668740592090126771498157 13375777722033797539311809)
        ·
          refine ⟨10031833291525348154483857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13375777722033797539311809 10031833291525348154483857)
          ·
            refine ⟨7523874968644011115862893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10031833291525348154483857 7523874968644011115862893)
            ·
              refine ⟨2821453113241504168448585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7523874968644011115862893 2821453113241504168448585)
              ·
                refine ⟨2116089834931128126336439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821453113241504168448585 2116089834931128126336439)
                ·
                  refine ⟨3174134752396692189504659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116089834931128126336439 3174134752396692189504659)
                  ·
                    refine ⟨4761202128595038284256989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174134752396692189504659 4761202128595038284256989)
                    ·
                      refine ⟨1785450798223139356596371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761202128595038284256989 1785450798223139356596371)
                      ·
                        rfl

theorem cell23_3477153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3477153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477153 prefixEnd_3477153 := by exact prefixLift 3477153
  have htrace : WordTrace (prefixWord ++ tailWord_3477153) baseStart_3477153 baseEnd_3477153 := by
    simpa [prefixWord, tailWord_3477153, baseEnd_3477153] using wordTrace_append hprefix tailTrace_3477153
  have hstable : (prefixWord ++ tailWord_3477153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477153).length < 2 ^ (prefixWord ++ tailWord_3477153).sum := by decide
  have hdescent : baseEnd_3477153 < baseStart_3477153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477160 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 6]
def baseStart_3477160 : Nat := 118140960795 + 3477160 * 2 ^ 59
def prefixEnd_3477160 : Nat := 4983230072969 + 3 ^ 40 * 3477160 * 2
def baseEnd_3477160 : Nat := 198383821398635647689871

theorem tailTrace_3477160 : CollatzResearch.WordTrace tailWord_3477160 prefixEnd_3477160 198383821398635647689871 := by
  unfold tailWord_3477160
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411222041425323247082467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84548296055233764329443289 63411222041425323247082467)
  ·
    refine ⟨95116833062137984870623701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63411222041425323247082467 95116833062137984870623701)
    ·
      refine ⟨2229300774893859020405243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95116833062137984870623701 2229300774893859020405243)
      ·
        refine ⟨3343951162340788530607865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229300774893859020405243 3343951162340788530607865)
        ·
          refine ⟨2507963371755591397955899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3343951162340788530607865 2507963371755591397955899)
          ·
            refine ⟨3761945057633387096933849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507963371755591397955899 3761945057633387096933849)
            ·
              refine ⟨2821458793225040322700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761945057633387096933849 2821458793225040322700387)
              ·
                refine ⟨4232188189837560484050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821458793225040322700387 4232188189837560484050581)
                ·
                  refine ⟨198383821398635647689871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4232188189837560484050581 198383821398635647689871)
                  ·
                    rfl

theorem cell23_3477160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 6].length) (baseStart_3477160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477160 prefixEnd_3477160 := by exact prefixLift 3477160
  have htrace : WordTrace (prefixWord ++ tailWord_3477160) baseStart_3477160 baseEnd_3477160 := by
    simpa [prefixWord, tailWord_3477160, baseEnd_3477160] using wordTrace_append hprefix tailTrace_3477160
  have hstable : (prefixWord ++ tailWord_3477160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477160).length < 2 ^ (prefixWord ++ tailWord_3477160).sum := by decide
  have hdescent : baseEnd_3477160 < baseStart_3477160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477192 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_3477192 : Nat := 118140960795 + 3477192 * 2 ^ 59
def prefixEnd_3477192 : Nat := 4983230072969 + 3 ^ 40 * 3477192 * 2
def baseEnd_3477192 : Nat := 1785470823968664704008691

theorem tailTrace_3477192 : CollatzResearch.WordTrace tailWord_3477192 prefixEnd_3477192 1785470823968664704008691 := by
  unfold tailWord_3477192
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411805609367357979664915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84549074145823143972886553 63411805609367357979664915)
  ·
    refine ⟨95117708414051036969497373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63411805609367357979664915 95117708414051036969497373)
    ·
      refine ⟨35669140655269138863561515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95117708414051036969497373 35669140655269138863561515)
      ·
        refine ⟨53503710982903708295342273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35669140655269138863561515 53503710982903708295342273)
        ·
          refine ⟨40127783237177781221506705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53503710982903708295342273 40127783237177781221506705)
          ·
            refine ⟨30095837427883335916130029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40127783237177781221506705 30095837427883335916130029)
            ·
              refine ⟨11285939035456250968548761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30095837427883335916130029 11285939035456250968548761)
              ·
                refine ⟨8464454276592188226411571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11285939035456250968548761 8464454276592188226411571)
                ·
                  refine ⟨12696681414888282339617357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464454276592188226411571 12696681414888282339617357)
                  ·
                    refine ⟨4761255530583105877356509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12696681414888282339617357 4761255530583105877356509)
                    ·
                      refine ⟨1785470823968664704008691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761255530583105877356509 1785470823968664704008691)
                      ·
                        rfl

theorem cell23_3477192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_3477192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477192 prefixEnd_3477192 := by exact prefixLift 3477192
  have htrace : WordTrace (prefixWord ++ tailWord_3477192) baseStart_3477192 baseEnd_3477192 := by
    simpa [prefixWord, tailWord_3477192, baseEnd_3477192] using wordTrace_append hprefix tailTrace_3477192
  have hstable : (prefixWord ++ tailWord_3477192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477192).length < 2 ^ (prefixWord ++ tailWord_3477192).sum := by decide
  have hdescent : baseEnd_3477192 < baseStart_3477192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477196 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3477196 : Nat := 118140960795 + 3477196 * 2 ^ 59
def prefixEnd_3477196 : Nat := 4983230072969 + 3 ^ 40 * 3477196 * 2
def baseEnd_3477196 : Nat := 1785472877891282688358673

theorem tailTrace_3477196 : CollatzResearch.WordTrace tailWord_3477196 prefixEnd_3477196 1785472877891282688358673 := by
  unfold tailWord_3477196
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411878555360112321237721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84549171407146816428316961 63411878555360112321237721)
  ·
    refine ⟨47558908916520084240928291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63411878555360112321237721 47558908916520084240928291)
    ·
      refine ⟨71338363374780126361392437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47558908916520084240928291 71338363374780126361392437)
      ·
        refine ⟨6687971566385636846380541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71338363374780126361392437 6687971566385636846380541)
        ·
          refine ⟨2507989337394613817392703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6687971566385636846380541 2507989337394613817392703)
          ·
            refine ⟨3761984006091920726089055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507989337394613817392703 3761984006091920726089055)
            ·
              refine ⟨5642976009137881089133583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761984006091920726089055 5642976009137881089133583)
              ·
                refine ⟨8464464013706821633700375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642976009137881089133583 8464464013706821633700375)
                ·
                  refine ⟨12696696020560232450550563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464464013706821633700375 12696696020560232450550563)
                  ·
                    refine ⟨19045044030840348675825845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12696696020560232450550563 19045044030840348675825845)
                    ·
                      refine ⟨1785472877891282688358673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19045044030840348675825845 1785472877891282688358673)
                      ·
                        rfl

theorem cell23_3477196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3477196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477196 prefixEnd_3477196 := by exact prefixLift 3477196
  have htrace : WordTrace (prefixWord ++ tailWord_3477196) baseStart_3477196 baseEnd_3477196 := by
    simpa [prefixWord, tailWord_3477196, baseEnd_3477196] using wordTrace_append hprefix tailTrace_3477196
  have hstable : (prefixWord ++ tailWord_3477196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477196).length < 2 ^ (prefixWord ++ tailWord_3477196).sum := by decide
  have hdescent : baseEnd_3477196 < baseStart_3477196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477209 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 3]
def baseStart_3477209 : Nat := 118140960795 + 3477209 * 2 ^ 59
def prefixEnd_3477209 : Nat := 4983230072969 + 3 ^ 40 * 3477209 * 2
def baseEnd_3477209 : Nat := 1785479553139791137496113

theorem tailTrace_3477209 : CollatzResearch.WordTrace tailWord_3477209 prefixEnd_3477209 1785479553139791137496113 := by
  unfold tailWord_3477209
  simp only [CollatzResearch.WordTrace]
  refine ⟨126824231259673127862698681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84549487506448751908465787 126824231259673127862698681)
  ·
    refine ⟨95118173444754845897024011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126824231259673127862698681 95118173444754845897024011)
    ·
      refine ⟨142677260167132268845536017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95118173444754845897024011 142677260167132268845536017)
      ·
        refine ⟨107007945125349201634152013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142677260167132268845536017 107007945125349201634152013)
        ·
          refine ⟨40127979422005950612807005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107007945125349201634152013 40127979422005950612807005)
          ·
            refine ⟨15047992283252231479802627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40127979422005950612807005 15047992283252231479802627)
            ·
              refine ⟨22571988424878347219703941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15047992283252231479802627 22571988424878347219703941)
              ·
                refine ⟨4232247829664690103694489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22571988424878347219703941 4232247829664690103694489)
                ·
                  refine ⟨3174185872248517577770867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232247829664690103694489 3174185872248517577770867)
                  ·
                    refine ⟨4761278808372776366656301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174185872248517577770867 4761278808372776366656301)
                    ·
                      refine ⟨1785479553139791137496113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761278808372776366656301 1785479553139791137496113)
                      ·
                        rfl

theorem cell23_3477209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_3477209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477209 prefixEnd_3477209 := by exact prefixLift 3477209
  have htrace : WordTrace (prefixWord ++ tailWord_3477209) baseStart_3477209 baseEnd_3477209 := by
    simpa [prefixWord, tailWord_3477209, baseEnd_3477209] using wordTrace_append hprefix tailTrace_3477209
  have hstable : (prefixWord ++ tailWord_3477209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477209).length < 2 ^ (prefixWord ++ tailWord_3477209).sum := by decide
  have hdescent : baseEnd_3477209 < baseStart_3477209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477210 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2]
def baseStart_3477210 : Nat := 118140960795 + 3477210 * 2 ^ 59
def prefixEnd_3477210 : Nat := 4983230072969 + 3 ^ 40 * 3477210 * 2
def baseEnd_3477210 : Nat := 1785480066620445633583609

theorem tailTrace_3477210 : CollatzResearch.WordTrace tailWord_3477210 prefixEnd_3477210 1785480066620445633583609 := by
  unfold tailWord_3477210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31706066933167376258371271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84549511821779670022323389 31706066933167376258371271)
  ·
    refine ⟨47559100399751064387556907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31706066933167376258371271 47559100399751064387556907)
    ·
      refine ⟨71338650599626596581335361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47559100399751064387556907 71338650599626596581335361)
      ·
        refine ⟨53503987949719947436001521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71338650599626596581335361 53503987949719947436001521)
        ·
          refine ⟨40127990962289960577001141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53503987949719947436001521 40127990962289960577001141)
          ·
            refine ⟨3761999152714683804093857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40127990962289960577001141 3761999152714683804093857)
            ·
              refine ⟨2821499364536012853070393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761999152714683804093857 2821499364536012853070393)
              ·
                refine ⟨2116124523402009639802795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821499364536012853070393 2116124523402009639802795)
                ·
                  refine ⟨3174186785103014459704193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116124523402009639802795 3174186785103014459704193)
                  ·
                    refine ⟨2380640088827260844778145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3174186785103014459704193 2380640088827260844778145)
                    ·
                      refine ⟨1785480066620445633583609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380640088827260844778145 1785480066620445633583609)
                      ·
                        rfl

theorem cell23_3477210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_3477210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477210 prefixEnd_3477210 := by exact prefixLift 3477210
  have htrace : WordTrace (prefixWord ++ tailWord_3477210) baseStart_3477210 baseEnd_3477210 := by
    simpa [prefixWord, tailWord_3477210, baseEnd_3477210] using wordTrace_append hprefix tailTrace_3477210
  have hstable : (prefixWord ++ tailWord_3477210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477210).length < 2 ^ (prefixWord ++ tailWord_3477210).sum := by decide
  have hdescent : baseEnd_3477210 < baseStart_3477210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477215 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_3477215 : Nat := 118140960795 + 3477215 * 2 ^ 59
def prefixEnd_3477215 : Nat := 4983230072969 + 3 ^ 40 * 3477215 * 2
def baseEnd_3477215 : Nat := 1785482634023718114021085

theorem tailTrace_3477215 : CollatzResearch.WordTrace tailWord_3477215 prefixEnd_3477215 1785482634023718114021085 := by
  unfold tailWord_3477215
  simp only [CollatzResearch.WordTrace]
  refine ⟨126824450097651390887417099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84549633398434260591611399 126824450097651390887417099)
  ·
    refine ⟨190236675146477086331125649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126824450097651390887417099 190236675146477086331125649)
    ·
      refine ⟨142677506359857814748344237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190236675146477086331125649 142677506359857814748344237)
      ·
        refine ⟨53504064884946680530629089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142677506359857814748344237 53504064884946680530629089)
        ·
          refine ⟨40128048663710010397971817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53504064884946680530629089 40128048663710010397971817)
          ·
            refine ⟨30096036497782507798478863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40128048663710010397971817 30096036497782507798478863)
            ·
              refine ⟨45144054746673761697718295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30096036497782507798478863 45144054746673761697718295)
              ·
                refine ⟨67716082120010642546577443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45144054746673761697718295 67716082120010642546577443)
                ·
                  refine ⟨101574123180015963819866165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67716082120010642546577443 101574123180015963819866165)
                  ·
                    refine ⟨9522574048126496608112453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101574123180015963819866165 9522574048126496608112453)
                    ·
                      refine ⟨1785482634023718114021085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9522574048126496608112453 1785482634023718114021085)
                      ·
                        rfl

theorem cell23_3477215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_3477215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477215 prefixEnd_3477215 := by exact prefixLift 3477215
  have htrace : WordTrace (prefixWord ++ tailWord_3477215) baseStart_3477215 baseEnd_3477215 := by
    simpa [prefixWord, tailWord_3477215, baseEnd_3477215] using wordTrace_append hprefix tailTrace_3477215
  have hstable : (prefixWord ++ tailWord_3477215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477215).length < 2 ^ (prefixWord ++ tailWord_3477215).sum := by decide
  have hdescent : baseEnd_3477215 < baseStart_3477215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477235 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5]
def baseStart_3477235 : Nat := 118140960795 + 3477235 * 2 ^ 59
def prefixEnd_3477235 : Nat := 4983230072969 + 3 ^ 40 * 3477235 * 2
def baseEnd_3477235 : Nat := 1785492903636808035770993

theorem tailTrace_3477235 : CollatzResearch.WordTrace tailWord_3477235 prefixEnd_3477235 1785492903636808035770993 := by
  unfold tailWord_3477235
  simp only [CollatzResearch.WordTrace]
  refine ⟨126825179557578934303145159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84550119705052622868763439 126825179557578934303145159)
  ·
    refine ⟨190237769336368401454717739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126825179557578934303145159 190237769336368401454717739)
    ·
      refine ⟨285356654004552602182076609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190237769336368401454717739 285356654004552602182076609)
      ·
        refine ⟨214017490503414451636557457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285356654004552602182076609 214017490503414451636557457)
        ·
          refine ⟨160513117877560838727418093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214017490503414451636557457 160513117877560838727418093)
          ·
            refine ⟨60192419204085314522781785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160513117877560838727418093 60192419204085314522781785)
            ·
              refine ⟨45144314403063985892086339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60192419204085314522781785 45144314403063985892086339)
              ·
                refine ⟨67716471604595978838129509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45144314403063985892086339 67716471604595978838129509)
                ·
                  refine ⟨12696838425861746032149283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67716471604595978838129509 12696838425861746032149283)
                  ·
                    refine ⟨19045257638792619048223925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12696838425861746032149283 19045257638792619048223925)
                    ·
                      refine ⟨1785492903636808035770993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19045257638792619048223925 1785492903636808035770993)
                      ·
                        rfl

theorem cell23_3477235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_3477235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477235 prefixEnd_3477235 := by exact prefixLift 3477235
  have htrace : WordTrace (prefixWord ++ tailWord_3477235) baseStart_3477235 baseEnd_3477235 := by
    simpa [prefixWord, tailWord_3477235, baseEnd_3477235] using wordTrace_append hprefix tailTrace_3477235
  have hstable : (prefixWord ++ tailWord_3477235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477235).length < 2 ^ (prefixWord ++ tailWord_3477235).sum := by decide
  have hdescent : baseEnd_3477235 < baseStart_3477235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477249 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_3477249 : Nat := 118140960795 + 3477249 * 2 ^ 59
def prefixEnd_3477249 : Nat := 4983230072969 + 3 ^ 40 * 3477249 * 2
def baseEnd_3477249 : Nat := 1785500092365970980995929

theorem tailTrace_3477249 : CollatzResearch.WordTrace tailWord_3477249 prefixEnd_3477249 1785500092365970980995929 := by
  unfold tailWord_3477249
  simp only [CollatzResearch.WordTrace]
  refine ⟨126825690179528214694154801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84550460119685476462769867 126825690179528214694154801)
  ·
    refine ⟨95119267634646161020616101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126825690179528214694154801 95119267634646161020616101)
    ·
      refine ⟨17834862681496155191365519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95119267634646161020616101 17834862681496155191365519)
      ·
        refine ⟨26752294022244232787048279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17834862681496155191365519 26752294022244232787048279)
        ·
          refine ⟨40128441033366349180572419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26752294022244232787048279 40128441033366349180572419)
          ·
            refine ⟨60192661550049523770858629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40128441033366349180572419 60192661550049523770858629)
            ·
              refine ⟨11286124040634285707035993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60192661550049523770858629 11286124040634285707035993)
              ·
                refine ⟨8464593030475714280276995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11286124040634285707035993 8464593030475714280276995)
                ·
                  refine ⟨12696889545713571420415493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464593030475714280276995 12696889545713571420415493)
                  ·
                    refine ⟨2380666789821294641327905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12696889545713571420415493 2380666789821294641327905)
                    ·
                      refine ⟨1785500092365970980995929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380666789821294641327905 1785500092365970980995929)
                      ·
                        rfl

theorem cell23_3477249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_3477249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477249 prefixEnd_3477249 := by exact prefixLift 3477249
  have htrace : WordTrace (prefixWord ++ tailWord_3477249) baseStart_3477249 baseEnd_3477249 := by
    simpa [prefixWord, tailWord_3477249, baseEnd_3477249] using wordTrace_append hprefix tailTrace_3477249
  have hstable : (prefixWord ++ tailWord_3477249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477249).length < 2 ^ (prefixWord ++ tailWord_3477249).sum := by decide
  have hdescent : baseEnd_3477249 < baseStart_3477249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477254 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3477254 : Nat := 118140960795 + 3477254 * 2 ^ 59
def prefixEnd_3477254 : Nat := 4983230072969 + 3 ^ 40 * 3477254 * 2
def baseEnd_3477254 : Nat := 595167553256414487144469

theorem tailTrace_3477254 : CollatzResearch.WordTrace tailWord_3477254 prefixEnd_3477254 595167553256414487144469 := by
  unfold tailWord_3477254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963308517015940642127713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84550581696340067032057877 3963308517015940642127713)
  ·
    refine ⟨2972481387761955481595785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3963308517015940642127713 2972481387761955481595785)
    ·
      refine ⟨2229361040821466611196839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972481387761955481595785 2229361040821466611196839)
      ·
        refine ⟨3344041561232199916795259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229361040821466611196839 3344041561232199916795259)
        ·
          refine ⟨5016062341848299875192889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344041561232199916795259 5016062341848299875192889)
          ·
            refine ⟨3762046756386224906394667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5016062341848299875192889 3762046756386224906394667)
            ·
              refine ⟨5643070134579337359592001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762046756386224906394667 5643070134579337359592001)
              ·
                refine ⟨4232302600934503019694001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643070134579337359592001 4232302600934503019694001)
                ·
                  refine ⟨3174226950700877264770501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232302600934503019694001 3174226950700877264770501)
                  ·
                    refine ⟨595167553256414487144469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174226950700877264770501 595167553256414487144469)
                    ·
                      rfl

theorem cell23_3477254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3477254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477254 prefixEnd_3477254 := by exact prefixLift 3477254
  have htrace : WordTrace (prefixWord ++ tailWord_3477254) baseStart_3477254 baseEnd_3477254 := by
    simpa [prefixWord, tailWord_3477254, baseEnd_3477254] using wordTrace_append hprefix tailTrace_3477254
  have hstable : (prefixWord ++ tailWord_3477254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477254).length < 2 ^ (prefixWord ++ tailWord_3477254).sum := by decide
  have hdescent : baseEnd_3477254 < baseStart_3477254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477262 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3477262 : Nat := 118140960795 + 3477262 * 2 ^ 59
def prefixEnd_3477262 : Nat := 4983230072969 + 3 ^ 40 * 3477262 * 2
def baseEnd_3477262 : Nat := 1785506767614479430133369

theorem tailTrace_3477262 : CollatzResearch.WordTrace tailWord_3477262 prefixEnd_3477262 1785506767614479430133369 := by
  unfold tailWord_3477262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853270541060139739297255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84550776218987411942918693 15853270541060139739297255)
  ·
    refine ⟨23779905811590209608945883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15853270541060139739297255 23779905811590209608945883)
    ·
      refine ⟨35669858717385314413418825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23779905811590209608945883 35669858717385314413418825)
      ·
        refine ⟨26752394038038985810064119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35669858717385314413418825 26752394038038985810064119)
        ·
          refine ⟨40128591057058478715096179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26752394038038985810064119 40128591057058478715096179)
          ·
            refine ⟨60192886585587718072644269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40128591057058478715096179 60192886585587718072644269)
            ·
              refine ⟨22572332469595394277241601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60192886585587718072644269 22572332469595394277241601)
              ·
                refine ⟨16929249352196545707931201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22572332469595394277241601 16929249352196545707931201)
                ·
                  refine ⟨12696937014147409280948401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16929249352196545707931201 12696937014147409280948401)
                  ·
                    refine ⟨9522702760610556960711301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12696937014147409280948401 9522702760610556960711301)
                    ·
                      refine ⟨1785506767614479430133369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9522702760610556960711301 1785506767614479430133369)
                      ·
                        rfl

theorem cell23_3477262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3477262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477262 prefixEnd_3477262 := by exact prefixLift 3477262
  have htrace : WordTrace (prefixWord ++ tailWord_3477262) baseStart_3477262 baseEnd_3477262 := by
    simpa [prefixWord, tailWord_3477262, baseEnd_3477262] using wordTrace_append hprefix tailTrace_3477262
  have hstable : (prefixWord ++ tailWord_3477262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477262).length < 2 ^ (prefixWord ++ tailWord_3477262).sum := by decide
  have hdescent : baseEnd_3477262 < baseStart_3477262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477295 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_3477295 : Nat := 118140960795 + 3477295 * 2 ^ 59
def prefixEnd_3477295 : Nat := 4983230072969 + 3 ^ 40 * 3477295 * 2
def baseEnd_3477295 : Nat := 1785523712476077801020717

theorem tailTrace_3477295 : CollatzResearch.WordTrace tailWord_3477295 prefixEnd_3477295 1785523712476077801020717 := by
  unfold tailWord_3477295
  simp only [CollatzResearch.WordTrace]
  refine ⟨126827367937361564550329339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84551578624907709700219559 126827367937361564550329339)
  ·
    refine ⟨190241051906042346825494009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126827367937361564550329339 190241051906042346825494009)
    ·
      refine ⟨142680788929531760119120507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190241051906042346825494009 142680788929531760119120507)
      ·
        refine ⟨214021183394297640178680761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142680788929531760119120507 214021183394297640178680761)
        ·
          refine ⟨160515887545723230134010571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214021183394297640178680761 160515887545723230134010571)
          ·
            refine ⟨240773831318584845201015857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160515887545723230134010571 240773831318584845201015857)
            ·
              refine ⟨180580373488938633900761893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240773831318584845201015857 180580373488938633900761893)
              ·
                refine ⟨33858820029175993856392855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180580373488938633900761893 33858820029175993856392855)
                ·
                  refine ⟨50788230043763990784589283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33858820029175993856392855 50788230043763990784589283)
                  ·
                    refine ⟨76182345065645986176883925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50788230043763990784589283 76182345065645986176883925)
                    ·
                      refine ⟨1785523712476077801020717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76182345065645986176883925 1785523712476077801020717)
                      ·
                        rfl

theorem cell23_3477295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_3477295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477295 prefixEnd_3477295 := by exact prefixLift 3477295
  have htrace : WordTrace (prefixWord ++ tailWord_3477295) baseStart_3477295 baseEnd_3477295 := by
    simpa [prefixWord, tailWord_3477295, baseEnd_3477295] using wordTrace_append hprefix tailTrace_3477295
  have hstable : (prefixWord ++ tailWord_3477295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477295).length < 2 ^ (prefixWord ++ tailWord_3477295).sum := by decide
  have hdescent : baseEnd_3477295 < baseStart_3477295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477306 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_3477306 : Nat := 118140960795 + 3477306 * 2 ^ 59
def prefixEnd_3477306 : Nat := 4983230072969 + 3 ^ 40 * 3477306 * 2
def baseEnd_3477306 : Nat := 198392151195919695331463

theorem tailTrace_3477306 : CollatzResearch.WordTrace tailWord_3477306 prefixEnd_3477306 198392151195919695331463 := by
  unfold tailWord_3477306
  simp only [CollatzResearch.WordTrace]
  refine ⟨31706942285080428357244943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84551846093547808952653181 31706942285080428357244943)
  ·
    refine ⟨47560413427620642535867415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31706942285080428357244943 47560413427620642535867415)
    ·
      refine ⟨71340620141430963803801123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47560413427620642535867415 71340620141430963803801123)
      ·
        refine ⟨107010930212146445705701685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71340620141430963803801123 107010930212146445705701685)
        ·
          refine ⟨10032274707388729284909533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107010930212146445705701685 10032274707388729284909533)
          ·
            refine ⟨3762103015270773481841075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10032274707388729284909533 3762103015270773481841075)
            ·
              refine ⟨5643154522906160222761613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762103015270773481841075 5643154522906160222761613)
              ·
                refine ⟨2116182946089810083535605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5643154522906160222761613 2116182946089810083535605)
                ·
                  refine ⟨198392151195919695331463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2116182946089810083535605 198392151195919695331463)
                  ·
                    rfl

theorem cell23_3477306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_3477306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477306 prefixEnd_3477306 := by exact prefixLift 3477306
  have htrace : WordTrace (prefixWord ++ tailWord_3477306) baseStart_3477306 baseEnd_3477306 := by
    simpa [prefixWord, tailWord_3477306, baseEnd_3477306] using wordTrace_append hprefix tailTrace_3477306
  have hstable : (prefixWord ++ tailWord_3477306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477306).length < 2 ^ (prefixWord ++ tailWord_3477306).sum := by decide
  have hdescent : baseEnd_3477306 < baseStart_3477306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477379 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 6]
def baseStart_3477379 : Nat := 118140960795 + 3477379 * 2 ^ 59
def prefixEnd_3477379 : Nat := 4983230072969 + 3 ^ 40 * 3477379 * 2
def baseEnd_3477379 : Nat := 198396316094561719152259

theorem tailTrace_3477379 : CollatzResearch.WordTrace tailWord_3477379 prefixEnd_3477379 198396316094561719152259 := by
  unfold tailWord_3477379
  simp only [CollatzResearch.WordTrace]
  refine ⟨126830431669057246896387191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84553621112704831264258127 126830431669057246896387191)
  ·
    refine ⟨190245647503585870344580787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126830431669057246896387191 190245647503585870344580787)
    ·
      refine ⟨285368471255378805516871181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190245647503585870344580787 285368471255378805516871181)
      ·
        refine ⟨107013176720767052068826693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285368471255378805516871181 107013176720767052068826693)
        ·
          refine ⟨20064970635143822262905005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107013176720767052068826693 20064970635143822262905005)
          ·
            refine ⟨7524363988178933348589377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20064970635143822262905005 7524363988178933348589377)
            ·
              refine ⟨5643272991134200011442033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7524363988178933348589377 5643272991134200011442033)
              ·
                refine ⟨4232454743350650008581525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643272991134200011442033 4232454743350650008581525)
                ·
                  refine ⟨198396316094561719152259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4232454743350650008581525 198396316094561719152259)
                  ·
                    rfl

theorem cell23_3477379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 6].length) (baseStart_3477379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477379 prefixEnd_3477379 := by exact prefixLift 3477379
  have htrace : WordTrace (prefixWord ++ tailWord_3477379) baseStart_3477379 baseEnd_3477379 := by
    simpa [prefixWord, tailWord_3477379, baseEnd_3477379] using wordTrace_append hprefix tailTrace_3477379
  have hstable : (prefixWord ++ tailWord_3477379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477379).length < 2 ^ (prefixWord ++ tailWord_3477379).sum := by decide
  have hdescent : baseEnd_3477379 < baseStart_3477379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477383 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 1, 4]
def baseStart_3477383 : Nat := 118140960795 + 3477383 * 2 ^ 59
def prefixEnd_3477383 : Nat := 4983230072969 + 3 ^ 40 * 3477383 * 2
def baseEnd_3477383 : Nat := 595189632924557818906771

theorem tailTrace_3477383 : CollatzResearch.WordTrace tailWord_3477383 prefixEnd_3477383 595189632924557818906771 := by
  unfold tailWord_3477383
  simp only [CollatzResearch.WordTrace]
  refine ⟨126830577561042755579532803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84553718374028503719688535 126830577561042755579532803)
  ·
    refine ⟨190245866341564133369299205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126830577561042755579532803 190245866341564133369299205)
    ·
      refine ⟨35671099939043275006743601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190245866341564133369299205 35671099939043275006743601)
      ·
        refine ⟨26753324954282456255057701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35671099939043275006743601 26753324954282456255057701)
        ·
          refine ⟨5016248428927960547823319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26753324954282456255057701 5016248428927960547823319)
          ·
            refine ⟨7524372643391940821734979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016248428927960547823319 7524372643391940821734979)
            ·
              refine ⟨11286558965087911232602469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524372643391940821734979 11286558965087911232602469)
              ·
                refine ⟨2116229805953983356112963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11286558965087911232602469 2116229805953983356112963)
                ·
                  refine ⟨3174344708930975034169445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116229805953983356112963 3174344708930975034169445)
                  ·
                    refine ⟨595189632924557818906771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174344708930975034169445 595189632924557818906771)
                    ·
                      rfl

theorem cell23_3477383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_3477383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477383 prefixEnd_3477383 := by exact prefixLift 3477383
  have htrace : WordTrace (prefixWord ++ tailWord_3477383) baseStart_3477383 baseEnd_3477383 := by
    simpa [prefixWord, tailWord_3477383, baseEnd_3477383] using wordTrace_append hprefix tailTrace_3477383
  have hstable : (prefixWord ++ tailWord_3477383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477383).length < 2 ^ (prefixWord ++ tailWord_3477383).sum := by decide
  have hdescent : baseEnd_3477383 < baseStart_3477383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477392 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_3477392 : Nat := 118140960795 + 3477392 * 2 ^ 59
def prefixEnd_3477392 : Nat := 4983230072969 + 3 ^ 40 * 3477392 * 2
def baseEnd_3477392 : Nat := 595191173366521307169257

theorem tailTrace_3477392 : CollatzResearch.WordTrace tailWord_3477392 prefixEnd_3477392 595191173366521307169257 := by
  unfold tailWord_3477392
  simp only [CollatzResearch.WordTrace]
  refine ⟨63415452909005075058305215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84553937212006766744406953 63415452909005075058305215)
  ·
    refine ⟨95123179363507612587457823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63415452909005075058305215 95123179363507612587457823)
    ·
      refine ⟨142684769045261418881186735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95123179363507612587457823 142684769045261418881186735)
      ·
        refine ⟨214027153567892128321780103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142684769045261418881186735 214027153567892128321780103)
        ·
          refine ⟨321040730351838192482670155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214027153567892128321780103 321040730351838192482670155)
          ·
            refine ⟨481561095527757288724005233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321040730351838192482670155 481561095527757288724005233)
            ·
              refine ⟨361170821645817966543003925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481561095527757288724005233 361170821645817966543003925)
              ·
                refine ⟨16929882264647717181703309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361170821645817966543003925 16929882264647717181703309)
                ·
                  refine ⟨6348705849242893943138741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16929882264647717181703309 6348705849242893943138741)
                  ·
                    refine ⟨595191173366521307169257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6348705849242893943138741 595191173366521307169257)
                    ·
                      rfl

theorem cell23_3477392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_3477392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477392 prefixEnd_3477392 := by exact prefixLift 3477392
  have htrace : WordTrace (prefixWord ++ tailWord_3477392) baseStart_3477392 baseEnd_3477392 := by
    simpa [prefixWord, tailWord_3477392, baseEnd_3477392] using wordTrace_append hprefix tailTrace_3477392
  have hstable : (prefixWord ++ tailWord_3477392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477392).length < 2 ^ (prefixWord ++ tailWord_3477392).sum := by decide
  have hdescent : baseEnd_3477392 < baseStart_3477392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477410 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_3477410 : Nat := 118140960795 + 3477410 * 2 ^ 59
def prefixEnd_3477410 : Nat := 4983230072969 + 3 ^ 40 * 3477410 * 2
def baseEnd_3477410 : Nat := 1785582762751344851082689

theorem tailTrace_3477410 : CollatzResearch.WordTrace tailWord_3477410 prefixEnd_3477410 1785582762751344851082689 := by
  unfold tailWord_3477410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31707890582986234797691421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84554374887963292793843789 31707890582986234797691421)
  ·
    refine ⟨11890458968619838049134283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31707890582986234797691421 11890458968619838049134283)
    ·
      refine ⟨17835688452929757073701425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11890458968619838049134283 17835688452929757073701425)
      ·
        refine ⟨13376766339697317805276069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17835688452929757073701425 13376766339697317805276069)
        ·
          refine ⟨2508143688693247088489263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13376766339697317805276069 2508143688693247088489263)
          ·
            refine ⟨3762215533039870632733895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508143688693247088489263 3762215533039870632733895)
            ·
              refine ⟨5643323299559805949100843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762215533039870632733895 5643323299559805949100843)
              ·
                refine ⟨8464984949339708923651265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643323299559805949100843 8464984949339708923651265)
                ·
                  refine ⟨6348738712004781692738449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8464984949339708923651265 6348738712004781692738449)
                  ·
                    refine ⟨4761554034003586269553837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6348738712004781692738449 4761554034003586269553837)
                    ·
                      refine ⟨1785582762751344851082689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761554034003586269553837 1785582762751344851082689)
                      ·
                        rfl

theorem cell23_3477410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_3477410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477410 prefixEnd_3477410 := by exact prefixLift 3477410
  have htrace : WordTrace (prefixWord ++ tailWord_3477410) baseStart_3477410 baseEnd_3477410 := by
    simpa [prefixWord, tailWord_3477410, baseEnd_3477410] using wordTrace_append hprefix tailTrace_3477410
  have hstable : (prefixWord ++ tailWord_3477410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477410).length < 2 ^ (prefixWord ++ tailWord_3477410).sum := by decide
  have hdescent : baseEnd_3477410 < baseStart_3477410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477423 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 1, 1, 3]
def baseStart_3477423 : Nat := 118140960795 + 3477423 * 2 ^ 59
def prefixEnd_3477423 : Nat := 4983230072969 + 3 ^ 40 * 3477423 * 2
def baseEnd_3477423 : Nat := 1785589437999853300220129

theorem tailTrace_3477423 : CollatzResearch.WordTrace tailWord_3477423 prefixEnd_3477423 1785589437999853300220129 := by
  unfold tailWord_3477423
  simp only [CollatzResearch.WordTrace]
  refine ⟨126832036480897842410988923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84554690987265228273992615 126832036480897842410988923)
  ·
    refine ⟨190248054721346763616483385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126832036480897842410988923 190248054721346763616483385)
    ·
      refine ⟨142686041041010072712362539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190248054721346763616483385 142686041041010072712362539)
      ·
        refine ⟨214029061561515109068543809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142686041041010072712362539 214029061561515109068543809)
        ·
          refine ⟨160521796171136331801407857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214029061561515109068543809 160521796171136331801407857)
          ·
            refine ⟨120391347128352248851055893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160521796171136331801407857 120391347128352248851055893)
            ·
              refine ⟨5643344396641511664893245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120391347128352248851055893 5643344396641511664893245)
              ·
                refine ⟨2116254148740566874334967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5643344396641511664893245 2116254148740566874334967)
                ·
                  refine ⟨3174381223110850311502451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116254148740566874334967 3174381223110850311502451)
                  ·
                    refine ⟨4761571834666275467253677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174381223110850311502451 4761571834666275467253677)
                    ·
                      refine ⟨1785589437999853300220129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761571834666275467253677 1785589437999853300220129)
                      ·
                        rfl

theorem cell23_3477423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 1, 3].length) (baseStart_3477423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477423 prefixEnd_3477423 := by exact prefixLift 3477423
  have htrace : WordTrace (prefixWord ++ tailWord_3477423) baseStart_3477423 baseEnd_3477423 := by
    simpa [prefixWord, tailWord_3477423, baseEnd_3477423] using wordTrace_append hprefix tailTrace_3477423
  have hstable : (prefixWord ++ tailWord_3477423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477423).length < 2 ^ (prefixWord ++ tailWord_3477423).sum := by decide
  have hdescent : baseEnd_3477423 < baseStart_3477423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
