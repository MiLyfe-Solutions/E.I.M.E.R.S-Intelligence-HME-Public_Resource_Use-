import V185TrunkScan22Chunk434

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3877352 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3877352 : Nat := 118140960795 + 3877352 * 2 ^ 59
def prefixEnd_3877352 : Nat := 4983230072969 + 3 ^ 40 * 3877352 * 2
def baseEnd_3877352 : Nat := 1327296828447879384112259

theorem tailTrace_3877352 : CollatzResearch.WordTrace tailWord_3877352 prefixEnd_3877352 1327296828447879384112259 := by
  unfold tailWord_3877352
  simp only [CollatzResearch.WordTrace]
  refine ⟨70709322724511688923177155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94279096966015585230902873 70709322724511688923177155)
  ·
    refine ⟨106063984086767533384765733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70709322724511688923177155 106063984086767533384765733)
    ·
      refine ⟨19886997016268912509643575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106063984086767533384765733 19886997016268912509643575)
      ·
        refine ⟨29830495524403368764465363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19886997016268912509643575 29830495524403368764465363)
        ·
          refine ⟨44745743286605053146698045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29830495524403368764465363 44745743286605053146698045)
          ·
            refine ⟨16779653732476894930011767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44745743286605053146698045 16779653732476894930011767)
            ·
              refine ⟨25169480598715342395017651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16779653732476894930011767 25169480598715342395017651)
              ·
                refine ⟨37754220898073013592526477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25169480598715342395017651 37754220898073013592526477)
                ·
                  refine ⟨14157832836777380097197429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37754220898073013592526477 14157832836777380097197429)
                  ·
                    refine ⟨1327296828447879384112259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14157832836777380097197429 1327296828447879384112259)
                    ·
                      rfl

theorem cell22_3877352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3877352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877352 prefixEnd_3877352 := by exact prefixLift 3877352
  have htrace : WordTrace (prefixWord ++ tailWord_3877352) baseStart_3877352 baseEnd_3877352 := by
    simpa [prefixWord, tailWord_3877352, baseEnd_3877352] using wordTrace_append hprefix tailTrace_3877352
  have hstable : (prefixWord ++ tailWord_3877352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877352).length < 2 ^ (prefixWord ++ tailWord_3877352).sum := by decide
  have hdescent : baseEnd_3877352 < baseStart_3877352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877369 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_3877369 : Nat := 118140960795 + 3877369 * 2 ^ 59
def prefixEnd_3877369 : Nat := 4983230072969 + 3 ^ 40 * 3877369 * 2
def baseEnd_3877369 : Nat := 1327302647895297006437207

theorem tailTrace_3877369 : CollatzResearch.WordTrace tailWord_3877369 prefixEnd_3877369 1327302647895297006437207 := by
  unfold tailWord_3877369
  simp only [CollatzResearch.WordTrace]
  refine ⟨141419265489961789749723161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94279510326641193166482107 141419265489961789749723161)
  ·
    refine ⟨106064449117471342312292371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141419265489961789749723161 106064449117471342312292371)
    ·
      refine ⟨159096673676207013468438557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106064449117471342312292371 159096673676207013468438557)
      ·
        refine ⟨59661252628577630050664459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159096673676207013468438557 59661252628577630050664459)
        ·
          refine ⟨89491878942866445075996689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59661252628577630050664459 89491878942866445075996689)
          ·
            refine ⟨67118909207149833806997517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89491878942866445075996689 67118909207149833806997517)
            ·
              refine ⟨25169590952681187677624069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67118909207149833806997517 25169590952681187677624069)
              ·
                refine ⟨4719298303627722689554513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25169590952681187677624069 4719298303627722689554513)
                ·
                  refine ⟨3539473727720792017165885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4719298303627722689554513 3539473727720792017165885)
                  ·
                    refine ⟨1327302647895297006437207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539473727720792017165885 1327302647895297006437207)
                    ·
                      rfl

theorem cell22_3877369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_3877369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877369 prefixEnd_3877369 := by exact prefixLift 3877369
  have htrace : WordTrace (prefixWord ++ tailWord_3877369) baseStart_3877369 baseEnd_3877369 := by
    simpa [prefixWord, tailWord_3877369, baseEnd_3877369] using wordTrace_append hprefix tailTrace_3877369
  have hstable : (prefixWord ++ tailWord_3877369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877369).length < 2 ^ (prefixWord ++ tailWord_3877369).sum := by decide
  have hdescent : baseEnd_3877369 < baseStart_3877369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877427 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 7]
def baseStart_3877427 : Nat := 118140960795 + 3877427 * 2 ^ 59
def prefixEnd_3877427 : Nat := 4983230072969 + 3 ^ 40 * 3877427 * 2
def baseEnd_3877427 : Nat := 442440834160201396162343

theorem tailTrace_3877427 : CollatzResearch.WordTrace tailWord_3877427 prefixEnd_3877427 442440834160201396162343 := by
  unfold tailWord_3877427
  simp only [CollatzResearch.WordTrace]
  refine ⟨141421380923751665655334535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94280920615834443770223023 141421380923751665655334535)
  ·
    refine ⟨212132071385627498483001803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141421380923751665655334535 212132071385627498483001803)
    ·
      refine ⟨318198107078441247724502705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212132071385627498483001803 318198107078441247724502705)
      ·
        refine ⟨238648580308830935793377029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318198107078441247724502705 238648580308830935793377029)
        ·
          refine ⟨44746608807905800461258193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238648580308830935793377029 44746608807905800461258193)
          ·
            refine ⟨33559956605929350345943645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44746608807905800461258193 33559956605929350345943645)
            ·
              refine ⟨12584983727223506379728867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33559956605929350345943645 12584983727223506379728867)
              ·
                refine ⟨18877475590835259569593301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584983727223506379728867 18877475590835259569593301)
                ·
                  refine ⟨442440834160201396162343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18877475590835259569593301 442440834160201396162343)
                  ·
                    rfl

theorem cell22_3877427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_3877427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877427 prefixEnd_3877427 := by exact prefixLift 3877427
  have htrace : WordTrace (prefixWord ++ tailWord_3877427) baseStart_3877427 baseEnd_3877427 := by
    simpa [prefixWord, tailWord_3877427, baseEnd_3877427] using wordTrace_append hprefix tailTrace_3877427
  have hstable : (prefixWord ++ tailWord_3877427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877427).length < 2 ^ (prefixWord ++ tailWord_3877427).sum := by decide
  have hdescent : baseEnd_3877427 < baseStart_3877427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877431 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 1, 3]
def baseStart_3877431 : Nat := 118140960795 + 3877431 * 2 ^ 59
def prefixEnd_3877431 : Nat := 4983230072969 + 3 ^ 40 * 3877431 * 2
def baseEnd_3877431 : Nat := 1327323871762349511387017

theorem tailTrace_3877431 : CollatzResearch.WordTrace tailWord_3877431 prefixEnd_3877431 1327323871762349511387017 := by
  unfold tailWord_3877431
  simp only [CollatzResearch.WordTrace]
  refine ⟨141421526815737174338480147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94281017877158116225653431 141421526815737174338480147)
  ·
    refine ⟨212132290223605761507720221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141421526815737174338480147 212132290223605761507720221)
    ·
      refine ⟨79549608833852160565395083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212132290223605761507720221 79549608833852160565395083)
      ·
        refine ⟨119324413250778240848092625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79549608833852160565395083 119324413250778240848092625)
        ·
          refine ⟨89493309938083680636069469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119324413250778240848092625 89493309938083680636069469)
          ·
            refine ⟨33559991226781380238526051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89493309938083680636069469 33559991226781380238526051)
            ·
              refine ⟨50339986840172070357789077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33559991226781380238526051 50339986840172070357789077)
              ·
                refine ⟨2359686883133065798021363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50339986840172070357789077 2359686883133065798021363)
                ·
                  refine ⟨3539530324699598697032045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359686883133065798021363 3539530324699598697032045)
                  ·
                    refine ⟨1327323871762349511387017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539530324699598697032045 1327323871762349511387017)
                    ·
                      rfl

theorem cell22_3877431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_3877431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877431 prefixEnd_3877431 := by exact prefixLift 3877431
  have htrace : WordTrace (prefixWord ++ tailWord_3877431) baseStart_3877431 baseEnd_3877431 := by
    simpa [prefixWord, tailWord_3877431, baseEnd_3877431] using wordTrace_append hprefix tailTrace_3877431
  have hstable : (prefixWord ++ tailWord_3877431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877431).length < 2 ^ (prefixWord ++ tailWord_3877431).sum := by decide
  have hdescent : baseEnd_3877431 < baseStart_3877431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877472 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_3877472 : Nat := 118140960795 + 3877472 * 2 ^ 59
def prefixEnd_3877472 : Nat := 4983230072969 + 3 ^ 40 * 3877472 * 2
def baseEnd_3877472 : Nat := 442445968966746357037297

theorem tailTrace_3877472 : CollatzResearch.WordTrace tailWord_3877472 prefixEnd_3877472 442445968966746357037297 := by
  unfold tailWord_3877472
  simp only [CollatzResearch.WordTrace]
  refine ⟨70711511104294319170361335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94282014805725758893815113 70711511104294319170361335)
  ·
    refine ⟨106067266656441478755542003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70711511104294319170361335 106067266656441478755542003)
    ·
      refine ⟨159100899984662218133313005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106067266656441478755542003 159100899984662218133313005)
      ·
        refine ⟨59662837494248331799992377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159100899984662218133313005 59662837494248331799992377)
        ·
          refine ⟨44747128120686248849994283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59662837494248331799992377 44747128120686248849994283)
          ·
            refine ⟨67120692181029373274991425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44747128120686248849994283 67120692181029373274991425)
            ·
              refine ⟨50340519135772029956243569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67120692181029373274991425 50340519135772029956243569)
              ·
                refine ⟨37755389351829022467182677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50340519135772029956243569 37755389351829022467182677)
                ·
                  refine ⟨442445968966746357037297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37755389351829022467182677 442445968966746357037297)
                  ·
                    rfl

theorem cell22_3877472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_3877472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877472 prefixEnd_3877472 := by exact prefixLift 3877472
  have htrace : WordTrace (prefixWord ++ tailWord_3877472) baseStart_3877472 baseEnd_3877472 := by
    simpa [prefixWord, tailWord_3877472, baseEnd_3877472] using wordTrace_append hprefix tailTrace_3877472
  have hstable : (prefixWord ++ tailWord_3877472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877472).length < 2 ^ (prefixWord ++ tailWord_3877472).sum := by decide
  have hdescent : baseEnd_3877472 < baseStart_3877472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877508 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_3877508 : Nat := 118140960795 + 3877508 * 2 ^ 59
def prefixEnd_3877508 : Nat := 4983230072969 + 3 ^ 40 * 3877508 * 2
def baseEnd_3877508 : Nat := 1327350230435946977211781

theorem tailTrace_3877508 : CollatzResearch.WordTrace tailWord_3877508 prefixEnd_3877508 1327350230435946977211781 := by
  unfold tailWord_3877508
  simp only [CollatzResearch.WordTrace]
  refine ⟨70712167618229108244516589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94282890157638810992688785 70712167618229108244516589)
  ·
    refine ⟨26517062856835915591693721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70712167618229108244516589 26517062856835915591693721)
    ·
      refine ⟨19887797142626936693770291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26517062856835915591693721 19887797142626936693770291)
      ·
        refine ⟨29831695713940405040655437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19887797142626936693770291 29831695713940405040655437)
        ·
          refine ⟨11186885892727651890245789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29831695713940405040655437 11186885892727651890245789)
          ·
            refine ⟨4195082209772869458842171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11186885892727651890245789 4195082209772869458842171)
            ·
              refine ⟨6292623314659304188263257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195082209772869458842171 6292623314659304188263257)
              ·
                refine ⟨4719467485994478141197443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6292623314659304188263257 4719467485994478141197443)
                ·
                  refine ⟨7079201228991717211796165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719467485994478141197443 7079201228991717211796165)
                  ·
                    refine ⟨1327350230435946977211781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079201228991717211796165 1327350230435946977211781)
                    ·
                      rfl

theorem cell22_3877508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_3877508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877508 prefixEnd_3877508 := by exact prefixLift 3877508
  have htrace : WordTrace (prefixWord ++ tailWord_3877508) baseStart_3877508 baseEnd_3877508 := by
    simpa [prefixWord, tailWord_3877508, baseEnd_3877508] using wordTrace_append hprefix tailTrace_3877508
  have hstable : (prefixWord ++ tailWord_3877508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877508).length < 2 ^ (prefixWord ++ tailWord_3877508).sum := by decide
  have hdescent : baseEnd_3877508 < baseStart_3877508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877564 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_3877564 : Nat := 118140960795 + 3877564 * 2 ^ 59
def prefixEnd_3877564 : Nat := 4983230072969 + 3 ^ 40 * 3877564 * 2
def baseEnd_3877564 : Nat := 1327369400380381497811609

theorem tailTrace_3877564 : CollatzResearch.WordTrace tailWord_3877564 prefixEnd_3877564 1327369400380381497811609 := by
  unfold tailWord_3877564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70713188862127669026535873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94284251816170225368714497 70713188862127669026535873)
  ·
    refine ⟨53034891646595751769901905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70713188862127669026535873 53034891646595751769901905)
    ·
      refine ⟨39776168734946813827426429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53034891646595751769901905 39776168734946813827426429)
      ·
        refine ⟨14916063275605055185284911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39776168734946813827426429 14916063275605055185284911)
        ·
          refine ⟨22374094913407582777927367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916063275605055185284911 22374094913407582777927367)
          ·
            refine ⟨33561142370111374166891051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22374094913407582777927367 33561142370111374166891051)
            ·
              refine ⟨50341713555167061250336577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33561142370111374166891051 50341713555167061250336577)
              ·
                refine ⟨37756285166375295937752433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50341713555167061250336577 37756285166375295937752433)
                ·
                  refine ⟨28317213874781471953314325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37756285166375295937752433 28317213874781471953314325)
                  ·
                    refine ⟨1327369400380381497811609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28317213874781471953314325 1327369400380381497811609)
                    ·
                      rfl

theorem cell22_3877564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_3877564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877564 prefixEnd_3877564 := by exact prefixLift 3877564
  have htrace : WordTrace (prefixWord ++ tailWord_3877564) baseStart_3877564 baseEnd_3877564 := by
    simpa [prefixWord, tailWord_3877564, baseEnd_3877564] using wordTrace_append hprefix tailTrace_3877564
  have hstable : (prefixWord ++ tailWord_3877564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877564).length < 2 ^ (prefixWord ++ tailWord_3877564).sum := by decide
  have hdescent : baseEnd_3877564 < baseStart_3877564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877594 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_3877594 : Nat := 118140960795 + 3877594 * 2 ^ 59
def prefixEnd_3877594 : Nat := 4983230072969 + 3 ^ 40 * 3877594 * 2
def baseEnd_3877594 : Nat := 1327379669993471419561517

theorem tailTrace_3877594 : CollatzResearch.WordTrace tailWord_3877594 prefixEnd_3877594 1327379669993471419561517 := by
  unfold tailWord_3877594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356867978536663294165959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94284981276097768784442557 35356867978536663294165959)
  ·
    refine ⟨53035301967804994941248939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35356867978536663294165959 53035301967804994941248939)
    ·
      refine ⟨79552952951707492411873409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53035301967804994941248939 79552952951707492411873409)
      ·
        refine ⟨59664714713780619308905057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79552952951707492411873409 59664714713780619308905057)
        ·
          refine ⟨44748536035335464481678793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59664714713780619308905057 44748536035335464481678793)
          ·
            refine ⟨33561402026501598361259095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44748536035335464481678793 33561402026501598361259095)
            ·
              refine ⟨50342103039752397541888643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33561402026501598361259095 50342103039752397541888643)
              ·
                refine ⟨75513154559628596312832965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50342103039752397541888643 75513154559628596312832965)
                ·
                  refine ⟨14158716479930361808656181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75513154559628596312832965 14158716479930361808656181)
                  ·
                    refine ⟨1327379669993471419561517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14158716479930361808656181 1327379669993471419561517)
                    ·
                      rfl

theorem cell22_3877594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_3877594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877594 prefixEnd_3877594 := by exact prefixLift 3877594
  have htrace : WordTrace (prefixWord ++ tailWord_3877594) baseStart_3877594 baseEnd_3877594 := by
    simpa [prefixWord, tailWord_3877594, baseEnd_3877594] using wordTrace_append hprefix tailTrace_3877594
  have hstable : (prefixWord ++ tailWord_3877594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877594).length < 2 ^ (prefixWord ++ tailWord_3877594).sum := by decide
  have hdescent : baseEnd_3877594 < baseStart_3877594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877609 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_3877609 : Nat := 118140960795 + 3877609 * 2 ^ 59
def prefixEnd_3877609 : Nat := 4983230072969 + 3 ^ 40 * 3877609 * 2
def baseEnd_3877609 : Nat := 1327384804800016380436471

theorem tailTrace_3877609 : CollatzResearch.WordTrace tailWord_3877609 prefixEnd_3877609 1327384804800016380436471 := by
  unfold tailWord_3877609
  simp only [CollatzResearch.WordTrace]
  refine ⟨141428019009092310738459881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94285346006061540492306587 141428019009092310738459881)
  ·
    refine ⟨106071014256819233053844911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141428019009092310738459881 106071014256819233053844911)
    ·
      refine ⟨159106521385228849580767367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106071014256819233053844911 159106521385228849580767367)
      ·
        refine ⟨238659782077843274371151051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159106521385228849580767367 238659782077843274371151051)
        ·
          refine ⟨357989673116764911556726577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238659782077843274371151051 357989673116764911556726577)
          ·
            refine ⟨268492254837573683667544933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357989673116764911556726577 268492254837573683667544933)
            ·
              refine ⟨50342297782045065687664675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268492254837573683667544933 50342297782045065687664675)
              ·
                refine ⟨75513446673067598531497013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50342297782045065687664675 75513446673067598531497013)
                ·
                  refine ⟨7079385625600087362327845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75513446673067598531497013 7079385625600087362327845)
                  ·
                    refine ⟨1327384804800016380436471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079385625600087362327845 1327384804800016380436471)
                    ·
                      rfl

theorem cell22_3877609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_3877609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877609 prefixEnd_3877609 := by exact prefixLift 3877609
  have htrace : WordTrace (prefixWord ++ tailWord_3877609) baseStart_3877609 baseEnd_3877609 := by
    simpa [prefixWord, tailWord_3877609, baseEnd_3877609] using wordTrace_append hprefix tailTrace_3877609
  have hstable : (prefixWord ++ tailWord_3877609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877609).length < 2 ^ (prefixWord ++ tailWord_3877609).sum := by decide
  have hdescent : baseEnd_3877609 < baseStart_3877609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877613 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 5]
def baseStart_3877613 : Nat := 118140960795 + 3877613 * 2 ^ 59
def prefixEnd_3877613 : Nat := 4983230072969 + 3 ^ 40 * 3877613 * 2
def baseEnd_3877613 : Nat := 442462058027253901112153

theorem tailTrace_3877613 : CollatzResearch.WordTrace tailWord_3877613 prefixEnd_3877613 442462058027253901112153 := by
  unfold tailWord_3877613
  simp only [CollatzResearch.WordTrace]
  refine ⟨141428164901077819421605493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94285443267385212947736995 141428164901077819421605493)
  ·
    refine ⟨13258890459476045570775515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141428164901077819421605493 13258890459476045570775515)
    ·
      refine ⟨19888335689214068356163273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13258890459476045570775515 19888335689214068356163273)
      ·
        refine ⟨14916251766910551267122455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19888335689214068356163273 14916251766910551267122455)
        ·
          refine ⟨22374377650365826900683683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916251766910551267122455 22374377650365826900683683)
          ·
            refine ⟨33561566475548740351025525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22374377650365826900683683 33561566475548740351025525)
            ·
              refine ⟨3146396857082694407908643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33561566475548740351025525 3146396857082694407908643)
              ·
                refine ⟨4719595285624041611862965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146396857082694407908643 4719595285624041611862965)
                ·
                  refine ⟨442462058027253901112153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4719595285624041611862965 442462058027253901112153)
                  ·
                    rfl

theorem cell22_3877613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_3877613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877613 prefixEnd_3877613 := by exact prefixLift 3877613
  have htrace : WordTrace (prefixWord ++ tailWord_3877613) baseStart_3877613 baseEnd_3877613 := by
    simpa [prefixWord, tailWord_3877613, baseEnd_3877613] using wordTrace_append hprefix tailTrace_3877613
  have hstable : (prefixWord ++ tailWord_3877613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877613).length < 2 ^ (prefixWord ++ tailWord_3877613).sum := by decide
  have hdescent : baseEnd_3877613 < baseStart_3877613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877624 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_3877624 : Nat := 118140960795 + 3877624 * 2 ^ 59
def prefixEnd_3877624 : Nat := 4983230072969 + 3 ^ 40 * 3877624 * 2
def baseEnd_3877624 : Nat := 442463313202187113770475

theorem tailTrace_3877624 : CollatzResearch.WordTrace tailWord_3877624 prefixEnd_3877624 442463313202187113770475 := by
  unfold tailWord_3877624
  simp only [CollatzResearch.WordTrace]
  refine ⟨70714283052018984150127963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94285710736025312200170617 70714283052018984150127963)
  ·
    refine ⟨106071424578028476225191945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70714283052018984150127963 106071424578028476225191945)
    ·
      refine ⟨79553568433521357168893959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106071424578028476225191945 79553568433521357168893959)
      ·
        refine ⟨119330352650282035753340939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79553568433521357168893959 119330352650282035753340939)
        ·
          refine ⟨178995528975423053630011409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119330352650282035753340939 178995528975423053630011409)
          ·
            refine ⟨134246646731567290222508557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178995528975423053630011409 134246646731567290222508557)
            ·
              refine ⟨50342492524337733833440709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134246646731567290222508557 50342492524337733833440709)
              ·
                refine ⟨9439217348313325093770133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50342492524337733833440709 9439217348313325093770133)
                ·
                  refine ⟨442463313202187113770475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9439217348313325093770133 442463313202187113770475)
                  ·
                    rfl

theorem cell22_3877624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_3877624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877624 prefixEnd_3877624 := by exact prefixLift 3877624
  have htrace : WordTrace (prefixWord ++ tailWord_3877624) baseStart_3877624 baseEnd_3877624 := by
    simpa [prefixWord, tailWord_3877624, baseEnd_3877624] using wordTrace_append hprefix tailTrace_3877624
  have hstable : (prefixWord ++ tailWord_3877624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877624).length < 2 ^ (prefixWord ++ tailWord_3877624).sum := by decide
  have hdescent : baseEnd_3877624 < baseStart_3877624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877626 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_3877626 : Nat := 118140960795 + 3877626 * 2 ^ 59
def prefixEnd_3877626 : Nat := 4983230072969 + 3 ^ 40 * 3877626 * 2
def baseEnd_3877626 : Nat := 1327390624247434002761419

theorem tailTrace_3877626 : CollatzResearch.WordTrace tailWord_3877626 prefixEnd_3877626 1327390624247434002761419 := by
  unfold tailWord_3877626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35357159762507680660457183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94285759366687148427885821 35357159762507680660457183)
  ·
    refine ⟨53035739643761520990685775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35357159762507680660457183 53035739643761520990685775)
    ·
      refine ⟨79553609465642281486028663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53035739643761520990685775 79553609465642281486028663)
      ·
        refine ⟨119330414198463422229042995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79553609465642281486028663 119330414198463422229042995)
        ·
          refine ⟨178995621297695133343564493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119330414198463422229042995 178995621297695133343564493)
          ·
            refine ⟨67123357986635675003836685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178995621297695133343564493 67123357986635675003836685)
            ·
              refine ⟨25171259244988378126438757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67123357986635675003836685 25171259244988378126438757)
              ·
                refine ⟨4719611108435320898707267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25171259244988378126438757 4719611108435320898707267)
                ·
                  refine ⟨7079416662652981348060901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719611108435320898707267 7079416662652981348060901)
                  ·
                    refine ⟨1327390624247434002761419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079416662652981348060901 1327390624247434002761419)
                    ·
                      rfl

theorem cell22_3877626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_3877626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877626 prefixEnd_3877626 := by exact prefixLift 3877626
  have htrace : WordTrace (prefixWord ++ tailWord_3877626) baseStart_3877626 baseEnd_3877626 := by
    simpa [prefixWord, tailWord_3877626, baseEnd_3877626] using wordTrace_append hprefix tailTrace_3877626
  have hstable : (prefixWord ++ tailWord_3877626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877626).length < 2 ^ (prefixWord ++ tailWord_3877626).sum := by decide
  have hdescent : baseEnd_3877626 < baseStart_3877626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877701 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_3877701 : Nat := 118140960795 + 3877701 * 2 ^ 59
def prefixEnd_3877701 : Nat := 4983230072969 + 3 ^ 40 * 3877701 * 2
def baseEnd_3877701 : Nat := 1327416298280158807136189

theorem tailTrace_3877701 : CollatzResearch.WordTrace tailWord_3877701 prefixEnd_3877701 1327416298280158807136189 := by
  unfold tailWord_3877701
  simp only [CollatzResearch.WordTrace]
  refine ⟨141431374524759010450808957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94287583016506006967205971 141431374524759010450808957)
  ·
    refine ⟨53036765446784628919053359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141431374524759010450808957 53036765446784628919053359)
    ·
      refine ⟨79555148170176943378580039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53036765446784628919053359 79555148170176943378580039)
      ·
        refine ⟨119332722255265415067870059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79555148170176943378580039 119332722255265415067870059)
        ·
          refine ⟨178999083382898122601805089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119332722255265415067870059 178999083382898122601805089)
          ·
            refine ⟨134249312537173591951353817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178999083382898122601805089 134249312537173591951353817)
            ·
              refine ⟨100686984402880193963515363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134249312537173591951353817 100686984402880193963515363)
              ·
                refine ⟨151030476604320290945273045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100686984402880193963515363 151030476604320290945273045)
                ·
                  refine ⟨3539776795413756819029837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 151030476604320290945273045 3539776795413756819029837)
                  ·
                    refine ⟨1327416298280158807136189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539776795413756819029837 1327416298280158807136189)
                    ·
                      rfl

theorem cell22_3877701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_3877701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877701 prefixEnd_3877701 := by exact prefixLift 3877701
  have htrace : WordTrace (prefixWord ++ tailWord_3877701) baseStart_3877701 baseEnd_3877701 := by
    simpa [prefixWord, tailWord_3877701, baseEnd_3877701] using wordTrace_append hprefix tailTrace_3877701
  have hstable : (prefixWord ++ tailWord_3877701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877701).length < 2 ^ (prefixWord ++ tailWord_3877701).sum := by decide
  have hdescent : baseEnd_3877701 < baseStart_3877701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877709 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3877709 : Nat := 118140960795 + 3877709 * 2 ^ 59
def prefixEnd_3877709 : Nat := 4983230072969 + 3 ^ 40 * 3877709 * 2
def baseEnd_3877709 : Nat := 442473012281216484312055

theorem tailTrace_3877709 : CollatzResearch.WordTrace tailWord_3877709 prefixEnd_3877709 442473012281216484312055 := by
  unfold tailWord_3877709
  simp only [CollatzResearch.WordTrace]
  refine ⟨141431666308730027817100181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94287777539153351878066787 141431666308730027817100181)
  ·
    refine ⟨6629609358221720053926571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141431666308730027817100181 6629609358221720053926571)
    ·
      refine ⟨9944414037332580080889857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6629609358221720053926571 9944414037332580080889857)
      ·
        refine ⟨7458310527999435060667393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9944414037332580080889857 7458310527999435060667393)
        ·
          refine ⟨5593732895999576295500545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7458310527999435060667393 5593732895999576295500545)
          ·
            refine ⟨4195299671999682221625409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593732895999576295500545 4195299671999682221625409)
            ·
              refine ⟨3146474753999761666219057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195299671999682221625409 3146474753999761666219057)
              ·
                refine ⟨2359856065499821249664293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146474753999761666219057 2359856065499821249664293)
                ·
                  refine ⟨442473012281216484312055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359856065499821249664293 442473012281216484312055)
                  ·
                    rfl

theorem cell22_3877709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3877709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877709 prefixEnd_3877709 := by exact prefixLift 3877709
  have htrace : WordTrace (prefixWord ++ tailWord_3877709) baseStart_3877709 baseEnd_3877709 := by
    simpa [prefixWord, tailWord_3877709, baseEnd_3877709] using wordTrace_append hprefix tailTrace_3877709
  have hstable : (prefixWord ++ tailWord_3877709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877709).length < 2 ^ (prefixWord ++ tailWord_3877709).sum := by decide
  have hdescent : baseEnd_3877709 < baseStart_3877709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877793 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 6]
def baseStart_3877793 : Nat := 118140960795 + 3877793 * 2 ^ 59
def prefixEnd_3877793 : Nat := 4983230072969 + 3 ^ 40 * 3877793 * 2
def baseEnd_3877793 : Nat := 442482597253433744611969

theorem tailTrace_3877793 : CollatzResearch.WordTrace tailWord_3877793 prefixEnd_3877793 442482597253433744611969 := by
  unfold tailWord_3877793
  simp only [CollatzResearch.WordTrace]
  refine ⟨141434730040425710163158033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94289820026950473442105355 141434730040425710163158033)
  ·
    refine ⟨106076047530319282622368525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141434730040425710163158033 106076047530319282622368525)
    ·
      refine ⟨39778517823869730983388197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106076047530319282622368525 39778517823869730983388197)
      ·
        refine ⟨7458472091975574559385287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39778517823869730983388197 7458472091975574559385287)
        ·
          refine ⟨11187708137963361839077931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458472091975574559385287 11187708137963361839077931)
          ·
            refine ⟨16781562206945042758616897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11187708137963361839077931 16781562206945042758616897)
            ·
              refine ⟨12586171655208782068962673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16781562206945042758616897 12586171655208782068962673)
              ·
                refine ⟨9439628741406586551722005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12586171655208782068962673 9439628741406586551722005)
                ·
                  refine ⟨442482597253433744611969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9439628741406586551722005 442482597253433744611969)
                  ·
                    rfl

theorem cell22_3877793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_3877793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877793 prefixEnd_3877793 := by exact prefixLift 3877793
  have htrace : WordTrace (prefixWord ++ tailWord_3877793) baseStart_3877793 baseEnd_3877793 := by
    simpa [prefixWord, tailWord_3877793, baseEnd_3877793] using wordTrace_append hprefix tailTrace_3877793
  have hstable : (prefixWord ++ tailWord_3877793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877793).length < 2 ^ (prefixWord ++ tailWord_3877793).sum := by decide
  have hdescent : baseEnd_3877793 < baseStart_3877793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877812 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3877812 : Nat := 118140960795 + 3877812 * 2 ^ 59
def prefixEnd_3877812 : Nat := 4983230072969 + 3 ^ 40 * 3877812 * 2
def baseEnd_3877812 : Nat := 1327454295848591517610849

theorem tailTrace_3877812 : CollatzResearch.WordTrace tailWord_3877812 prefixEnd_3877812 1327454295848591517610849 := by
  unfold tailWord_3877812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70717711513678438204049845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94290282018237917605399793 70717711513678438204049845)
  ·
    refine ⟨6629785454407353581629673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70717711513678438204049845 6629785454407353581629673)
    ·
      refine ⟨4972339090805515186222255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6629785454407353581629673 4972339090805515186222255)
      ·
        refine ⟨7458508636208272779333383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972339090805515186222255 7458508636208272779333383)
        ·
          refine ⟨11187762954312409169000075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458508636208272779333383 11187762954312409169000075)
          ·
            refine ⟨16781644431468613753500113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11187762954312409169000075 16781644431468613753500113)
            ·
              refine ⟨12586233323601460315125085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16781644431468613753500113 12586233323601460315125085)
              ·
                refine ⟨4719837496350547618171907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12586233323601460315125085 4719837496350547618171907)
                ·
                  refine ⟨7079756244525821427257861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719837496350547618171907 7079756244525821427257861)
                  ·
                    refine ⟨1327454295848591517610849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079756244525821427257861 1327454295848591517610849)
                    ·
                      rfl

theorem cell22_3877812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3877812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877812 prefixEnd_3877812 := by exact prefixLift 3877812
  have htrace : WordTrace (prefixWord ++ tailWord_3877812) baseStart_3877812 baseEnd_3877812 := by
    simpa [prefixWord, tailWord_3877812, baseEnd_3877812] using wordTrace_append hprefix tailTrace_3877812
  have hstable : (prefixWord ++ tailWord_3877812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877812).length < 2 ^ (prefixWord ++ tailWord_3877812).sum := by decide
  have hdescent : baseEnd_3877812 < baseStart_3877812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877838 : List Nat := [4, 1, 1, 1, 2, 4, 2, 7]
def baseStart_3877838 : Nat := 118140960795 + 3877838 * 2 ^ 59
def prefixEnd_3877838 : Nat := 4983230072969 + 3 ^ 40 * 3877838 * 2
def baseEnd_3877838 : Nat := 147495910686659568495641

theorem tailTrace_3877838 : CollatzResearch.WordTrace tailWord_3877838 prefixEnd_3877838 147495910686659568495641 := by
  unfold tailWord_3877838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17679546415657835356068271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94290914216841788565697445 17679546415657835356068271)
  ·
    refine ⟨26519319623486753034102407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17679546415657835356068271 26519319623486753034102407)
    ·
      refine ⟨39778979435230129551153611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26519319623486753034102407 39778979435230129551153611)
      ·
        refine ⟨59668469152845194326730417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39778979435230129551153611 59668469152845194326730417)
        ·
          refine ⟨44751351864633895745047813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59668469152845194326730417 44751351864633895745047813)
          ·
            refine ⟨8390878474618855452196465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44751351864633895745047813 8390878474618855452196465)
            ·
              refine ⟨6293158855964141589147349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8390878474618855452196465 6293158855964141589147349)
              ·
                refine ⟨147495910686659568495641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6293158855964141589147349 147495910686659568495641)
                ·
                  rfl

theorem cell22_3877838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_3877838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877838 prefixEnd_3877838 := by exact prefixLift 3877838
  have htrace : WordTrace (prefixWord ++ tailWord_3877838) baseStart_3877838 baseEnd_3877838 := by
    simpa [prefixWord, tailWord_3877838, baseEnd_3877838] using wordTrace_append hprefix tailTrace_3877838
  have hstable : (prefixWord ++ tailWord_3877838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877838).length < 2 ^ (prefixWord ++ tailWord_3877838).sum := by decide
  have hdescent : baseEnd_3877838 < baseStart_3877838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877842 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_3877842 : Nat := 118140960795 + 3877842 * 2 ^ 59
def prefixEnd_3877842 : Nat := 4983230072969 + 3 ^ 40 * 3877842 * 2
def baseEnd_3877842 : Nat := 1327464565461681439360757

theorem tailTrace_3877842 : CollatzResearch.WordTrace tailWord_3877842 prefixEnd_3877842 1327464565461681439360757 := by
  unfold tailWord_3877842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35359129304312047882922945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94291011478165461021127853 35359129304312047882922945)
  ·
    refine ⟨26519346978234035912192209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35359129304312047882922945 26519346978234035912192209)
    ·
      refine ⟨19889510233675526934144157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26519346978234035912192209 19889510233675526934144157)
      ·
        refine ⟨7458566337628322600304059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19889510233675526934144157 7458566337628322600304059)
        ·
          refine ⟨11187849506442483900456089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458566337628322600304059 11187849506442483900456089)
          ·
            refine ⟨8390887129831862925342067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11187849506442483900456089 8390887129831862925342067)
            ·
              refine ⟨12586330694747794388013101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8390887129831862925342067 12586330694747794388013101)
              ·
                refine ⟨4719874010530422895504913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12586330694747794388013101 4719874010530422895504913)
                ·
                  refine ⟨3539905507897817171628685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4719874010530422895504913 3539905507897817171628685)
                  ·
                    refine ⟨1327464565461681439360757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539905507897817171628685 1327464565461681439360757)
                    ·
                      rfl

theorem cell22_3877842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_3877842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877842 prefixEnd_3877842 := by exact prefixLift 3877842
  have htrace : WordTrace (prefixWord ++ tailWord_3877842) baseStart_3877842 baseEnd_3877842 := by
    simpa [prefixWord, tailWord_3877842, baseEnd_3877842] using wordTrace_append hprefix tailTrace_3877842
  have hstable : (prefixWord ++ tailWord_3877842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877842).length < 2 ^ (prefixWord ++ tailWord_3877842).sum := by decide
  have hdescent : baseEnd_3877842 < baseStart_3877842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877898 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3877898 : Nat := 118140960795 + 3877898 * 2 ^ 59
def prefixEnd_3877898 : Nat := 4983230072969 + 3 ^ 40 * 3877898 * 2
def baseEnd_3877898 : Nat := 1327483735406115959960585

theorem tailTrace_3877898 : CollatzResearch.WordTrace tailWord_3877898 prefixEnd_3877898 1327483735406115959960585 := by
  unfold tailWord_3877898
  simp only [CollatzResearch.WordTrace]
  refine ⟨35359639926261328273932587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94292373136696875397153565 35359639926261328273932587)
  ·
    refine ⟨53039459889391992410898881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35359639926261328273932587 53039459889391992410898881)
    ·
      refine ⟨39779594917043994308174161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53039459889391992410898881 39779594917043994308174161)
      ·
        refine ⟨29834696187782995731130621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39779594917043994308174161 29834696187782995731130621)
        ·
          refine ⟨11188011070418623399173983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29834696187782995731130621 11188011070418623399173983)
          ·
            refine ⟨16782016605627935098760975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11188011070418623399173983 16782016605627935098760975)
            ·
              refine ⟨25173024908441902648141463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16782016605627935098760975 25173024908441902648141463)
              ·
                refine ⟨37759537362662853972212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25173024908441902648141463 37759537362662853972212195)
                ·
                  refine ⟨56639306043994280958318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37759537362662853972212195 56639306043994280958318293)
                  ·
                    refine ⟨1327483735406115959960585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56639306043994280958318293 1327483735406115959960585)
                    ·
                      rfl

theorem cell22_3877898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3877898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877898 prefixEnd_3877898 := by exact prefixLift 3877898
  have htrace : WordTrace (prefixWord ++ tailWord_3877898) baseStart_3877898 baseEnd_3877898 := by
    simpa [prefixWord, tailWord_3877898, baseEnd_3877898] using wordTrace_append hprefix tailTrace_3877898
  have hstable : (prefixWord ++ tailWord_3877898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877898).length < 2 ^ (prefixWord ++ tailWord_3877898).sum := by decide
  have hdescent : baseEnd_3877898 < baseStart_3877898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877913 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_3877913 : Nat := 118140960795 + 3877913 * 2 ^ 59
def prefixEnd_3877913 : Nat := 4983230072969 + 3 ^ 40 * 3877913 * 2
def baseEnd_3877913 : Nat := 1327488870212660920835539

theorem tailTrace_3877913 : CollatzResearch.WordTrace tailWord_3877913 prefixEnd_3877913 1327488870212660920835539 := by
  unfold tailWord_3877913
  simp only [CollatzResearch.WordTrace]
  refine ⟨141439106799990970657526393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94292737866660647105017595 141439106799990970657526393)
  ·
    refine ⟨106079330099993227993144795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141439106799990970657526393 106079330099993227993144795)
    ·
      refine ⟨159118995149989841989717193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106079330099993227993144795 159118995149989841989717193)
      ·
        refine ⟨119339246362492381492287895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159118995149989841989717193 119339246362492381492287895)
        ·
          refine ⟨179008869543738572238431843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119339246362492381492287895 179008869543738572238431843)
          ·
            refine ⟨268513304315607858357647765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179008869543738572238431843 268513304315607858357647765)
            ·
              refine ⟨12586561139794118360514739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268513304315607858357647765 12586561139794118360514739)
              ·
                refine ⟨18879841709691177540772109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12586561139794118360514739 18879841709691177540772109)
                ·
                  refine ⟨7079940641134191577789541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18879841709691177540772109 7079940641134191577789541)
                  ·
                    refine ⟨1327488870212660920835539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079940641134191577789541 1327488870212660920835539)
                    ·
                      rfl

theorem cell22_3877913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_3877913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877913 prefixEnd_3877913 := by exact prefixLift 3877913
  have htrace : WordTrace (prefixWord ++ tailWord_3877913) baseStart_3877913 baseEnd_3877913 := by
    simpa [prefixWord, tailWord_3877913, baseEnd_3877913] using wordTrace_append hprefix tailTrace_3877913
  have hstable : (prefixWord ++ tailWord_3877913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877913).length < 2 ^ (prefixWord ++ tailWord_3877913).sum := by decide
  have hdescent : baseEnd_3877913 < baseStart_3877913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877945 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 6]
def baseStart_3877945 : Nat := 118140960795 + 3877945 * 2 ^ 59
def prefixEnd_3877945 : Nat := 4983230072969 + 3 ^ 40 * 3877945 * 2
def baseEnd_3877945 : Nat := 442499941488874501345147

theorem tailTrace_3877945 : CollatzResearch.WordTrace tailWord_3877945 prefixEnd_3877945 442499941488874501345147 := by
  unfold tailWord_3877945
  simp only [CollatzResearch.WordTrace]
  refine ⟨141440273935875040122691289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94293515957250026748460859 141440273935875040122691289)
  ·
    refine ⟨106080205451906280092018467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141440273935875040122691289 106080205451906280092018467)
    ·
      refine ⟨159120308177859420138027701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106080205451906280092018467 159120308177859420138027701)
      ·
        refine ⟨14917528891674320637940097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159120308177859420138027701 14917528891674320637940097)
        ·
          refine ⟨11188146668755740478455073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14917528891674320637940097 11188146668755740478455073)
          ·
            refine ⟨8391110001566805358841305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188146668755740478455073 8391110001566805358841305)
            ·
              refine ⟨6293332501175104019130979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391110001566805358841305 6293332501175104019130979)
              ·
                refine ⟨9439998751762656028696469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293332501175104019130979 9439998751762656028696469)
                ·
                  refine ⟨442499941488874501345147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9439998751762656028696469 442499941488874501345147)
                  ·
                    rfl

theorem cell22_3877945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_3877945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877945 prefixEnd_3877945 := by exact prefixLift 3877945
  have htrace : WordTrace (prefixWord ++ tailWord_3877945) baseStart_3877945 baseEnd_3877945 := by
    simpa [prefixWord, tailWord_3877945, baseEnd_3877945] using wordTrace_append hprefix tailTrace_3877945
  have hstable : (prefixWord ++ tailWord_3877945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877945).length < 2 ^ (prefixWord ++ tailWord_3877945).sum := by decide
  have hdescent : baseEnd_3877945 < baseStart_3877945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877973 : List Nat := [1, 3, 2, 2, 1, 2, 3, 8]
def baseStart_3877973 : Nat := 118140960795 + 3877973 * 2 ^ 59
def prefixEnd_3877973 : Nat := 4983230072969 + 3 ^ 40 * 3877973 * 2
def baseEnd_3877973 : Nat := 147501045493204529370595

theorem tailTrace_3877973 : CollatzResearch.WordTrace tailWord_3877973 prefixEnd_3877973 147501045493204529370595 := by
  unfold tailWord_3877973
  simp only [CollatzResearch.WordTrace]
  refine ⟨141441295179773600904710573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94294196786515733936473715 141441295179773600904710573)
  ·
    refine ⟨53040485692415100339266465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141441295179773600904710573 53040485692415100339266465)
    ·
      refine ⟨39780364269311325254449849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53040485692415100339266465 39780364269311325254449849)
      ·
        refine ⟨29835273201983493940837387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39780364269311325254449849 29835273201983493940837387)
        ·
          refine ⟨44752909802975240911256081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29835273201983493940837387 44752909802975240911256081)
          ·
            refine ⟨33564682352231430683442061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44752909802975240911256081 33564682352231430683442061)
            ·
              refine ⟨12586755882086786506290773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33564682352231430683442061 12586755882086786506290773)
              ·
                refine ⟨147501045493204529370595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12586755882086786506290773 147501045493204529370595)
                ·
                  rfl

theorem cell22_3877973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 8].length) (baseStart_3877973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877973 prefixEnd_3877973 := by exact prefixLift 3877973
  have htrace : WordTrace (prefixWord ++ tailWord_3877973) baseStart_3877973 baseEnd_3877973 := by
    simpa [prefixWord, tailWord_3877973, baseEnd_3877973] using wordTrace_append hprefix tailTrace_3877973
  have hstable : (prefixWord ++ tailWord_3877973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877973).length < 2 ^ (prefixWord ++ tailWord_3877973).sum := by decide
  have hdescent : baseEnd_3877973 < baseStart_3877973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878052 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_3878052 : Nat := 118140960795 + 3878052 * 2 ^ 59
def prefixEnd_3878052 : Nat := 4983230072969 + 3 ^ 40 * 3878052 * 2
def baseEnd_3878052 : Nat := 442512150917770297203371

theorem tailTrace_3878052 : CollatzResearch.WordTrace tailWord_3878052 prefixEnd_3878052 442512150917770297203371 := by
  unfold tailWord_3878052
  simp only [CollatzResearch.WordTrace]
  refine ⟨70722088273243698698418205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94296117697658264931224273 70722088273243698698418205)
  ·
    refine ⟨26520783102466387011906827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70722088273243698698418205 26520783102466387011906827)
    ·
      refine ⟨39781174653699580517860241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26520783102466387011906827 39781174653699580517860241)
      ·
        refine ⟨29835880990274685388395181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39781174653699580517860241 29835880990274685388395181)
        ·
          refine ⟨11188455371353007020648193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29835880990274685388395181 11188455371353007020648193)
          ·
            refine ⟨8391341528514755265486145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188455371353007020648193 8391341528514755265486145)
            ·
              refine ⟨6293506146386066449114609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391341528514755265486145 6293506146386066449114609)
              ·
                refine ⟨4720129609789549836835957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6293506146386066449114609 4720129609789549836835957)
                ·
                  refine ⟨442512150917770297203371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4720129609789549836835957 442512150917770297203371)
                  ·
                    rfl

theorem cell22_3878052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_3878052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878052 prefixEnd_3878052 := by exact prefixLift 3878052
  have htrace : WordTrace (prefixWord ++ tailWord_3878052) baseStart_3878052 baseEnd_3878052 := by
    simpa [prefixWord, tailWord_3878052, baseEnd_3878052] using wordTrace_append hprefix tailTrace_3878052
  have hstable : (prefixWord ++ tailWord_3878052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878052).length < 2 ^ (prefixWord ++ tailWord_3878052).sum := by decide
  have hdescent : baseEnd_3878052 < baseStart_3878052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878112 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_3878112 : Nat := 118140960795 + 3878112 * 2 ^ 59
def prefixEnd_3878112 : Nat := 4983230072969 + 3 ^ 40 * 3878112 * 2
def baseEnd_3878112 : Nat := 1327556991979490735109929

theorem tailTrace_3878112 : CollatzResearch.WordTrace tailWord_3878112 prefixEnd_3878112 1327556991979490735109929 := by
  unfold tailWord_3878112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70723182463135013822010295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94297576617513351762680393 70723182463135013822010295)
  ·
    refine ⟨106084773694702520733015443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70723182463135013822010295 106084773694702520733015443)
    ·
      refine ⟨159127160542053781099523165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106084773694702520733015443 159127160542053781099523165)
      ·
        refine ⟨59672685203270167912321187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159127160542053781099523165 59672685203270167912321187)
        ·
          refine ⟨89509027804905251868481781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59672685203270167912321187 89509027804905251868481781)
          ·
            refine ⟨8391471356709867362670167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89509027804905251868481781 8391471356709867362670167)
            ·
              refine ⟨12587207035064801044005251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391471356709867362670167 12587207035064801044005251)
              ·
                refine ⟨18880810552597201566007877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12587207035064801044005251 18880810552597201566007877)
                ·
                  refine ⟨3540151978611975293626477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18880810552597201566007877 3540151978611975293626477)
                  ·
                    refine ⟨1327556991979490735109929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3540151978611975293626477 1327556991979490735109929)
                    ·
                      rfl

theorem cell22_3878112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_3878112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878112 prefixEnd_3878112 := by exact prefixLift 3878112
  have htrace : WordTrace (prefixWord ++ tailWord_3878112) baseStart_3878112 baseEnd_3878112 := by
    simpa [prefixWord, tailWord_3878112, baseEnd_3878112] using wordTrace_append hprefix tailTrace_3878112
  have hstable : (prefixWord ++ tailWord_3878112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878112).length < 2 ^ (prefixWord ++ tailWord_3878112).sum := by decide
  have hdescent : baseEnd_3878112 < baseStart_3878112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878142 : List Nat := [4, 2, 2, 1, 1, 3, 1, 8]
def baseStart_3878142 : Nat := 118140960795 + 3878142 * 2 ^ 59
def prefixEnd_3878142 : Nat := 4983230072969 + 3 ^ 40 * 3878142 * 2
def baseEnd_3878142 : Nat := 147507473510286739651093

theorem tailTrace_3878142 : CollatzResearch.WordTrace tailWord_3878142 prefixEnd_3878142 147507473510286739651093 := by
  unfold tailWord_3878142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680932389520167845951585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94298306077440895178408453 17680932389520167845951585)
  ·
    refine ⟨13260699292140125884463689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17680932389520167845951585 13260699292140125884463689)
    ·
      refine ⟨9945524469105094413347767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13260699292140125884463689 9945524469105094413347767)
      ·
        refine ⟨14918286703657641620021651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9945524469105094413347767 14918286703657641620021651)
        ·
          refine ⟨22377430055486462430032477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14918286703657641620021651 22377430055486462430032477)
          ·
            refine ⟨8391536270807423411262179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22377430055486462430032477 8391536270807423411262179)
            ·
              refine ⟨12587304406211135116893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391536270807423411262179 12587304406211135116893269)
              ·
                refine ⟨147507473510286739651093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12587304406211135116893269 147507473510286739651093)
                ·
                  rfl

theorem cell22_3878142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_3878142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878142 prefixEnd_3878142 := by exact prefixLift 3878142
  have htrace : WordTrace (prefixWord ++ tailWord_3878142) baseStart_3878142 baseEnd_3878142 := by
    simpa [prefixWord, tailWord_3878142, baseEnd_3878142] using wordTrace_append hprefix tailTrace_3878142
  have hstable : (prefixWord ++ tailWord_3878142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878142).length < 2 ^ (prefixWord ++ tailWord_3878142).sum := by decide
  have hdescent : baseEnd_3878142 < baseStart_3878142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878217 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_3878217 : Nat := 118140960795 + 3878217 * 2 ^ 59
def prefixEnd_3878217 : Nat := 4983230072969 + 3 ^ 40 * 3878217 * 2
def baseEnd_3878217 : Nat := 1327592935625305461234607

theorem tailTrace_3878217 : CollatzResearch.WordTrace tailWord_3878217 prefixEnd_3878217 1327592935625305461234607 := by
  unfold tailWord_3878217
  simp only [CollatzResearch.WordTrace]
  refine ⟨141450194590889630576592905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94300129727259753717728603 141450194590889630576592905)
  ·
    refine ⟨106087645943167222932444679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141450194590889630576592905 106087645943167222932444679)
    ·
      refine ⟨159131468914750834398667019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106087645943167222932444679 159131468914750834398667019)
      ·
        refine ⟨238697203372126251598000529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159131468914750834398667019 238697203372126251598000529)
        ·
          refine ⟨179022902529094688698500397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238697203372126251598000529 179022902529094688698500397)
          ·
            refine ⟨67133588448410508261937649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179022902529094688698500397 67133588448410508261937649)
            ·
              refine ⟨50350191336307881196453237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67133588448410508261937649 50350191336307881196453237)
              ·
                refine ⟨4720330437778863862167491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50350191336307881196453237 4720330437778863862167491)
                ·
                  refine ⟨7080495656668295793251237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720330437778863862167491 7080495656668295793251237)
                  ·
                    refine ⟨1327592935625305461234607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7080495656668295793251237 1327592935625305461234607)
                    ·
                      rfl

theorem cell22_3878217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_3878217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878217 prefixEnd_3878217 := by exact prefixLift 3878217
  have htrace : WordTrace (prefixWord ++ tailWord_3878217) baseStart_3878217 baseEnd_3878217 := by
    simpa [prefixWord, tailWord_3878217, baseEnd_3878217] using wordTrace_append hprefix tailTrace_3878217
  have hstable : (prefixWord ++ tailWord_3878217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878217).length < 2 ^ (prefixWord ++ tailWord_3878217).sum := by decide
  have hdescent : baseEnd_3878217 < baseStart_3878217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878343 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 1, 3]
def baseStart_3878343 : Nat := 118140960795 + 3878343 * 2 ^ 59
def prefixEnd_3878343 : Nat := 4983230072969 + 3 ^ 40 * 3878343 * 2
def baseEnd_3878343 : Nat := 1327636068000283132584221

theorem tailTrace_3878343 : CollatzResearch.WordTrace tailWord_3878343 prefixEnd_3878343 1327636068000283132584221 := by
  unfold tailWord_3878343
  simp only [CollatzResearch.WordTrace]
  refine ⟨141454790188433154095679683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94303193458955436063786455 141454790188433154095679683)
  ·
    refine ⟨212182185282649731143519525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141454790188433154095679683 212182185282649731143519525)
    ·
      refine ⟨39784159740496824589409911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212182185282649731143519525 39784159740496824589409911)
      ·
        refine ⟨59676239610745236884114867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39784159740496824589409911 59676239610745236884114867)
        ·
          refine ⟨89514359416117855326172301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59676239610745236884114867 89514359416117855326172301)
          ·
            refine ⟨33567884781044195747314613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89514359416117855326172301 33567884781044195747314613)
            ·
              refine ⟨3146989198222893351310745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33567884781044195747314613 3146989198222893351310745)
              ·
                refine ⟨2360241898667170013483059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146989198222893351310745 2360241898667170013483059)
                ·
                  refine ⟨3540362848000755020224589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360241898667170013483059 3540362848000755020224589)
                  ·
                    refine ⟨1327636068000283132584221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3540362848000755020224589 1327636068000283132584221)
                    ·
                      rfl

theorem cell22_3878343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_3878343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878343 prefixEnd_3878343 := by exact prefixLift 3878343
  have htrace : WordTrace (prefixWord ++ tailWord_3878343) baseStart_3878343 baseEnd_3878343 := by
    simpa [prefixWord, tailWord_3878343, baseEnd_3878343] using wordTrace_append hprefix tailTrace_3878343
  have hstable : (prefixWord ++ tailWord_3878343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878343).length < 2 ^ (prefixWord ++ tailWord_3878343).sum := by decide
  have hdescent : baseEnd_3878343 < baseStart_3878343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878352 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_3878352 : Nat := 118140960795 + 3878352 * 2 ^ 59
def prefixEnd_3878352 : Nat := 4983230072969 + 3 ^ 40 * 3878352 * 2
def baseEnd_3878352 : Nat := 1327639148884210109109193

theorem tailTrace_3878352 : CollatzResearch.WordTrace tailWord_3878352 prefixEnd_3878352 1327639148884210109109193 := by
  unfold tailWord_3878352
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727559222700274316378655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94303412296933699088504873 70727559222700274316378655)
  ·
    refine ⟨106091338834050411474567983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70727559222700274316378655 106091338834050411474567983)
    ·
      refine ⟨159137008251075617211851975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106091338834050411474567983 159137008251075617211851975)
      ·
        refine ⟨238705512376613425817777963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159137008251075617211851975 238705512376613425817777963)
        ·
          refine ⟨358058268564920138726666945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238705512376613425817777963 358058268564920138726666945)
          ·
            refine ⟨268543701423690104045000209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358058268564920138726666945 268543701423690104045000209)
            ·
              refine ⟨201407776067767578033750157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268543701423690104045000209 201407776067767578033750157)
              ·
                refine ⟨75527916025412841762656309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201407776067767578033750157 75527916025412841762656309)
                ·
                  refine ⟨7080742127382453915249029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75527916025412841762656309 7080742127382453915249029)
                  ·
                    refine ⟨1327639148884210109109193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7080742127382453915249029 1327639148884210109109193)
                    ·
                      rfl

theorem cell22_3878352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_3878352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878352 prefixEnd_3878352 := by exact prefixLift 3878352
  have htrace : WordTrace (prefixWord ++ tailWord_3878352) baseStart_3878352 baseEnd_3878352 := by
    simpa [prefixWord, tailWord_3878352, baseEnd_3878352] using wordTrace_append hprefix tailTrace_3878352
  have hstable : (prefixWord ++ tailWord_3878352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878352).length < 2 ^ (prefixWord ++ tailWord_3878352).sum := by decide
  have hdescent : baseEnd_3878352 < baseStart_3878352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878356 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3878356 : Nat := 118140960795 + 3878356 * 2 ^ 59
def prefixEnd_3878356 : Nat := 4983230072969 + 3 ^ 40 * 3878356 * 2
def baseEnd_3878356 : Nat := 442546839388651810669727

theorem tailTrace_3878356 : CollatzResearch.WordTrace tailWord_3878356 prefixEnd_3878356 442546839388651810669727 := by
  unfold tailWord_3878356
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727632168693028657951461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94303509558257371543935281 70727632168693028657951461)
  ·
    refine ⟨13261431031629942873365899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70727632168693028657951461 13261431031629942873365899)
    ·
      refine ⟨19892146547444914310048849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13261431031629942873365899 19892146547444914310048849)
      ·
        refine ⟨14919109910583685732536637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19892146547444914310048849 14919109910583685732536637)
        ·
          refine ⟨5594666216468882149701239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14919109910583685732536637 5594666216468882149701239)
          ·
            refine ⟨8391999324703323224551859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594666216468882149701239 8391999324703323224551859)
            ·
              refine ⟨12587998987054984836827789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391999324703323224551859 12587998987054984836827789)
              ·
                refine ⟨4720499620145619313810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12587998987054984836827789 4720499620145619313810421)
                ·
                  refine ⟨442546839388651810669727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4720499620145619313810421 442546839388651810669727)
                  ·
                    rfl

theorem cell22_3878356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3878356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878356 prefixEnd_3878356 := by exact prefixLift 3878356
  have htrace : WordTrace (prefixWord ++ tailWord_3878356) baseStart_3878356 baseEnd_3878356 := by
    simpa [prefixWord, tailWord_3878356, baseEnd_3878356] using wordTrace_append hprefix tailTrace_3878356
  have hstable : (prefixWord ++ tailWord_3878356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878356).length < 2 ^ (prefixWord ++ tailWord_3878356).sum := by decide
  have hdescent : baseEnd_3878356 < baseStart_3878356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878367 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 8]
def baseStart_3878367 : Nat := 118140960795 + 3878367 * 2 ^ 59
def prefixEnd_3878367 : Nat := 4983230072969 + 3 ^ 40 * 3878367 * 2
def baseEnd_3878367 : Nat := 442548094563585023328049

theorem tailTrace_3878367 : CollatzResearch.WordTrace tailWord_3878367 prefixEnd_3878367 442548094563585023328049 := by
  unfold tailWord_3878367
  simp only [CollatzResearch.WordTrace]
  refine ⟨141455665540346206194553355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94303777026897470796368903 141455665540346206194553355)
  ·
    refine ⟨212183498310519309291830033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141455665540346206194553355 212183498310519309291830033)
    ·
      refine ⟨159137623732889481968872525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212183498310519309291830033 159137623732889481968872525)
      ·
        refine ⟨59676608899833555738327197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159137623732889481968872525 59676608899833555738327197)
        ·
          refine ⟨22378728337437583401872699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59676608899833555738327197 22378728337437583401872699)
          ·
            refine ⟨33568092506156375102809049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22378728337437583401872699 33568092506156375102809049)
            ·
              refine ⟨25176069379617281327106787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33568092506156375102809049 25176069379617281327106787)
              ·
                refine ⟨37764104069425921990660181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25176069379617281327106787 37764104069425921990660181)
                ·
                  refine ⟨442548094563585023328049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37764104069425921990660181 442548094563585023328049)
                  ·
                    rfl

theorem cell22_3878367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_3878367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878367 prefixEnd_3878367 := by exact prefixLift 3878367
  have htrace : WordTrace (prefixWord ++ tailWord_3878367) baseStart_3878367 baseEnd_3878367 := by
    simpa [prefixWord, tailWord_3878367, baseEnd_3878367] using wordTrace_append hprefix tailTrace_3878367
  have hstable : (prefixWord ++ tailWord_3878367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878367).length < 2 ^ (prefixWord ++ tailWord_3878367).sum := by decide
  have hdescent : baseEnd_3878367 < baseStart_3878367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878369 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_3878369 : Nat := 118140960795 + 3878369 * 2 ^ 59
def prefixEnd_3878369 : Nat := 4983230072969 + 3 ^ 40 * 3878369 * 2
def baseEnd_3878369 : Nat := 1327644968331627731434141

theorem tailTrace_3878369 : CollatzResearch.WordTrace tailWord_3878369 prefixEnd_3878369 1327644968331627731434141 := by
  unfold tailWord_3878369
  simp only [CollatzResearch.WordTrace]
  refine ⟨141455738486338960536126161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94303825657559307024084107 141455738486338960536126161)
  ·
    refine ⟨106091803864754220402094621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141455738486338960536126161 106091803864754220402094621)
    ·
      refine ⟨39784426449282832650785483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106091803864754220402094621 39784426449282832650785483)
      ·
        refine ⟨59676639673924248976178225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39784426449282832650785483 59676639673924248976178225)
        ·
          refine ⟨44757479755443186732133669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59676639673924248976178225 44757479755443186732133669)
          ·
            refine ⟨8392027454145597512275063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44757479755443186732133669 8392027454145597512275063)
            ·
              refine ⟨12588041181218396268412595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392027454145597512275063 12588041181218396268412595)
              ·
                refine ⟨18882061771827594402618893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12588041181218396268412595 18882061771827594402618893)
                ·
                  refine ⟨7080773164435347900982085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18882061771827594402618893 7080773164435347900982085)
                  ·
                    refine ⟨1327644968331627731434141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7080773164435347900982085 1327644968331627731434141)
                    ·
                      rfl

theorem cell22_3878369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_3878369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878369 prefixEnd_3878369 := by exact prefixLift 3878369
  have htrace : WordTrace (prefixWord ++ tailWord_3878369) baseStart_3878369 baseEnd_3878369 := by
    simpa [prefixWord, tailWord_3878369, baseEnd_3878369] using wordTrace_append hprefix tailTrace_3878369
  have hstable : (prefixWord ++ tailWord_3878369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878369).length < 2 ^ (prefixWord ++ tailWord_3878369).sum := by decide
  have hdescent : baseEnd_3878369 < baseStart_3878369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878538 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3878538 : Nat := 118140960795 + 3878538 * 2 ^ 59
def prefixEnd_3878538 : Nat := 4983230072969 + 3 ^ 40 * 3878538 * 2
def baseEnd_3878538 : Nat := 1327702820485367623958623

theorem tailTrace_3878538 : CollatzResearch.WordTrace tailWord_3878538 prefixEnd_3878538 1327702820485367623958623 := by
  unfold tailWord_3878538
  simp only [CollatzResearch.WordTrace]
  refine ⟨35365475605681675599757067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94307934948484468266018845 35365475605681675599757067)
  ·
    refine ⟨53048213408522513399635601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35365475605681675599757067 53048213408522513399635601)
    ·
      refine ⟨39786160056391885049726701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53048213408522513399635601 39786160056391885049726701)
      ·
        refine ⟨14919810021146956893647513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39786160056391885049726701 14919810021146956893647513)
        ·
          refine ⟨11189857515860217670235635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14919810021146956893647513 11189857515860217670235635)
          ·
            refine ⟨16784786273790326505353453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11189857515860217670235635 16784786273790326505353453)
            ·
              refine ⟨6294294852671372439507545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16784786273790326505353453 6294294852671372439507545)
              ·
                refine ⟨4720721139503529329630659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6294294852671372439507545 4720721139503529329630659)
                ·
                  refine ⟨7081081709255293994445989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720721139503529329630659 7081081709255293994445989)
                  ·
                    refine ⟨1327702820485367623958623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081081709255293994445989 1327702820485367623958623)
                    ·
                      rfl

theorem cell22_3878538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3878538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878538 prefixEnd_3878538 := by exact prefixLift 3878538
  have htrace : WordTrace (prefixWord ++ tailWord_3878538) baseStart_3878538 baseEnd_3878538 := by
    simpa [prefixWord, tailWord_3878538, baseEnd_3878538] using wordTrace_append hprefix tailTrace_3878538
  have hstable : (prefixWord ++ tailWord_3878538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878538).length < 2 ^ (prefixWord ++ tailWord_3878538).sum := by decide
  have hdescent : baseEnd_3878538 < baseStart_3878538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878549 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3878549 : Nat := 118140960795 + 3878549 * 2 ^ 59
def prefixEnd_3878549 : Nat := 4983230072969 + 3 ^ 40 * 3878549 * 2
def baseEnd_3878549 : Nat := 1327706586010167261933589

theorem tailTrace_3878549 : CollatzResearch.WordTrace tailWord_3878549 prefixEnd_3878549 1327706586010167261933589 := by
  unfold tailWord_3878549
  simp only [CollatzResearch.WordTrace]
  refine ⟨141462303625686851277678701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94308202417124567518452467 141462303625686851277678701)
  ·
    refine ⟨53048363859632569229129513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141462303625686851277678701 53048363859632569229129513)
    ·
      refine ⟨39786272894724426921847135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53048363859632569229129513 39786272894724426921847135)
      ·
        refine ⟨59679409342086640382770703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39786272894724426921847135 59679409342086640382770703)
        ·
          refine ⟨89519114013129960574156055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59679409342086640382770703 89519114013129960574156055)
          ·
            refine ⟨134278671019694940861234083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89519114013129960574156055 134278671019694940861234083)
            ·
              refine ⟨201418006529542411291851125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134278671019694940861234083 201418006529542411291851125)
              ·
                refine ⟨18882938112144601058611043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201418006529542411291851125 18882938112144601058611043)
                ·
                  refine ⟨28324407168216901587916565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18882938112144601058611043 28324407168216901587916565)
                  ·
                    refine ⟨1327706586010167261933589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28324407168216901587916565 1327706586010167261933589)
                    ·
                      rfl

theorem cell22_3878549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3878549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878549 prefixEnd_3878549 := by exact prefixLift 3878549
  have htrace : WordTrace (prefixWord ++ tailWord_3878549) baseStart_3878549 baseEnd_3878549 := by
    simpa [prefixWord, tailWord_3878549, baseEnd_3878549] using wordTrace_append hprefix tailTrace_3878549
  have hstable : (prefixWord ++ tailWord_3878549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878549).length < 2 ^ (prefixWord ++ tailWord_3878549).sum := by decide
  have hdescent : baseEnd_3878549 < baseStart_3878549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878551 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 1, 5]
def baseStart_3878551 : Nat := 118140960795 + 3878551 * 2 ^ 59
def prefixEnd_3878551 : Nat := 4983230072969 + 3 ^ 40 * 3878551 * 2
def baseEnd_3878551 : Nat := 1327707270651039923383583

theorem tailTrace_3878551 : CollatzResearch.WordTrace tailWord_3878551 prefixEnd_3878551 1327707270651039923383583 := by
  unfold tailWord_3878551
  simp only [CollatzResearch.WordTrace]
  refine ⟨141462376571679605619251507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94308251047786403746167671 141462376571679605619251507)
  ·
    refine ⟨212193564857519408428877261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141462376571679605619251507 212193564857519408428877261)
    ·
      refine ⟨79572586821569778160828973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212193564857519408428877261 79572586821569778160828973)
      ·
        refine ⟨29839720058088666810310865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79572586821569778160828973 29839720058088666810310865)
        ·
          refine ⟨22379790043566500107733149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29839720058088666810310865 22379790043566500107733149)
          ·
            refine ⟨8392421266337437540399931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22379790043566500107733149 8392421266337437540399931)
            ·
              refine ⟨12588631899506156310599897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392421266337437540399931 12588631899506156310599897)
              ·
                refine ⟨9441473924629617232949923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588631899506156310599897 9441473924629617232949923)
                ·
                  refine ⟨14162210886944425849424885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441473924629617232949923 14162210886944425849424885)
                  ·
                    refine ⟨1327707270651039923383583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14162210886944425849424885 1327707270651039923383583)
                    ·
                      rfl

theorem cell22_3878551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_3878551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878551 prefixEnd_3878551 := by exact prefixLift 3878551
  have htrace : WordTrace (prefixWord ++ tailWord_3878551) baseStart_3878551 baseEnd_3878551 := by
    simpa [prefixWord, tailWord_3878551, baseEnd_3878551] using wordTrace_append hprefix tailTrace_3878551
  have hstable : (prefixWord ++ tailWord_3878551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878551).length < 2 ^ (prefixWord ++ tailWord_3878551).sum := by decide
  have hdescent : baseEnd_3878551 < baseStart_3878551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878564 : List Nat := [2, 3, 1, 2, 2, 12]
def baseStart_3878564 : Nat := 118140960795 + 3878564 * 2 ^ 59
def prefixEnd_3878564 : Nat := 4983230072969 + 3 ^ 40 * 3878564 * 2
def baseEnd_3878564 : Nat := 16391502726132249664303

theorem tailTrace_3878564 : CollatzResearch.WordTrace tailWord_3878564 prefixEnd_3878564 16391502726132249664303 := by
  unfold tailWord_3878564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70731425360316254419737373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94308567147088339226316497 70731425360316254419737373)
  ·
    refine ⟨26524284510118595407401515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70731425360316254419737373 26524284510118595407401515)
    ·
      refine ⟨39786426765177893111102273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26524284510118595407401515 39786426765177893111102273)
      ·
        refine ⟨29839820073883419833326705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39786426765177893111102273 29839820073883419833326705)
        ·
          refine ⟨22379865055412564874995029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29839820073883419833326705 22379865055412564874995029)
          ·
            refine ⟨16391502726132249664303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22379865055412564874995029 16391502726132249664303)
            ·
              rfl

theorem cell22_3878564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 12].length) (baseStart_3878564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878564 prefixEnd_3878564 := by exact prefixLift 3878564
  have htrace : WordTrace (prefixWord ++ tailWord_3878564) baseStart_3878564 baseEnd_3878564 := by
    simpa [prefixWord, tailWord_3878564, baseEnd_3878564] using wordTrace_append hprefix tailTrace_3878564
  have hstable : (prefixWord ++ tailWord_3878564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878564).length < 2 ^ (prefixWord ++ tailWord_3878564).sum := by decide
  have hdescent : baseEnd_3878564 < baseStart_3878564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878641 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_3878641 : Nat := 118140960795 + 3878641 * 2 ^ 59
def prefixEnd_3878641 : Nat := 4983230072969 + 3 ^ 40 * 3878641 * 2
def baseEnd_3878641 : Nat := 1327738079490309688633307

theorem tailTrace_3878641 : CollatzResearch.WordTrace tailWord_3878641 prefixEnd_3878641 1327738079490309688633307 := by
  unfold tailWord_3878641
  simp only [CollatzResearch.WordTrace]
  refine ⟨141465659141353550990027777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94310439427569033993351851 141465659141353550990027777)
  ·
    refine ⟨106099244356015163242520833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141465659141353550990027777 106099244356015163242520833)
    ·
      refine ⟨79574433267011372431890625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106099244356015163242520833 79574433267011372431890625)
      ·
        refine ⟨59680824950258529323917969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79574433267011372431890625 59680824950258529323917969)
        ·
          refine ⟨44760618712693896992938477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59680824950258529323917969 44760618712693896992938477)
          ·
            refine ⟨16785232017260211372351929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44760618712693896992938477 16785232017260211372351929)
            ·
              refine ⟨12588924012945158529263947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16785232017260211372351929 12588924012945158529263947)
              ·
                refine ⟨18883386019417737793895921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12588924012945158529263947 18883386019417737793895921)
                ·
                  refine ⟨14162539514563303345421941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18883386019417737793895921 14162539514563303345421941)
                  ·
                    refine ⟨1327738079490309688633307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14162539514563303345421941 1327738079490309688633307)
                    ·
                      rfl

theorem cell22_3878641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_3878641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878641 prefixEnd_3878641 := by exact prefixLift 3878641
  have htrace : WordTrace (prefixWord ++ tailWord_3878641) baseStart_3878641 baseEnd_3878641 := by
    simpa [prefixWord, tailWord_3878641, baseEnd_3878641] using wordTrace_append hprefix tailTrace_3878641
  have hstable : (prefixWord ++ tailWord_3878641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878641).length < 2 ^ (prefixWord ++ tailWord_3878641).sum := by decide
  have hdescent : baseEnd_3878641 < baseStart_3878641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878703 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 2, 3]
def baseStart_3878703 : Nat := 118140960795 + 3878703 * 2 ^ 59
def prefixEnd_3878703 : Nat := 4983230072969 + 3 ^ 40 * 3878703 * 2
def baseEnd_3878703 : Nat := 1327759303357362193583117

theorem tailTrace_3878703 : CollatzResearch.WordTrace tailWord_3878703 prefixEnd_3878703 1327759303357362193583117 := by
  unfold tailWord_3878703
  simp only [CollatzResearch.WordTrace]
  refine ⟨141467920467128935578784763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94311946978085957052523175 141467920467128935578784763)
  ·
    refine ⟨212201880700693403368177145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141467920467128935578784763 212201880700693403368177145)
    ·
      refine ⟨159151410525520052526132859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212201880700693403368177145 159151410525520052526132859)
      ·
        refine ⟨238727115788280078789199289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159151410525520052526132859 238727115788280078789199289)
        ·
          refine ⟨179045336841210059091899467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238727115788280078789199289 179045336841210059091899467)
          ·
            refine ⟨268568005261815088637849201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179045336841210059091899467 268568005261815088637849201)
            ·
              refine ⟨201426003946361316478386901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268568005261815088637849201 201426003946361316478386901)
              ·
                refine ⟨4720921967492843354962193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201426003946361316478386901 4720921967492843354962193)
                ·
                  refine ⟨3540691475619632516221645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4720921967492843354962193 3540691475619632516221645)
                  ·
                    refine ⟨1327759303357362193583117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3540691475619632516221645 1327759303357362193583117)
                    ·
                      rfl

theorem cell22_3878703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_3878703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878703 prefixEnd_3878703 := by exact prefixLift 3878703
  have htrace : WordTrace (prefixWord ++ tailWord_3878703) baseStart_3878703 baseEnd_3878703 := by
    simpa [prefixWord, tailWord_3878703, baseEnd_3878703] using wordTrace_append hprefix tailTrace_3878703
  have hstable : (prefixWord ++ tailWord_3878703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878703).length < 2 ^ (prefixWord ++ tailWord_3878703).sum := by decide
  have hdescent : baseEnd_3878703 < baseStart_3878703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878707 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 1, 4]
def baseStart_3878707 : Nat := 118140960795 + 3878707 * 2 ^ 59
def prefixEnd_3878707 : Nat := 4983230072969 + 3 ^ 40 * 3878707 * 2
def baseEnd_3878707 : Nat := 1327760672639107516483105

theorem tailTrace_3878707 : CollatzResearch.WordTrace tailWord_3878707 prefixEnd_3878707 1327760672639107516483105 := by
  unfold tailWord_3878707
  simp only [CollatzResearch.WordTrace]
  refine ⟨141468066359114444261930375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94312044239409629507953583 141468066359114444261930375)
  ·
    refine ⟨212202099538671666392895563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141468066359114444261930375 212202099538671666392895563)
    ·
      refine ⟨318303149308007499589343345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212202099538671666392895563 318303149308007499589343345)
      ·
        refine ⟨238727361981005624692007509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318303149308007499589343345 238727361981005624692007509)
        ·
          refine ⟨2797586273214909664359463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 238727361981005624692007509 2797586273214909664359463)
          ·
            refine ⟨4196379409822364496539195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797586273214909664359463 4196379409822364496539195)
            ·
              refine ⟨6294569114733546744808793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196379409822364496539195 6294569114733546744808793)
              ·
                refine ⟨4720926836050160058606595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6294569114733546744808793 4720926836050160058606595)
                ·
                  refine ⟨7081390254075240087909893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720926836050160058606595 7081390254075240087909893)
                  ·
                    refine ⟨1327760672639107516483105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081390254075240087909893 1327760672639107516483105)
                    ·
                      rfl

theorem cell22_3878707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 4].length) (baseStart_3878707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878707 prefixEnd_3878707 := by exact prefixLift 3878707
  have htrace : WordTrace (prefixWord ++ tailWord_3878707) baseStart_3878707 baseEnd_3878707 := by
    simpa [prefixWord, tailWord_3878707, baseEnd_3878707] using wordTrace_append hprefix tailTrace_3878707
  have hstable : (prefixWord ++ tailWord_3878707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878707).length < 2 ^ (prefixWord ++ tailWord_3878707).sum := by decide
  have hdescent : baseEnd_3878707 < baseStart_3878707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878716 : List Nat := [2, 2, 2, 2, 1, 1, 4, 8]
def baseStart_3878716 : Nat := 118140960795 + 3878716 * 2 ^ 59
def prefixEnd_3878716 : Nat := 4983230072969 + 3 ^ 40 * 3878716 * 2
def baseEnd_3878716 : Nat := 147529305947003832556453

theorem tailTrace_3878716 : CollatzResearch.WordTrace tailWord_3878716 prefixEnd_3878716 147529305947003832556453 := by
  unfold tailWord_3878716
  simp only [CollatzResearch.WordTrace]
  refine ⟨70734197308040919399504001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94312263077387892532672001 70734197308040919399504001)
  ·
    refine ⟨53050647981030689549628001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70734197308040919399504001 53050647981030689549628001)
    ·
      refine ⟨39787985985773017162221001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53050647981030689549628001 39787985985773017162221001)
      ·
        refine ⟨29840989489329762871665751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39787985985773017162221001 29840989489329762871665751)
        ·
          refine ⟨44761484233994644307498627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29840989489329762871665751 44761484233994644307498627)
          ·
            refine ⟨67142226350991966461247941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44761484233994644307498627 67142226350991966461247941)
            ·
              refine ⟨12589167440810993711483989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67142226350991966461247941 12589167440810993711483989)
              ·
                refine ⟨147529305947003832556453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12589167440810993711483989 147529305947003832556453)
                ·
                  rfl

theorem cell22_3878716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_3878716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878716 prefixEnd_3878716 := by exact prefixLift 3878716
  have htrace : WordTrace (prefixWord ++ tailWord_3878716) baseStart_3878716 baseEnd_3878716 := by
    simpa [prefixWord, tailWord_3878716, baseEnd_3878716] using wordTrace_append hprefix tailTrace_3878716
  have hstable : (prefixWord ++ tailWord_3878716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878716).length < 2 ^ (prefixWord ++ tailWord_3878716).sum := by decide
  have hdescent : baseEnd_3878716 < baseStart_3878716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878733 : List Nat := [1, 6, 1, 2, 1, 11]
def baseStart_3878733 : Nat := 118140960795 + 3878733 * 2 ^ 59
def prefixEnd_3878733 : Nat := 4983230072969 + 3 ^ 40 * 3878733 * 2
def baseEnd_3878733 : Nat := 16392216950252495251025

theorem tailTrace_3878733 : CollatzResearch.WordTrace tailWord_3878733 prefixEnd_3878733 16392216950252495251025 := by
  unfold tailWord_3878733
  simp only [CollatzResearch.WordTrace]
  refine ⟨141469014657020250702376853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94312676438013500468251235 141469014657020250702376853)
  ·
    refine ⟨6631360062047824251673915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141469014657020250702376853 6631360062047824251673915)
    ·
      refine ⟨9947040093071736377510873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631360062047824251673915 9947040093071736377510873)
      ·
        refine ⟨7460280069803802283133155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9947040093071736377510873 7460280069803802283133155)
        ·
          refine ⟨11190420104705703424699733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460280069803802283133155 11190420104705703424699733)
          ·
            refine ⟨16392216950252495251025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11190420104705703424699733 16392216950252495251025)
            ·
              rfl

theorem cell22_3878733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 11].length) (baseStart_3878733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878733 prefixEnd_3878733 := by exact prefixLift 3878733
  have htrace : WordTrace (prefixWord ++ tailWord_3878733) baseStart_3878733 baseEnd_3878733 := by
    simpa [prefixWord, tailWord_3878733, baseEnd_3878733] using wordTrace_append hprefix tailTrace_3878733
  have hstable : (prefixWord ++ tailWord_3878733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878733).length < 2 ^ (prefixWord ++ tailWord_3878733).sum := by decide
  have hdescent : baseEnd_3878733 < baseStart_3878733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878746 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_3878746 : Nat := 118140960795 + 3878746 * 2 ^ 59
def prefixEnd_3878746 : Nat := 4983230072969 + 3 ^ 40 * 3878746 * 2
def baseEnd_3878746 : Nat := 1327774023136124414757985

theorem tailTrace_3878746 : CollatzResearch.WordTrace tailWord_3878746 prefixEnd_3878746 1327774023136124414757985 := by
  unfold tailWord_3878746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35367372201493288480650023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94312992537315435948400061 35367372201493288480650023)
  ·
    refine ⟨53051058302239932720975035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35367372201493288480650023 53051058302239932720975035)
    ·
      refine ⟨79576587453359899081462553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53051058302239932720975035 79576587453359899081462553)
      ·
        refine ⟨59682440590019924311096915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79576587453359899081462553 59682440590019924311096915)
        ·
          refine ⟨89523660885029886466645373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59682440590019924311096915 89523660885029886466645373)
          ·
            refine ⟨33571372831886207424992015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89523660885029886466645373 33571372831886207424992015)
            ·
              refine ⟨50357059247829311137488023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33571372831886207424992015 50357059247829311137488023)
              ·
                refine ⟨75535588871743966706232035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50357059247829311137488023 75535588871743966706232035)
                ·
                  refine ⟨113303383307615950059348053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75535588871743966706232035 113303383307615950059348053)
                  ·
                    refine ⟨1327774023136124414757985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113303383307615950059348053 1327774023136124414757985)
                    ·
                      rfl

theorem cell22_3878746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_3878746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878746 prefixEnd_3878746 := by exact prefixLift 3878746
  have htrace : WordTrace (prefixWord ++ tailWord_3878746) baseStart_3878746 baseEnd_3878746 := by
    simpa [prefixWord, tailWord_3878746, baseEnd_3878746] using wordTrace_append hprefix tailTrace_3878746
  have hstable : (prefixWord ++ tailWord_3878746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878746).length < 2 ^ (prefixWord ++ tailWord_3878746).sum := by decide
  have hdescent : baseEnd_3878746 < baseStart_3878746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878812 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 5]
def baseStart_3878812 : Nat := 118140960795 + 3878812 * 2 ^ 59
def prefixEnd_3878812 : Nat := 4983230072969 + 3 ^ 40 * 3878812 * 2
def baseEnd_3878812 : Nat := 442598872094974080869261

theorem tailTrace_3878812 : CollatzResearch.WordTrace tailWord_3878812 prefixEnd_3878812 442598872094974080869261 := by
  unfold tailWord_3878812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70735948011867023597251345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94314597349156031463001793 70735948011867023597251345)
  ·
    refine ⟨53051961008900267697938509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70735948011867023597251345 53051961008900267697938509)
    ·
      refine ⟨19894485378337600386726941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53051961008900267697938509 19894485378337600386726941)
      ·
        refine ⟨7460432016876600145022603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19894485378337600386726941 7460432016876600145022603)
        ·
          refine ⟨11190648025314900217533905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460432016876600145022603 11190648025314900217533905)
          ·
            refine ⟨8392986018986175163150429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190648025314900217533905 8392986018986175163150429)
            ·
              refine ⟨3147369757119815686181411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8392986018986175163150429 3147369757119815686181411)
              ·
                refine ⟨4721054635679723529272117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147369757119815686181411 4721054635679723529272117)
                ·
                  refine ⟨442598872094974080869261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4721054635679723529272117 442598872094974080869261)
                  ·
                    rfl

theorem cell22_3878812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_3878812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878812 prefixEnd_3878812 := by exact prefixLift 3878812
  have htrace : WordTrace (prefixWord ++ tailWord_3878812) baseStart_3878812 baseEnd_3878812 := by
    simpa [prefixWord, tailWord_3878812, baseEnd_3878812] using wordTrace_append hprefix tailTrace_3878812
  have hstable : (prefixWord ++ tailWord_3878812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878812).length < 2 ^ (prefixWord ++ tailWord_3878812).sum := by decide
  have hdescent : baseEnd_3878812 < baseStart_3878812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878855 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 2, 3]
def baseStart_3878855 : Nat := 118140960795 + 3878855 * 2 ^ 59
def prefixEnd_3878855 : Nat := 4983230072969 + 3 ^ 40 * 3878855 * 2
def baseEnd_3878855 : Nat := 1327811336063684463782651

theorem tailTrace_3878855 : CollatzResearch.WordTrace tailWord_3878855 prefixEnd_3878855 1327811336063684463782651 := by
  unfold tailWord_3878855
  simp only [CollatzResearch.WordTrace]
  refine ⟨141473464362578265538318019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94315642908385510358878679 141473464362578265538318019)
  ·
    refine ⟨212210196543867398307477029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141473464362578265538318019 212210196543867398307477029)
    ·
      refine ⟨39789411851975137182651943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212210196543867398307477029 39789411851975137182651943)
      ·
        refine ⟨59684117777962705773977915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39789411851975137182651943 59684117777962705773977915)
        ·
          refine ⟨89526176666944058660966873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59684117777962705773977915 89526176666944058660966873)
          ·
            refine ⟨67144632500208043995725155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89526176666944058660966873 67144632500208043995725155)
            ·
              refine ⟨100716948750312065993587733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67144632500208043995725155 100716948750312065993587733)
              ·
                refine ⟨4721106972670878093449425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100716948750312065993587733 4721106972670878093449425)
                ·
                  refine ⟨3540830229503158570087069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721106972670878093449425 3540830229503158570087069)
                  ·
                    refine ⟨1327811336063684463782651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3540830229503158570087069 1327811336063684463782651)
                    ·
                      rfl

theorem cell22_3878855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_3878855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878855 prefixEnd_3878855 := by exact prefixLift 3878855
  have htrace : WordTrace (prefixWord ++ tailWord_3878855) baseStart_3878855 baseEnd_3878855 := by
    simpa [prefixWord, tailWord_3878855, baseEnd_3878855] using wordTrace_append hprefix tailTrace_3878855
  have hstable : (prefixWord ++ tailWord_3878855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878855).length < 2 ^ (prefixWord ++ tailWord_3878855).sum := by decide
  have hdescent : baseEnd_3878855 < baseStart_3878855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878887 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3878887 : Nat := 118140960795 + 3878887 * 2 ^ 59
def prefixEnd_3878887 : Nat := 4983230072969 + 3 ^ 40 * 3878887 * 2
def baseEnd_3878887 : Nat := 1327822290317647046982553

theorem tailTrace_3878887 : CollatzResearch.WordTrace tailWord_3878887 prefixEnd_3878887 1327822290317647046982553 := by
  unfold tailWord_3878887
  simp only [CollatzResearch.WordTrace]
  refine ⟨141474631498462335003482915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94316420998974890002321943 141474631498462335003482915)
  ·
    refine ⟨212211947247693502505224373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141474631498462335003482915 212211947247693502505224373)
    ·
      refine ⟨19894870054471265859864785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212211947247693502505224373 19894870054471265859864785)
      ·
        refine ⟨14921152540853449394898589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19894870054471265859864785 14921152540853449394898589)
        ·
          refine ⟨5595432202820043523086971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14921152540853449394898589 5595432202820043523086971)
          ·
            refine ⟨8393148304230065284630457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595432202820043523086971 8393148304230065284630457)
            ·
              refine ⟨6294861228172548963472843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393148304230065284630457 6294861228172548963472843)
              ·
                refine ⟨9442291842258823445209265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294861228172548963472843 9442291842258823445209265)
                ·
                  refine ⟨7081718881694117583906949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9442291842258823445209265 7081718881694117583906949)
                  ·
                    refine ⟨1327822290317647046982553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081718881694117583906949 1327822290317647046982553)
                    ·
                      rfl

theorem cell22_3878887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3878887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878887 prefixEnd_3878887 := by exact prefixLift 3878887
  have htrace : WordTrace (prefixWord ++ tailWord_3878887) baseStart_3878887 baseEnd_3878887 := by
    simpa [prefixWord, tailWord_3878887, baseEnd_3878887] using wordTrace_append hprefix tailTrace_3878887
  have hstable : (prefixWord ++ tailWord_3878887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878887).length < 2 ^ (prefixWord ++ tailWord_3878887).sum := by decide
  have hdescent : baseEnd_3878887 < baseStart_3878887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878928 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_3878928 : Nat := 118140960795 + 3878928 * 2 ^ 59
def prefixEnd_3878928 : Nat := 4983230072969 + 3 ^ 40 * 3878928 * 2
def baseEnd_3878928 : Nat := 1327836325455536606707427

theorem tailTrace_3878928 : CollatzResearch.WordTrace tailWord_3878928 prefixEnd_3878928 1327836325455536606707427 := by
  unfold tailWord_3878928
  simp only [CollatzResearch.WordTrace]
  refine ⟨70738063445656899502862719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94317417927542532670483625 70738063445656899502862719)
  ·
    refine ⟨106107095168485349254294079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70738063445656899502862719 106107095168485349254294079)
    ·
      refine ⟨159160642752728023881441119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106107095168485349254294079 159160642752728023881441119)
      ·
        refine ⟨238740964129092035822161679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159160642752728023881441119 238740964129092035822161679)
        ·
          refine ⟨358111446193638053733242519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238740964129092035822161679 358111446193638053733242519)
          ·
            refine ⟨537167169290457080599863779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358111446193638053733242519 537167169290457080599863779)
            ·
              refine ⟨805750753935685620899795669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537167169290457080599863779 805750753935685620899795669)
              ·
                refine ⟨18884783295367631739838961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 805750753935685620899795669 18884783295367631739838961)
                ·
                  refine ⟨14163587471525723804879221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18884783295367631739838961 14163587471525723804879221)
                  ·
                    refine ⟨1327836325455536606707427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14163587471525723804879221 1327836325455536606707427)
                    ·
                      rfl

theorem cell22_3878928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_3878928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878928 prefixEnd_3878928 := by exact prefixLift 3878928
  have htrace : WordTrace (prefixWord ++ tailWord_3878928) baseStart_3878928 baseEnd_3878928 := by
    simpa [prefixWord, tailWord_3878928, baseEnd_3878928] using wordTrace_append hprefix tailTrace_3878928
  have hstable : (prefixWord ++ tailWord_3878928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878928).length < 2 ^ (prefixWord ++ tailWord_3878928).sum := by decide
  have hdescent : baseEnd_3878928 < baseStart_3878928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878994 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3878994 : Nat := 118140960795 + 3878994 * 2 ^ 59
def prefixEnd_3878994 : Nat := 4983230072969 + 3 ^ 40 * 3878994 * 2
def baseEnd_3878994 : Nat := 1327858918604334434557225

theorem tailTrace_3878994 : CollatzResearch.WordTrace tailWord_3878994 prefixEnd_3878994 1327858918604334434557225 := by
  unfold tailWord_3878994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35369633527268673069407009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94319022739383128185085357 35369633527268673069407009)
  ·
    refine ⟨26527225145451504802055257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35369633527268673069407009 26527225145451504802055257)
    ·
      refine ⟨19895418859088628601541443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26527225145451504802055257 19895418859088628601541443)
      ·
        refine ⟨29843128288632942902312165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19895418859088628601541443 29843128288632942902312165)
        ·
          refine ⟨5595586554118676794183531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29843128288632942902312165 5595586554118676794183531)
          ·
            refine ⟨8393379831178015191275297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595586554118676794183531 8393379831178015191275297)
            ·
              refine ⟨6295034873383511393456473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393379831178015191275297 6295034873383511393456473)
              ·
                refine ⟨4721276155037633545092355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295034873383511393456473 4721276155037633545092355)
                ·
                  refine ⟨7081914232556450317638533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721276155037633545092355 7081914232556450317638533)
                  ·
                    refine ⟨1327858918604334434557225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081914232556450317638533 1327858918604334434557225)
                    ·
                      rfl

theorem cell22_3878994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3878994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3878994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3878994 prefixEnd_3878994 := by exact prefixLift 3878994
  have htrace : WordTrace (prefixWord ++ tailWord_3878994) baseStart_3878994 baseEnd_3878994 := by
    simpa [prefixWord, tailWord_3878994, baseEnd_3878994] using wordTrace_append hprefix tailTrace_3878994
  have hstable : (prefixWord ++ tailWord_3878994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878994).length < 2 ^ (prefixWord ++ tailWord_3878994).sum := by decide
  have hdescent : baseEnd_3878994 < baseStart_3878994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879020 : List Nat := [2, 2, 1, 1, 3, 5, 8]
def baseStart_3879020 : Nat := 118140960795 + 3879020 * 2 ^ 59
def prefixEnd_3879020 : Nat := 4983230072969 + 3 ^ 40 * 3879020 * 2
def baseEnd_3879020 : Nat := 49180289590210334570635

theorem tailTrace_3879020 : CollatzResearch.WordTrace tailWord_3879020 prefixEnd_3879020 49180289590210334570635 := by
  unfold tailWord_3879020
  simp only [CollatzResearch.WordTrace]
  refine ⟨70739741203490249359037257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94319654937986999145383009 70739741203490249359037257)
  ·
    refine ⟨53054805902617687019277943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70739741203490249359037257 53054805902617687019277943)
    ·
      refine ⟨79582208853926530528916915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53054805902617687019277943 79582208853926530528916915)
      ·
        refine ⟨119373313280889795793375373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79582208853926530528916915 119373313280889795793375373)
        ·
          refine ⟨44764992480333673422515765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119373313280889795793375373 44764992480333673422515765)
          ·
            refine ⟨4196718045031281883360853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44764992480333673422515765 4196718045031281883360853)
            ·
              refine ⟨49180289590210334570635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4196718045031281883360853 49180289590210334570635)
              ·
                rfl

theorem cell22_3879020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 8].length) (baseStart_3879020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879020 prefixEnd_3879020 := by exact prefixLift 3879020
  have htrace : WordTrace (prefixWord ++ tailWord_3879020) baseStart_3879020 baseEnd_3879020 := by
    simpa [prefixWord, tailWord_3879020, baseEnd_3879020] using wordTrace_append hprefix tailTrace_3879020
  have hstable : (prefixWord ++ tailWord_3879020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879020).length < 2 ^ (prefixWord ++ tailWord_3879020).sum := by decide
  have hdescent : baseEnd_3879020 < baseStart_3879020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879022 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3879022 : Nat := 118140960795 + 3879022 * 2 ^ 59
def prefixEnd_3879022 : Nat := 4983230072969 + 3 ^ 40 * 3879022 * 2
def baseEnd_3879022 : Nat := 1327868503576551694857139

theorem tailTrace_3879022 : CollatzResearch.WordTrace tailWord_3879022 prefixEnd_3879022 1327868503576551694857139 := by
  unfold tailWord_3879022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684944419121656632455915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94319703568648835373098213 17684944419121656632455915)
  ·
    refine ⟨26527416628682484948683873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17684944419121656632455915 26527416628682484948683873)
    ·
      refine ⟨19895562471511863711512905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26527416628682484948683873 19895562471511863711512905)
      ·
        refine ⟨14921671853633897783634679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19895562471511863711512905 14921671853633897783634679)
        ·
          refine ⟨22382507780450846675452019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14921671853633897783634679 22382507780450846675452019)
          ·
            refine ⟨33573761670676270013178029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22382507780450846675452019 33573761670676270013178029)
            ·
              refine ⟨12590160626503601254941761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33573761670676270013178029 12590160626503601254941761)
              ·
                refine ⟨9442620469877700941206321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12590160626503601254941761 9442620469877700941206321)
                ·
                  refine ⟨7081965352408275705904741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9442620469877700941206321 7081965352408275705904741)
                  ·
                    refine ⟨1327868503576551694857139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081965352408275705904741 1327868503576551694857139)
                    ·
                      rfl

theorem cell22_3879022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3879022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879022 prefixEnd_3879022 := by exact prefixLift 3879022
  have htrace : WordTrace (prefixWord ++ tailWord_3879022) baseStart_3879022 baseEnd_3879022 := by
    simpa [prefixWord, tailWord_3879022, baseEnd_3879022] using wordTrace_append hprefix tailTrace_3879022
  have hstable : (prefixWord ++ tailWord_3879022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879022).length < 2 ^ (prefixWord ++ tailWord_3879022).sum := by decide
  have hdescent : baseEnd_3879022 < baseStart_3879022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879062 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3879062 : Nat := 118140960795 + 3879062 * 2 ^ 59
def prefixEnd_3879062 : Nat := 4983230072969 + 3 ^ 40 * 3879062 * 2
def baseEnd_3879062 : Nat := 1327882196394004923857017

theorem tailTrace_3879062 : CollatzResearch.WordTrace tailWord_3879062 prefixEnd_3879062 1327882196394004923857017 := by
  unfold tailWord_3879062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842563392051771243193965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94320676181885559927402293 8842563392051771243193965)
  ·
    refine ⟨3315961272019414216197737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8842563392051771243193965 3315961272019414216197737)
    ·
      refine ⟨2486970954014560662148303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3315961272019414216197737 2486970954014560662148303)
      ·
        refine ⟨3730456431021840993222455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486970954014560662148303 3730456431021840993222455)
        ·
          refine ⟨5595684646532761489833683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730456431021840993222455 5595684646532761489833683)
          ·
            refine ⟨8393526969799142234750525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595684646532761489833683 8393526969799142234750525)
            ·
              refine ⟨3147572613674678338031447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8393526969799142234750525 3147572613674678338031447)
              ·
                refine ⟨4721358920512017507047171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147572613674678338031447 4721358920512017507047171)
                ·
                  refine ⟨7082038380768026260570757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721358920512017507047171 7082038380768026260570757)
                  ·
                    refine ⟨1327882196394004923857017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082038380768026260570757 1327882196394004923857017)
                    ·
                      rfl

theorem cell22_3879062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3879062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879062 prefixEnd_3879062 := by exact prefixLift 3879062
  have htrace : WordTrace (prefixWord ++ tailWord_3879062) baseStart_3879062 baseEnd_3879062 := by
    simpa [prefixWord, tailWord_3879062, baseEnd_3879062] using wordTrace_append hprefix tailTrace_3879062
  have hstable : (prefixWord ++ tailWord_3879062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879062).length < 2 ^ (prefixWord ++ tailWord_3879062).sum := by decide
  have hdescent : baseEnd_3879062 < baseStart_3879062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879112 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_3879112 : Nat := 118140960795 + 3879112 * 2 ^ 59
def prefixEnd_3879112 : Nat := 4983230072969 + 3 ^ 40 * 3879112 * 2
def baseEnd_3879112 : Nat := 1327899312415821460106863

theorem tailTrace_3879112 : CollatzResearch.WordTrace tailWord_3879112 prefixEnd_3879112 1327899312415821460106863 := by
  unfold tailWord_3879112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70741418961323599215211795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94321891948431465620282393 70741418961323599215211795)
  ·
    refine ⟨106112128441985398822817693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70741418961323599215211795 106112128441985398822817693)
    ·
      refine ⟨39792048165744524558556635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106112128441985398822817693 39792048165744524558556635)
      ·
        refine ⟨59688072248616786837834953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39792048165744524558556635 59688072248616786837834953)
        ·
          refine ⟨44766054186462590128376215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59688072248616786837834953 44766054186462590128376215)
          ·
            refine ⟨67149081279693885192564323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44766054186462590128376215 67149081279693885192564323)
            ·
              refine ⟨100723621919540827788846485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67149081279693885192564323 100723621919540827788846485)
              ·
                refine ⟨4721419777478476302602179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100723621919540827788846485 4721419777478476302602179)
                ·
                  refine ⟨7082129666217714453903269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721419777478476302602179 7082129666217714453903269)
                  ·
                    refine ⟨1327899312415821460106863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082129666217714453903269 1327899312415821460106863)
                    ·
                      rfl

theorem cell22_3879112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_3879112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879112 prefixEnd_3879112 := by exact prefixLift 3879112
  have htrace : WordTrace (prefixWord ++ tailWord_3879112) baseStart_3879112 baseEnd_3879112 := by
    simpa [prefixWord, tailWord_3879112, baseEnd_3879112] using wordTrace_append hprefix tailTrace_3879112
  have hstable : (prefixWord ++ tailWord_3879112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879112).length < 2 ^ (prefixWord ++ tailWord_3879112).sum := by decide
  have hdescent : baseEnd_3879112 < baseStart_3879112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879129 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 1, 4]
def baseStart_3879129 : Nat := 118140960795 + 3879129 * 2 ^ 59
def prefixEnd_3879129 : Nat := 4983230072969 + 3 ^ 40 * 3879129 * 2
def baseEnd_3879129 : Nat := 1327905131863239082431811

theorem tailTrace_3879129 : CollatzResearch.WordTrace tailWord_3879129 prefixEnd_3879129 1327905131863239082431811 := by
  unfold tailWord_3879129
  simp only [CollatzResearch.WordTrace]
  refine ⟨141483457963585610333792441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94322305309057073555861627 141483457963585610333792441)
  ·
    refine ⟨106112593472689207750344331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141483457963585610333792441 106112593472689207750344331)
    ·
      refine ⟨159168890209033811625516497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106112593472689207750344331 159168890209033811625516497)
      ·
        refine ⟨119376667656775358719137373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159168890209033811625516497 119376667656775358719137373)
        ·
          refine ⟨44766250371290759519676515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119376667656775358719137373 44766250371290759519676515)
          ·
            refine ⟨67149375556936139279514773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44766250371290759519676515 67149375556936139279514773)
            ·
              refine ⟨3147626979231381528727255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67149375556936139279514773 3147626979231381528727255)
              ·
                refine ⟨4721440468847072293090883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147626979231381528727255 4721440468847072293090883)
                ·
                  refine ⟨7082160703270608439636325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721440468847072293090883 7082160703270608439636325)
                  ·
                    refine ⟨1327905131863239082431811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082160703270608439636325 1327905131863239082431811)
                    ·
                      rfl

theorem cell22_3879129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_3879129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879129 prefixEnd_3879129 := by exact prefixLift 3879129
  have htrace : WordTrace (prefixWord ++ tailWord_3879129) baseStart_3879129 baseEnd_3879129 := by
    simpa [prefixWord, tailWord_3879129, baseEnd_3879129] using wordTrace_append hprefix tailTrace_3879129
  have hstable : (prefixWord ++ tailWord_3879129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879129).length < 2 ^ (prefixWord ++ tailWord_3879129).sum := by decide
  have hdescent : baseEnd_3879129 < baseStart_3879129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879144 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 4]
def baseStart_3879144 : Nat := 118140960795 + 3879144 * 2 ^ 59
def prefixEnd_3879144 : Nat := 4983230072969 + 3 ^ 40 * 3879144 * 2
def baseEnd_3879144 : Nat := 442636755556594681102255

theorem tailTrace_3879144 : CollatzResearch.WordTrace tailWord_3879144 prefixEnd_3879144 442636755556594681102255 := by
  unfold tailWord_3879144
  simp only [CollatzResearch.WordTrace]
  refine ⟨70742002529265633947794243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94322670039020845263725657 70742002529265633947794243)
  ·
    refine ⟨106113003793898450921691365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70742002529265633947794243 106113003793898450921691365)
    ·
      refine ⟨19896188211355959547817131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106113003793898450921691365 19896188211355959547817131)
      ·
        refine ⟨29844282317033939321725697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896188211355959547817131 29844282317033939321725697)
        ·
          refine ⟨22383211737775454491294273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29844282317033939321725697 22383211737775454491294273)
          ·
            refine ⟨16787408803331590868470705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22383211737775454491294273 16787408803331590868470705)
            ·
              refine ⟨12590556602498693151353029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16787408803331590868470705 12590556602498693151353029)
              ·
                refine ⟨2360729362968504965878693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12590556602498693151353029 2360729362968504965878693)
                ·
                  refine ⟨442636755556594681102255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360729362968504965878693 442636755556594681102255)
                  ·
                    rfl

theorem cell22_3879144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_3879144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879144 prefixEnd_3879144 := by exact prefixLift 3879144
  have htrace : WordTrace (prefixWord ++ tailWord_3879144) baseStart_3879144 baseEnd_3879144 := by
    simpa [prefixWord, tailWord_3879144, baseEnd_3879144] using wordTrace_append hprefix tailTrace_3879144
  have hstable : (prefixWord ++ tailWord_3879144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879144).length < 2 ^ (prefixWord ++ tailWord_3879144).sum := by decide
  have hdescent : baseEnd_3879144 < baseStart_3879144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879155 : List Nat := [1, 1, 1, 2, 2, 4, 2, 9]
def baseStart_3879155 : Nat := 118140960795 + 3879155 * 2 ^ 59
def prefixEnd_3879155 : Nat := 4983230072969 + 3 ^ 40 * 3879155 * 2
def baseEnd_3879155 : Nat := 147546003577175964586859

theorem tailTrace_3879155 : CollatzResearch.WordTrace tailWord_3879155 prefixEnd_3879155 147546003577175964586859 := by
  unfold tailWord_3879155
  simp only [CollatzResearch.WordTrace]
  refine ⟨141484406261491416774238919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94322937507660944516159279 141484406261491416774238919)
  ·
    refine ⟨212226609392237125161358379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141484406261491416774238919 212226609392237125161358379)
    ·
      refine ⟨318339914088355687742037569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212226609392237125161358379 318339914088355687742037569)
      ·
        refine ⟨238754935566266765806528177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318339914088355687742037569 238754935566266765806528177)
        ·
          refine ⟨179066201674700074354896133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238754935566266765806528177 179066201674700074354896133)
          ·
            refine ⟨33574912814006263941543025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179066201674700074354896133 33574912814006263941543025)
            ·
              refine ⟨25181184610504697956157269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33574912814006263941543025 25181184610504697956157269)
              ·
                refine ⟨147546003577175964586859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25181184610504697956157269 147546003577175964586859)
                ·
                  rfl

theorem cell22_3879155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 9].length) (baseStart_3879155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879155 prefixEnd_3879155 := by exact prefixLift 3879155
  have htrace : WordTrace (prefixWord ++ tailWord_3879155) baseStart_3879155 baseEnd_3879155 := by
    simpa [prefixWord, tailWord_3879155, baseEnd_3879155] using wordTrace_append hprefix tailTrace_3879155
  have hstable : (prefixWord ++ tailWord_3879155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879155).length < 2 ^ (prefixWord ++ tailWord_3879155).sum := by decide
  have hdescent : baseEnd_3879155 < baseStart_3879155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879187 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 5, 3]
def baseStart_3879187 : Nat := 118140960795 + 3879187 * 2 ^ 59
def prefixEnd_3879187 : Nat := 4983230072969 + 3 ^ 40 * 3879187 * 2
def baseEnd_3879187 : Nat := 1327924986448546264481633

theorem tailTrace_3879187 : CollatzResearch.WordTrace tailWord_3879187 prefixEnd_3879187 1327924986448546264481633 := by
  unfold tailWord_3879187
  simp only [CollatzResearch.WordTrace]
  refine ⟨141485573397375486239403815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94323715598250324159602543 141485573397375486239403815)
  ·
    refine ⟨212228360096063229359105723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141485573397375486239403815 212228360096063229359105723)
    ·
      refine ⟨318342540144094844038658585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212228360096063229359105723 318342540144094844038658585)
      ·
        refine ⟨238756905108071133028993939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318342540144094844038658585 238756905108071133028993939)
        ·
          refine ⟨358135357662106699543490909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238756905108071133028993939 358135357662106699543490909)
          ·
            refine ⟨134300759123290012328809091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358135357662106699543490909 134300759123290012328809091)
            ·
              refine ⟨201451138684935018493213637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134300759123290012328809091 201451138684935018493213637)
              ·
                refine ⟨37772088503425315967477557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201451138684935018493213637 37772088503425315967477557)
                ·
                  refine ⟨3541133297196123371951021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37772088503425315967477557 3541133297196123371951021)
                  ·
                    refine ⟨1327924986448546264481633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541133297196123371951021 1327924986448546264481633)
                    ·
                      rfl

theorem cell22_3879187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 3].length) (baseStart_3879187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879187 prefixEnd_3879187 := by exact prefixLift 3879187
  have htrace : WordTrace (prefixWord ++ tailWord_3879187) baseStart_3879187 baseEnd_3879187 := by
    simpa [prefixWord, tailWord_3879187, baseEnd_3879187] using wordTrace_append hprefix tailTrace_3879187
  have hstable : (prefixWord ++ tailWord_3879187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879187).length < 2 ^ (prefixWord ++ tailWord_3879187).sum := by decide
  have hdescent : baseEnd_3879187 < baseStart_3879187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879210 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3879210 : Nat := 118140960795 + 3879210 * 2 ^ 59
def prefixEnd_3879210 : Nat := 4983230072969 + 3 ^ 40 * 3879210 * 2
def baseEnd_3879210 : Nat := 1327932859818581871156563

theorem tailTrace_3879210 : CollatzResearch.WordTrace tailWord_3879210 prefixEnd_3879210 1327932859818581871156563 := by
  unfold tailWord_3879210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35371603069073040291872771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94324274850861440778327389 35371603069073040291872771)
  ·
    refine ⟨53057404603609560437809157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35371603069073040291872771 53057404603609560437809157)
    ·
      refine ⟨9948263363176792582089217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53057404603609560437809157 9948263363176792582089217)
      ·
        refine ⟨7461197522382594436566913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9948263363176792582089217 7461197522382594436566913)
        ·
          refine ⟨5595898141786945827425185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7461197522382594436566913 5595898141786945827425185)
          ·
            refine ⟨4196923606340209370568889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5595898141786945827425185 4196923606340209370568889)
            ·
              refine ⟨3147692704755157027926667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196923606340209370568889 3147692704755157027926667)
              ·
                refine ⟨4721539057132735541890001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147692704755157027926667 4721539057132735541890001)
                ·
                  refine ⟨3541154292849551656417501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721539057132735541890001 3541154292849551656417501)
                  ·
                    refine ⟨1327932859818581871156563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541154292849551656417501 1327932859818581871156563)
                    ·
                      rfl

theorem cell22_3879210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3879210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879210 prefixEnd_3879210 := by exact prefixLift 3879210
  have htrace : WordTrace (prefixWord ++ tailWord_3879210) baseStart_3879210 baseEnd_3879210 := by
    simpa [prefixWord, tailWord_3879210, baseEnd_3879210] using wordTrace_append hprefix tailTrace_3879210
  have hstable : (prefixWord ++ tailWord_3879210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879210).length < 2 ^ (prefixWord ++ tailWord_3879210).sum := by decide
  have hdescent : baseEnd_3879210 < baseStart_3879210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879307 : List Nat := [1, 1, 1, 1, 4, 5, 9]
def baseStart_3879307 : Nat := 118140960795 + 3879307 * 2 ^ 59
def prefixEnd_3879307 : Nat := 4983230072969 + 3 ^ 40 * 3879307 * 2
def baseEnd_3879307 : Nat := 49183928329663183388195

theorem tailTrace_3879307 : CollatzResearch.WordTrace tailWord_3879307 prefixEnd_3879307 49183928329663183388195 := by
  unfold tailWord_3879307
  simp only [CollatzResearch.WordTrace]
  refine ⟨141489950156940746733772175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94326633437960497822514783 141489950156940746733772175)
  ·
    refine ⟨212234925235411120100658263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141489950156940746733772175 212234925235411120100658263)
    ·
      refine ⟨318352387853116680150987395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212234925235411120100658263 318352387853116680150987395)
      ·
        refine ⟨477528581779675020226481093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318352387853116680150987395 477528581779675020226481093)
        ·
          refine ⟨89536609083689066292465205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477528581779675020226481093 89536609083689066292465205)
          ·
            refine ⟨8394057101595849964918613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89536609083689066292465205 8394057101595849964918613)
            ·
              refine ⟨49183928329663183388195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8394057101595849964918613 49183928329663183388195)
              ·
                rfl

theorem cell22_3879307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 9].length) (baseStart_3879307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879307 prefixEnd_3879307 := by exact prefixLift 3879307
  have htrace : WordTrace (prefixWord ++ tailWord_3879307) baseStart_3879307 baseEnd_3879307 := by
    simpa [prefixWord, tailWord_3879307, baseEnd_3879307] using wordTrace_append hprefix tailTrace_3879307
  have hstable : (prefixWord ++ tailWord_3879307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879307).length < 2 ^ (prefixWord ++ tailWord_3879307).sum := by decide
  have hdescent : baseEnd_3879307 < baseStart_3879307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879326 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3879326 : Nat := 118140960795 + 3879326 * 2 ^ 59
def prefixEnd_3879326 : Nat := 4983230072969 + 3 ^ 40 * 3879326 * 2
def baseEnd_3879326 : Nat := 1327972568989196235256207

theorem tailTrace_3879326 : CollatzResearch.WordTrace tailWord_3879326 prefixEnd_3879326 1327972568989196235256207 := by
  unfold tailWord_3879326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686330392983989122339229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94327095429247941985809221 17686330392983989122339229)
  ·
    refine ⟨6632373897368995920877211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17686330392983989122339229 6632373897368995920877211)
    ·
      refine ⟨9948560846053493881315817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6632373897368995920877211 9948560846053493881315817)
      ·
        refine ⟨7461420634540120410986863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9948560846053493881315817 7461420634540120410986863)
        ·
          refine ⟨11192130951810180616480295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461420634540120410986863 11192130951810180616480295)
          ·
            refine ⟨16788196427715270924720443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11192130951810180616480295 16788196427715270924720443)
            ·
              refine ⟨25182294641572906387080665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16788196427715270924720443 25182294641572906387080665)
              ·
                refine ⟨18886720981179679790310499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25182294641572906387080665 18886720981179679790310499)
                ·
                  refine ⟨28330081471769519685465749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18886720981179679790310499 28330081471769519685465749)
                  ·
                    refine ⟨1327972568989196235256207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28330081471769519685465749 1327972568989196235256207)
                    ·
                      rfl

theorem cell22_3879326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3879326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879326 prefixEnd_3879326 := by exact prefixLift 3879326
  have htrace : WordTrace (prefixWord ++ tailWord_3879326) baseStart_3879326 baseEnd_3879326 := by
    simpa [prefixWord, tailWord_3879326, baseEnd_3879326] using wordTrace_append hprefix tailTrace_3879326
  have hstable : (prefixWord ++ tailWord_3879326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879326).length < 2 ^ (prefixWord ++ tailWord_3879326).sum := by decide
  have hdescent : baseEnd_3879326 < baseStart_3879326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879328 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 2, 3]
def baseStart_3879328 : Nat := 118140960795 + 3879328 * 2 ^ 59
def prefixEnd_3879328 : Nat := 4983230072969 + 3 ^ 40 * 3879328 * 2
def baseEnd_3879328 : Nat := 1327973253630068896706201

theorem tailTrace_3879328 : CollatzResearch.WordTrace tailWord_3879328 prefixEnd_3879328 1327973253630068896706201 := by
  unfold tailWord_3879328
  simp only [CollatzResearch.WordTrace]
  refine ⟨70745358044932333660143319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94327144059909778213524425 70745358044932333660143319)
  ·
    refine ⟨106118037067398500490214979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70745358044932333660143319 106118037067398500490214979)
    ·
      refine ⟨159177055601097750735322469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106118037067398500490214979 159177055601097750735322469)
      ·
        refine ⟨29845697925205828262872963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159177055601097750735322469 29845697925205828262872963)
        ·
          refine ⟨44768546887808742394309445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29845697925205828262872963 44768546887808742394309445)
          ·
            refine ⟨8394102541464139198933021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44768546887808742394309445 8394102541464139198933021)
            ·
              refine ⟨3147788453049052199599883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8394102541464139198933021 3147788453049052199599883)
              ·
                refine ⟨4721682679573578299399825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147788453049052199599883 4721682679573578299399825)
                ·
                  refine ⟨3541262009680183724549869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721682679573578299399825 3541262009680183724549869)
                  ·
                    refine ⟨1327973253630068896706201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541262009680183724549869 1327973253630068896706201)
                    ·
                      rfl

theorem cell22_3879328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_3879328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879328 prefixEnd_3879328 := by exact prefixLift 3879328
  have htrace : WordTrace (prefixWord ++ tailWord_3879328) baseStart_3879328 baseEnd_3879328 := by
    simpa [prefixWord, tailWord_3879328, baseEnd_3879328] using wordTrace_append hprefix tailTrace_3879328
  have hstable : (prefixWord ++ tailWord_3879328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879328).length < 2 ^ (prefixWord ++ tailWord_3879328).sum := by decide
  have hdescent : baseEnd_3879328 < baseStart_3879328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879337 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_3879337 : Nat := 118140960795 + 3879337 * 2 ^ 59
def prefixEnd_3879337 : Nat := 4983230072969 + 3 ^ 40 * 3879337 * 2
def baseEnd_3879337 : Nat := 1327976334513995873231173

theorem tailTrace_3879337 : CollatzResearch.WordTrace tailWord_3879337 prefixEnd_3879337 1327976334513995873231173 := by
  unfold tailWord_3879337
  simp only [CollatzResearch.WordTrace]
  refine ⟨141491044346832061857364265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94327362897888041238242843 141491044346832061857364265)
  ·
    refine ⟨106118283260124046393023199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141491044346832061857364265 106118283260124046393023199)
    ·
      refine ⟨159177424890186069589534799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106118283260124046393023199 159177424890186069589534799)
      ·
        refine ⟨238766137335279104384302199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159177424890186069589534799 238766137335279104384302199)
        ·
          refine ⟨358149206002918656576453299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238766137335279104384302199 358149206002918656576453299)
          ·
            refine ⟨537223809004377984864679949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358149206002918656576453299 537223809004377984864679949)
            ·
              refine ⟨201458928376641744324254981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537223809004377984864679949 201458928376641744324254981)
              ·
                refine ⟨37773549070620327060797809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201458928376641744324254981 37773549070620327060797809)
                ·
                  refine ⟨28330161802965245295598357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37773549070620327060797809 28330161802965245295598357)
                  ·
                    refine ⟨1327976334513995873231173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28330161802965245295598357 1327976334513995873231173)
                    ·
                      rfl

theorem cell22_3879337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_3879337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879337 prefixEnd_3879337 := by exact prefixLift 3879337
  have htrace : WordTrace (prefixWord ++ tailWord_3879337) baseStart_3879337 baseEnd_3879337 := by
    simpa [prefixWord, tailWord_3879337, baseEnd_3879337] using wordTrace_append hprefix tailTrace_3879337
  have hstable : (prefixWord ++ tailWord_3879337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879337).length < 2 ^ (prefixWord ++ tailWord_3879337).sum := by decide
  have hdescent : baseEnd_3879337 < baseStart_3879337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879341 : List Nat := [1, 5, 2, 2, 2, 1, 1, 8]
def baseStart_3879341 : Nat := 118140960795 + 3879341 * 2 ^ 59
def prefixEnd_3879341 : Nat := 4983230072969 + 3 ^ 40 * 3879341 * 2
def baseEnd_3879341 : Nat := 147553078199526799570129

theorem tailTrace_3879341 : CollatzResearch.WordTrace tailWord_3879341 prefixEnd_3879341 147553078199526799570129 := by
  unfold tailWord_3879341
  simp only [CollatzResearch.WordTrace]
  refine ⟨141491190238817570540509877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94327460159211713693673251 141491190238817570540509877)
  ·
    refine ⟨13264799084889147238172801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141491190238817570540509877 13264799084889147238172801)
    ·
      refine ⟨9948599313666860428629601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13264799084889147238172801 9948599313666860428629601)
      ·
        refine ⟨7461449485250145321472201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9948599313666860428629601 7461449485250145321472201)
        ·
          refine ⟨5596087113937608991104151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7461449485250145321472201 5596087113937608991104151)
          ·
            refine ⟨8394130670906413486656227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596087113937608991104151 8394130670906413486656227)
            ·
              refine ⟨12591196006359620229984341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394130670906413486656227 12591196006359620229984341)
              ·
                refine ⟨147553078199526799570129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12591196006359620229984341 147553078199526799570129)
                ·
                  rfl

theorem cell22_3879341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 8].length) (baseStart_3879341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879341 prefixEnd_3879341 := by exact prefixLift 3879341
  have htrace : WordTrace (prefixWord ++ tailWord_3879341) baseStart_3879341 baseEnd_3879341 := by
    simpa [prefixWord, tailWord_3879341, baseEnd_3879341] using wordTrace_append hprefix tailTrace_3879341
  have hstable : (prefixWord ++ tailWord_3879341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879341).length < 2 ^ (prefixWord ++ tailWord_3879341).sum := by decide
  have hdescent : baseEnd_3879341 < baseStart_3879341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879461 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_3879461 : Nat := 118140960795 + 3879461 * 2 ^ 59
def prefixEnd_3879461 : Nat := 4983230072969 + 3 ^ 40 * 3879461 * 2
def baseEnd_3879461 : Nat := 1328018782248100883130793

theorem tailTrace_3879461 : CollatzResearch.WordTrace tailWord_3879461 prefixEnd_3879461 1328018782248100883130793 := by
  unfold tailWord_3879461
  simp only [CollatzResearch.WordTrace]
  refine ⟨141495566998382831034878237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94330377998921887356585491 141495566998382831034878237)
  ·
    refine ⟨53060837624393561638079339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141495566998382831034878237 53060837624393561638079339)
    ·
      refine ⟨79591256436590342457119009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53060837624393561638079339 79591256436590342457119009)
      ·
        refine ⟨59693442327442756842839257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79591256436590342457119009 59693442327442756842839257)
        ·
          refine ⟨44770081745582067632129443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59693442327442756842839257 44770081745582067632129443)
          ·
            refine ⟨67155122618373101448194165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44770081745582067632129443 67155122618373101448194165)
            ·
              refine ⟨6295792745472478260768203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67155122618373101448194165 6295792745472478260768203)
              ·
                refine ⟨9443689118208717391152305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295792745472478260768203 9443689118208717391152305)
                ·
                  refine ⟨7082766838656538043364229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443689118208717391152305 7082766838656538043364229)
                  ·
                    refine ⟨1328018782248100883130793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082766838656538043364229 1328018782248100883130793)
                    ·
                      rfl

theorem cell22_3879461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_3879461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879461 prefixEnd_3879461 := by exact prefixLift 3879461
  have htrace : WordTrace (prefixWord ++ tailWord_3879461) baseStart_3879461 baseEnd_3879461 := by
    simpa [prefixWord, tailWord_3879461, baseEnd_3879461] using wordTrace_append hprefix tailTrace_3879461
  have hstable : (prefixWord ++ tailWord_3879461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879461).length < 2 ^ (prefixWord ++ tailWord_3879461).sum := by decide
  have hdescent : baseEnd_3879461 < baseStart_3879461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879508 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_3879508 : Nat := 118140960795 + 3879508 * 2 ^ 59
def prefixEnd_3879508 : Nat := 4983230072969 + 3 ^ 40 * 3879508 * 2
def baseEnd_3879508 : Nat := 1328034871308608427205649

theorem tailTrace_3879508 : CollatzResearch.WordTrace tailWord_3879508 prefixEnd_3879508 1328034871308608427205649 := by
  unfold tailWord_3879508
  simp only [CollatzResearch.WordTrace]
  refine ⟨70748640614606279030919589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94331520819475038707892785 70748640614606279030919589)
  ·
    refine ⟨13265370115238677318297423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70748640614606279030919589 13265370115238677318297423)
    ·
      refine ⟨19898055172858015977446135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13265370115238677318297423 19898055172858015977446135)
      ·
        refine ⟨29847082759287023966169203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19898055172858015977446135 29847082759287023966169203)
        ·
          refine ⟨44770624138930535949253805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29847082759287023966169203 44770624138930535949253805)
          ·
            refine ⟨16788984052098950980970177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44770624138930535949253805 16788984052098950980970177)
            ·
              refine ⟨12591738039074213235727633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16788984052098950980970177 12591738039074213235727633)
              ·
                refine ⟨9443803529305659926795725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12591738039074213235727633 9443803529305659926795725)
                ·
                  refine ⟨3541426323489622472548397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9443803529305659926795725 3541426323489622472548397)
                  ·
                    refine ⟨1328034871308608427205649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541426323489622472548397 1328034871308608427205649)
                    ·
                      rfl

theorem cell22_3879508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_3879508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879508 prefixEnd_3879508 := by exact prefixLift 3879508
  have htrace : WordTrace (prefixWord ++ tailWord_3879508) baseStart_3879508 baseEnd_3879508 := by
    simpa [prefixWord, tailWord_3879508, baseEnd_3879508] using wordTrace_append hprefix tailTrace_3879508
  have hstable : (prefixWord ++ tailWord_3879508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879508).length < 2 ^ (prefixWord ++ tailWord_3879508).sum := by decide
  have hdescent : baseEnd_3879508 < baseStart_3879508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879519 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_3879519 : Nat := 118140960795 + 3879519 * 2 ^ 59
def prefixEnd_3879519 : Nat := 4983230072969 + 3 ^ 40 * 3879519 * 2
def baseEnd_3879519 : Nat := 1328038636833408065180615

theorem tailTrace_3879519 : CollatzResearch.WordTrace tailWord_3879519 prefixEnd_3879519 1328038636833408065180615 := by
  unfold tailWord_3879519
  simp only [CollatzResearch.WordTrace]
  refine ⟨141497682432172706940489611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94331788288115137960326407 141497682432172706940489611)
  ·
    refine ⟨212246523648259060410734417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141497682432172706940489611 212246523648259060410734417)
    ·
      refine ⟨159184892736194295308050813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212246523648259060410734417 159184892736194295308050813)
      ·
        refine ⟨59694334776072860740519055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159184892736194295308050813 59694334776072860740519055)
        ·
          refine ⟨89541502164109291110778583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59694334776072860740519055 89541502164109291110778583)
          ·
            refine ⟨134312253246163936666167875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89541502164109291110778583 134312253246163936666167875)
            ·
              refine ⟨201468379869245904999251813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134312253246163936666167875 201468379869245904999251813)
              ·
                refine ⟨37775321225483607187359715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201468379869245904999251813 37775321225483607187359715)
                ·
                  refine ⟨56662981838225410781039573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37775321225483607187359715 56662981838225410781039573)
                  ·
                    refine ⟨1328038636833408065180615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56662981838225410781039573 1328038636833408065180615)
                    ·
                      rfl

theorem cell22_3879519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_3879519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879519 prefixEnd_3879519 := by exact prefixLift 3879519
  have htrace : WordTrace (prefixWord ++ tailWord_3879519) baseStart_3879519 baseEnd_3879519 := by
    simpa [prefixWord, tailWord_3879519, baseEnd_3879519] using wordTrace_append hprefix tailTrace_3879519
  have hstable : (prefixWord ++ tailWord_3879519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879519).length < 2 ^ (prefixWord ++ tailWord_3879519).sum := by decide
  have hdescent : baseEnd_3879519 < baseStart_3879519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879542 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3879542 : Nat := 118140960795 + 3879542 * 2 ^ 59
def prefixEnd_3879542 : Nat := 4983230072969 + 3 ^ 40 * 3879542 * 2
def baseEnd_3879542 : Nat := 1328046510203443671855545

theorem tailTrace_3879542 : CollatzResearch.WordTrace tailWord_3879542 prefixEnd_3879542 1328046510203443671855545 := by
  unfold tailWord_3879542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843657581943086366786055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94332347540726254579051253 8843657581943086366786055)
  ·
    refine ⟨13265486372914629550179083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8843657581943086366786055 13265486372914629550179083)
    ·
      refine ⟨19898229559371944325268625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13265486372914629550179083 19898229559371944325268625)
      ·
        refine ⟨14923672169528958243951469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19898229559371944325268625 14923672169528958243951469)
        ·
          refine ⟨5596377063573359341481801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14923672169528958243951469 5596377063573359341481801)
          ·
            refine ⟨4197282797680019506111351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5596377063573359341481801 4197282797680019506111351)
            ·
              refine ⟨6295924196520029259167027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197282797680019506111351 6295924196520029259167027)
              ·
                refine ⟨9443886294780043888750541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295924196520029259167027 9443886294780043888750541)
                ·
                  refine ⟨3541457360542516458281453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9443886294780043888750541 3541457360542516458281453)
                  ·
                    refine ⟨1328046510203443671855545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541457360542516458281453 1328046510203443671855545)
                    ·
                      rfl

theorem cell22_3879542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3879542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879542 prefixEnd_3879542 := by exact prefixLift 3879542
  have htrace : WordTrace (prefixWord ++ tailWord_3879542) baseStart_3879542 baseEnd_3879542 := by
    simpa [prefixWord, tailWord_3879542, baseEnd_3879542] using wordTrace_append hprefix tailTrace_3879542
  have hstable : (prefixWord ++ tailWord_3879542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879542).length < 2 ^ (prefixWord ++ tailWord_3879542).sum := by decide
  have hdescent : baseEnd_3879542 < baseStart_3879542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879566 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_3879566 : Nat := 118140960795 + 3879566 * 2 ^ 59
def prefixEnd_3879566 : Nat := 4983230072969 + 3 ^ 40 * 3879566 * 2
def baseEnd_3879566 : Nat := 442684908631305203085157

theorem tailTrace_3879566 : CollatzResearch.WordTrace tailWord_3879566 prefixEnd_3879566 442684908631305203085157 := by
  unfold tailWord_3879566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17687424582875304245931319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94332931108668289311633701 17687424582875304245931319)
  ·
    refine ⟨26531136874312956368896979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17687424582875304245931319 26531136874312956368896979)
    ·
      refine ⟨39796705311469434553345469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26531136874312956368896979 39796705311469434553345469)
      ·
        refine ⟨14923764491801037957504551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39796705311469434553345469 14923764491801037957504551)
        ·
          refine ⟨22385646737701556936256827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923764491801037957504551 22385646737701556936256827)
          ·
            refine ⟨33578470106552335404385241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22385646737701556936256827 33578470106552335404385241)
            ·
              refine ⟨25183852579914251553288931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33578470106552335404385241 25183852579914251553288931)
              ·
                refine ⟨37775778869871377329933397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25183852579914251553288931 37775778869871377329933397)
                ·
                  refine ⟨442684908631305203085157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37775778869871377329933397 442684908631305203085157)
                  ·
                    rfl

theorem cell22_3879566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_3879566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879566 prefixEnd_3879566 := by exact prefixLift 3879566
  have htrace : WordTrace (prefixWord ++ tailWord_3879566) baseStart_3879566 baseEnd_3879566 := by
    simpa [prefixWord, tailWord_3879566, baseEnd_3879566] using wordTrace_append hprefix tailTrace_3879566
  have hstable : (prefixWord ++ tailWord_3879566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879566).length < 2 ^ (prefixWord ++ tailWord_3879566).sum := by decide
  have hdescent : baseEnd_3879566 < baseStart_3879566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879581 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3879581 : Nat := 118140960795 + 3879581 * 2 ^ 59
def prefixEnd_3879581 : Nat := 4983230072969 + 3 ^ 40 * 3879581 * 2
def baseEnd_3879581 : Nat := 1328059860700460570130425

theorem tailTrace_3879581 : CollatzResearch.WordTrace tailWord_3879581 prefixEnd_3879581 1328059860700460570130425 := by
  unfold tailWord_3879581
  simp only [CollatzResearch.WordTrace]
  refine ⟨141499943757948091529246597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94333295838632061019497731 141499943757948091529246597)
  ·
    refine ⟨26531239454615267161733737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141499943757948091529246597 26531239454615267161733737)
    ·
      refine ⟨19898429590961450371300303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26531239454615267161733737 19898429590961450371300303)
      ·
        refine ⟨29847644386442175556950455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19898429590961450371300303 29847644386442175556950455)
        ·
          refine ⟨44771466579663263335425683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29847644386442175556950455 44771466579663263335425683)
          ·
            refine ⟨67157199869494895003138525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44771466579663263335425683 67157199869494895003138525)
            ·
              refine ⟨25183949951060585626176947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67157199869494895003138525 25183949951060585626176947)
              ·
                refine ⟨37775924926590878439265421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25183949951060585626176947 37775924926590878439265421)
                ·
                  refine ⟨14165971847471579414724533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37775924926590878439265421 14165971847471579414724533)
                  ·
                    refine ⟨1328059860700460570130425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14165971847471579414724533 1328059860700460570130425)
                    ·
                      rfl

theorem cell22_3879581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3879581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879581 prefixEnd_3879581 := by exact prefixLift 3879581
  have htrace : WordTrace (prefixWord ++ tailWord_3879581) baseStart_3879581 baseEnd_3879581 := by
    simpa [prefixWord, tailWord_3879581, baseEnd_3879581] using wordTrace_append hprefix tailTrace_3879581
  have hstable : (prefixWord ++ tailWord_3879581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879581).length < 2 ^ (prefixWord ++ tailWord_3879581).sum := by decide
  have hdescent : baseEnd_3879581 < baseStart_3879581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879630 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_3879630 : Nat := 118140960795 + 3879630 * 2 ^ 59
def prefixEnd_3879630 : Nat := 4983230072969 + 3 ^ 40 * 3879630 * 2
def baseEnd_3879630 : Nat := 1328076634401840775655275

theorem tailTrace_3879630 : CollatzResearch.WordTrace tailWord_3879630 prefixEnd_3879630 1328076634401840775655275 := by
  unfold tailWord_3879630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17687716366846321612222543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94334487289847048598520229 17687716366846321612222543)
  ·
    refine ⟨26531574550269482418333815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17687716366846321612222543 26531574550269482418333815)
    ·
      refine ⟨39797361825404223627500723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26531574550269482418333815 39797361825404223627500723)
      ·
        refine ⟨59696042738106335441251085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39797361825404223627500723 59696042738106335441251085)
        ·
          refine ⟨22386016026789875790469157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59696042738106335441251085 22386016026789875790469157)
          ·
            refine ⟨4197378005023101710712967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22386016026789875790469157 4197378005023101710712967)
            ·
              refine ⟨6296067007534652566069451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197378005023101710712967 6296067007534652566069451)
              ·
                refine ⟨9444100511301978849104177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296067007534652566069451 9444100511301978849104177)
                ·
                  refine ⟨7083075383476484136828133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9444100511301978849104177 7083075383476484136828133)
                  ·
                    refine ⟨1328076634401840775655275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083075383476484136828133 1328076634401840775655275)
                    ·
                      rfl

theorem cell22_3879630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_3879630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879630 prefixEnd_3879630 := by exact prefixLift 3879630
  have htrace : WordTrace (prefixWord ++ tailWord_3879630) baseStart_3879630 baseEnd_3879630 := by
    simpa [prefixWord, tailWord_3879630, baseEnd_3879630] using wordTrace_append hprefix tailTrace_3879630
  have hstable : (prefixWord ++ tailWord_3879630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879630).length < 2 ^ (prefixWord ++ tailWord_3879630).sum := by decide
  have hdescent : baseEnd_3879630 < baseStart_3879630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879767 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 2, 3]
def baseStart_3879767 : Nat := 118140960795 + 3879767 * 2 ^ 59
def prefixEnd_3879767 : Nat := 4983230072969 + 3 ^ 40 * 3879767 * 2
def baseEnd_3879767 : Nat := 1328123532301618084979855

theorem tailTrace_3879767 : CollatzResearch.WordTrace tailWord_3879767 prefixEnd_3879767 1328123532301618084979855 := by
  unfold tailWord_3879767
  simp only [CollatzResearch.WordTrace]
  refine ⟨141506727735274245295517555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94337818490182830197011703 141506727735274245295517555)
  ·
    refine ⟨212260091602911367943276333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141506727735274245295517555 212260091602911367943276333)
    ·
      refine ⟨79597534351091762978728625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212260091602911367943276333 79597534351091762978728625)
      ·
        refine ⟨59698150763318822234046469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79597534351091762978728625 59698150763318822234046469)
        ·
          refine ⟨11193403268122279168883713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59698150763318822234046469 11193403268122279168883713)
          ·
            refine ⟨8395052451091709376662785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11193403268122279168883713 8395052451091709376662785)
            ·
              refine ⟨6296289338318782032497089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8395052451091709376662785 6296289338318782032497089)
              ·
                refine ⟨4722217003739086524372817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6296289338318782032497089 4722217003739086524372817)
                ·
                  refine ⟨3541662752804314893279613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722217003739086524372817 3541662752804314893279613)
                  ·
                    refine ⟨1328123532301618084979855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541662752804314893279613 1328123532301618084979855)
                    ·
                      rfl

theorem cell22_3879767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_3879767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879767 prefixEnd_3879767 := by exact prefixLift 3879767
  have htrace : WordTrace (prefixWord ++ tailWord_3879767) baseStart_3879767 baseEnd_3879767 := by
    simpa [prefixWord, tailWord_3879767, baseEnd_3879767] using wordTrace_append hprefix tailTrace_3879767
  have hstable : (prefixWord ++ tailWord_3879767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879767).length < 2 ^ (prefixWord ++ tailWord_3879767).sum := by decide
  have hdescent : baseEnd_3879767 < baseStart_3879767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879780 : List Nat := [2, 3, 1, 1, 4, 3, 1, 7]
def baseStart_3879780 : Nat := 118140960795 + 3879780 * 2 ^ 59
def prefixEnd_3879780 : Nat := 4983230072969 + 3 ^ 40 * 3879780 * 2
def baseEnd_3879780 : Nat := 147569775829698931600535

theorem tailTrace_3879780 : CollatzResearch.WordTrace tailWord_3879780 prefixEnd_3879780 147569775829698931600535 := by
  unfold tailWord_3879780
  simp only [CollatzResearch.WordTrace]
  refine ⟨70753600942113574257870397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94338134589484765677160529 70753600942113574257870397)
  ·
    refine ⟨26532600353292590346701399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70753600942113574257870397 26532600353292590346701399)
    ·
      refine ⟨39798900529938885520052099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26532600353292590346701399 39798900529938885520052099)
      ·
        refine ⟨59698350794908328280078149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39798900529938885520052099 59698350794908328280078149)
        ·
          refine ⟨11193440774045311552514653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59698350794908328280078149 11193440774045311552514653)
          ·
            refine ⟨4197540290266991832192995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11193440774045311552514653 4197540290266991832192995)
            ·
              refine ⟨6296310435400487748289493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197540290266991832192995 6296310435400487748289493)
              ·
                refine ⟨147569775829698931600535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6296310435400487748289493 147569775829698931600535)
                ·
                  rfl

theorem cell22_3879780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 7].length) (baseStart_3879780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879780 prefixEnd_3879780 := by exact prefixLift 3879780
  have htrace : WordTrace (prefixWord ++ tailWord_3879780) baseStart_3879780 baseEnd_3879780 := by
    simpa [prefixWord, tailWord_3879780, baseEnd_3879780] using wordTrace_append hprefix tailTrace_3879780
  have hstable : (prefixWord ++ tailWord_3879780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879780).length < 2 ^ (prefixWord ++ tailWord_3879780).sum := by decide
  have hdescent : baseEnd_3879780 < baseStart_3879780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879906 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3879906 : Nat := 118140960795 + 3879906 * 2 ^ 59
def prefixEnd_3879906 : Nat := 4983230072969 + 3 ^ 40 * 3879906 * 2
def baseEnd_3879906 : Nat := 1328171114842268055754429

theorem tailTrace_3879906 : CollatzResearch.WordTrace tailWord_3879906 prefixEnd_3879906 1328171114842268055754429 := by
  unfold tailWord_3879906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35377949370442668008706893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94341198321180448023218381 35377949370442668008706893)
  ·
    refine ⟨13266731013916000503265085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35377949370442668008706893 13266731013916000503265085)
    ·
      refine ⟨4975024130218500188724407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13266731013916000503265085 4975024130218500188724407)
      ·
        refine ⟨7462536195327750283086611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975024130218500188724407 7462536195327750283086611)
        ·
          refine ⟨11193804292991625424629917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7462536195327750283086611 11193804292991625424629917)
          ·
            refine ⟨4197676609871859534236219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11193804292991625424629917 4197676609871859534236219)
            ·
              refine ⟨6296514914807789301354329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197676609871859534236219 6296514914807789301354329)
              ·
                refine ⟨4722386186105841976015747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6296514914807789301354329 4722386186105841976015747)
                ·
                  refine ⟨7083579279158762964023621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722386186105841976015747 7083579279158762964023621)
                  ·
                    refine ⟨1328171114842268055754429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083579279158762964023621 1328171114842268055754429)
                    ·
                      rfl

theorem cell22_3879906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3879906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879906 prefixEnd_3879906 := by exact prefixLift 3879906
  have htrace : WordTrace (prefixWord ++ tailWord_3879906) baseStart_3879906 baseEnd_3879906 := by
    simpa [prefixWord, tailWord_3879906, baseEnd_3879906] using wordTrace_append hprefix tailTrace_3879906
  have hstable : (prefixWord ++ tailWord_3879906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879906).length < 2 ^ (prefixWord ++ tailWord_3879906).sum := by decide
  have hdescent : baseEnd_3879906 < baseStart_3879906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879964 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_3879964 : Nat := 118140960795 + 3879964 * 2 ^ 59
def prefixEnd_3879964 : Nat := 4983230072969 + 3 ^ 40 * 3879964 * 2
def baseEnd_3879964 : Nat := 1328190969427575237804251

theorem tailTrace_3879964 : CollatzResearch.WordTrace tailWord_3879964 prefixEnd_3879964 1328190969427575237804251 := by
  unfold tailWord_3879964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70756956457780273970219473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94342608610373698626959297 70756956457780273970219473)
  ·
    refine ⟨53067717343335205477664605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70756956457780273970219473 53067717343335205477664605)
    ·
      refine ⟨19900394003750702054124227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53067717343335205477664605 19900394003750702054124227)
      ·
        refine ⟨29850591005626053081186341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19900394003750702054124227 29850591005626053081186341)
        ·
          refine ⟨5596985813554884952722439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29850591005626053081186341 5596985813554884952722439)
          ·
            refine ⟨8395478720332327429083659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596985813554884952722439 8395478720332327429083659)
            ·
              refine ⟨12593218080498491143625489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395478720332327429083659 12593218080498491143625489)
              ·
                refine ⟨9444913560373868357719117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12593218080498491143625489 9444913560373868357719117)
                ·
                  refine ⟨3541842585140200634144669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9444913560373868357719117 3541842585140200634144669)
                  ·
                    refine ⟨1328190969427575237804251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541842585140200634144669 1328190969427575237804251)
                    ·
                      rfl

theorem cell22_3879964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_3879964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3879964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3879964 prefixEnd_3879964 := by exact prefixLift 3879964
  have htrace : WordTrace (prefixWord ++ tailWord_3879964) baseStart_3879964 baseEnd_3879964 := by
    simpa [prefixWord, tailWord_3879964, baseEnd_3879964] using wordTrace_append hprefix tailTrace_3879964
  have hstable : (prefixWord ++ tailWord_3879964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879964).length < 2 ^ (prefixWord ++ tailWord_3879964).sum := by decide
  have hdescent : baseEnd_3879964 < baseStart_3879964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880005 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 6]
def baseStart_3880005 : Nat := 118140960795 + 3880005 * 2 ^ 59
def prefixEnd_3880005 : Nat := 4983230072969 + 3 ^ 40 * 3880005 * 2
def baseEnd_3880005 : Nat := 442735001521821599176375

theorem tailTrace_3880005 : CollatzResearch.WordTrace tailWord_3880005 prefixEnd_3880005 442735001521821599176375 := by
  unfold tailWord_3880005
  simp only [CollatzResearch.WordTrace]
  refine ⟨141515408308412011942681469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94343605538941341295120979 141515408308412011942681469)
  ·
    refine ⟨53068278115654504478505551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141515408308412011942681469 53068278115654504478505551)
    ·
      refine ⟨79602417173481756717758327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53068278115654504478505551 79602417173481756717758327)
      ·
        refine ⟨119403625760222635076637491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79602417173481756717758327 119403625760222635076637491)
        ·
          refine ⟨179105438640333952614956237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119403625760222635076637491 179105438640333952614956237)
          ·
            refine ⟨67164539490125232230608589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179105438640333952614956237 67164539490125232230608589)
            ·
              refine ⟨25186702308796962086478221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67164539490125232230608589 25186702308796962086478221)
              ·
                refine ⟨9445013365798860782429333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25186702308796962086478221 9445013365798860782429333)
                ·
                  refine ⟨442735001521821599176375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9445013365798860782429333 442735001521821599176375)
                  ·
                    rfl

theorem cell22_3880005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_3880005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880005 prefixEnd_3880005 := by exact prefixLift 3880005
  have htrace : WordTrace (prefixWord ++ tailWord_3880005) baseStart_3880005 baseEnd_3880005 := by
    simpa [prefixWord, tailWord_3880005, baseEnd_3880005] using wordTrace_append hprefix tailTrace_3880005
  have hstable : (prefixWord ++ tailWord_3880005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880005).length < 2 ^ (prefixWord ++ tailWord_3880005).sum := by decide
  have hdescent : baseEnd_3880005 < baseStart_3880005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880037 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_3880037 : Nat := 118140960795 + 3880037 * 2 ^ 59
def prefixEnd_3880037 : Nat := 4983230072969 + 3 ^ 40 * 3880037 * 2
def baseEnd_3880037 : Nat := 1328215958819427380729027

theorem tailTrace_3880037 : CollatzResearch.WordTrace tailWord_3880037 prefixEnd_3880037 1328215958819427380729027 := by
  unfold tailWord_3880037
  simp only [CollatzResearch.WordTrace]
  refine ⟨141516575444296081407846365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94344383629530720938564243 141516575444296081407846365)
  ·
    refine ⟨53068715791611030527942387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141516575444296081407846365 53068715791611030527942387)
    ·
      refine ⟨79603073687416545791913581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53068715791611030527942387 79603073687416545791913581)
      ·
        refine ⟨29851152632781204671967593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79603073687416545791913581 29851152632781204671967593)
        ·
          refine ⟨22388364474585903503975695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29851152632781204671967593 22388364474585903503975695)
          ·
            refine ⟨33582546711878855255963543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22388364474585903503975695 33582546711878855255963543)
            ·
              refine ⟨50373820067818282883945315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33582546711878855255963543 50373820067818282883945315)
              ·
                refine ⟨75560730101727424325917973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50373820067818282883945315 75560730101727424325917973)
                ·
                  refine ⟨3541909223518473015277405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75560730101727424325917973 3541909223518473015277405)
                  ·
                    refine ⟨1328215958819427380729027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541909223518473015277405 1328215958819427380729027)
                    ·
                      rfl

theorem cell22_3880037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_3880037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880037 prefixEnd_3880037 := by exact prefixLift 3880037
  have htrace : WordTrace (prefixWord ++ tailWord_3880037) baseStart_3880037 baseEnd_3880037 := by
    simpa [prefixWord, tailWord_3880037, baseEnd_3880037] using wordTrace_append hprefix tailTrace_3880037
  have hstable : (prefixWord ++ tailWord_3880037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880037).length < 2 ^ (prefixWord ++ tailWord_3880037).sum := by decide
  have hdescent : baseEnd_3880037 < baseStart_3880037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880039 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 4]
def baseStart_3880039 : Nat := 118140960795 + 3880039 * 2 ^ 59
def prefixEnd_3880039 : Nat := 4983230072969 + 3 ^ 40 * 3880039 * 2
def baseEnd_3880039 : Nat := 442738881153433347393007

theorem tailTrace_3880039 : CollatzResearch.WordTrace tailWord_3880039 prefixEnd_3880039 442738881153433347393007 := by
  unfold tailWord_3880039
  simp only [CollatzResearch.WordTrace]
  refine ⟨141516648390288835749419171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94344432260192557166279447 141516648390288835749419171)
  ·
    refine ⟨212274972585433253624128757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141516648390288835749419171 212274972585433253624128757)
    ·
      refine ⟨19900778679884367527262071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212274972585433253624128757 19900778679884367527262071)
      ·
        refine ⟨29851168019826551290893107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19900778679884367527262071 29851168019826551290893107)
        ·
          refine ⟨44776752029739826936339661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29851168019826551290893107 44776752029739826936339661)
          ·
            refine ⟨16791282011152435101127373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44776752029739826936339661 16791282011152435101127373)
            ·
              refine ⟨6296730754182163162922765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16791282011152435101127373 6296730754182163162922765)
              ·
                refine ⟨2361274032818311186096037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6296730754182163162922765 2361274032818311186096037)
                ·
                  refine ⟨442738881153433347393007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361274032818311186096037 442738881153433347393007)
                  ·
                    rfl

theorem cell22_3880039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 4].length) (baseStart_3880039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880039 prefixEnd_3880039 := by exact prefixLift 3880039
  have htrace : WordTrace (prefixWord ++ tailWord_3880039) baseStart_3880039 baseEnd_3880039 := by
    simpa [prefixWord, tailWord_3880039, baseEnd_3880039] using wordTrace_append hprefix tailTrace_3880039
  have hstable : (prefixWord ++ tailWord_3880039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880039).length < 2 ^ (prefixWord ++ tailWord_3880039).sum := by decide
  have hdescent : baseEnd_3880039 < baseStart_3880039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880054 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_3880054 : Nat := 118140960795 + 3880054 * 2 ^ 59
def prefixEnd_3880054 : Nat := 4983230072969 + 3 ^ 40 * 3880054 * 2
def baseEnd_3880054 : Nat := 1328221778266845003053975

theorem tailTrace_3880054 : CollatzResearch.WordTrace tailWord_3880054 prefixEnd_3880054 1328221778266845003053975 := by
  unfold tailWord_3880054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844824717827155831950951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94344796990156328874143477 8844824717827155831950951)
  ·
    refine ⟨13267237076740733747926427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844824717827155831950951 13267237076740733747926427)
    ·
      refine ⟨19900855615111100621889641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13267237076740733747926427 19900855615111100621889641)
      ·
        refine ⟨14925641711333325466417231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19900855615111100621889641 14925641711333325466417231)
        ·
          refine ⟨22388462566999988199625847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14925641711333325466417231 22388462566999988199625847)
          ·
            refine ⟨33582693850499982299438771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22388462566999988199625847 33582693850499982299438771)
            ·
              refine ⟨50374040775749973449158157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33582693850499982299438771 50374040775749973449158157)
              ·
                refine ⟨18890265290906240043434309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50374040775749973449158157 18890265290906240043434309)
                ·
                  refine ⟨3541924742044920008143933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18890265290906240043434309 3541924742044920008143933)
                  ·
                    refine ⟨1328221778266845003053975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541924742044920008143933 1328221778266845003053975)
                    ·
                      rfl

theorem cell22_3880054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_3880054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880054 prefixEnd_3880054 := by exact prefixLift 3880054
  have htrace : WordTrace (prefixWord ++ tailWord_3880054) baseStart_3880054 baseEnd_3880054 := by
    simpa [prefixWord, tailWord_3880054, baseEnd_3880054] using wordTrace_append hprefix tailTrace_3880054
  have hstable : (prefixWord ++ tailWord_3880054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880054).length < 2 ^ (prefixWord ++ tailWord_3880054).sum := by decide
  have hdescent : baseEnd_3880054 < baseStart_3880054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880062 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3880062 : Nat := 118140960795 + 3880062 * 2 ^ 59
def prefixEnd_3880062 : Nat := 4983230072969 + 3 ^ 40 * 3880062 * 2
def baseEnd_3880062 : Nat := 442741505610111882951317

theorem tailTrace_3880062 : CollatzResearch.WordTrace tailWord_3880062 prefixEnd_3880062 442741505610111882951317 := by
  unfold tailWord_3880062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689685908650688834688305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94344991512803673785004293 17689685908650688834688305)
  ·
    refine ⟨13267264431488016626016229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17689685908650688834688305 13267264431488016626016229)
    ·
      refine ⟨2487612080904003117378043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13267264431488016626016229 2487612080904003117378043)
      ·
        refine ⟨3731418121356004676067065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487612080904003117378043 3731418121356004676067065)
        ·
          refine ⟨2798563591017003507050299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731418121356004676067065 2798563591017003507050299)
          ·
            refine ⟨4197845386525505260575449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798563591017003507050299 4197845386525505260575449)
            ·
              refine ⟨3148384039894128945431587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197845386525505260575449 3148384039894128945431587)
              ·
                refine ⟨4722576059841193418147381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148384039894128945431587 4722576059841193418147381)
                ·
                  refine ⟨442741505610111882951317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4722576059841193418147381 442741505610111882951317)
                  ·
                    rfl

theorem cell22_3880062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3880062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880062 prefixEnd_3880062 := by exact prefixLift 3880062
  have htrace : WordTrace (prefixWord ++ tailWord_3880062) baseStart_3880062 baseEnd_3880062 := by
    simpa [prefixWord, tailWord_3880062, baseEnd_3880062] using wordTrace_append hprefix tailTrace_3880062
  have hstable : (prefixWord ++ tailWord_3880062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880062).length < 2 ^ (prefixWord ++ tailWord_3880062).sum := by decide
  have hdescent : baseEnd_3880062 < baseStart_3880062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880080 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_3880080 : Nat := 118140960795 + 3880080 * 2 ^ 59
def prefixEnd_3880080 : Nat := 4983230072969 + 3 ^ 40 * 3880080 * 2
def baseEnd_3880080 : Nat := 1328230678598189601903895

theorem tailTrace_3880080 : CollatzResearch.WordTrace tailWord_3880080 prefixEnd_3880080 1328230678598189601903895 := by
  unfold tailWord_3880080
  simp only [CollatzResearch.WordTrace]
  refine ⟨70759071891570149875830847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94345429188760199834441129 70759071891570149875830847)
  ·
    refine ⟨106138607837355224813746271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70759071891570149875830847 106138607837355224813746271)
    ·
      refine ⟨159207911756032837220619407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106138607837355224813746271 159207911756032837220619407)
      ·
        refine ⟨238811867634049255830929111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159207911756032837220619407 238811867634049255830929111)
        ·
          refine ⟨358217801451073883746393667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238811867634049255830929111 358217801451073883746393667)
          ·
            refine ⟨537326702176610825619590501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358217801451073883746393667 537326702176610825619590501)
            ·
              refine ⟨100748756658114529803673219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 537326702176610825619590501 100748756658114529803673219)
              ·
                refine ⟨151123134987171794705509829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100748756658114529803673219 151123134987171794705509829)
                ·
                  refine ⟨28335587810094711507283093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151123134987171794705509829 28335587810094711507283093)
                  ·
                    refine ⟨1328230678598189601903895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28335587810094711507283093 1328230678598189601903895)
                    ·
                      rfl

theorem cell22_3880080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_3880080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880080 prefixEnd_3880080 := by exact prefixLift 3880080
  have htrace : WordTrace (prefixWord ++ tailWord_3880080) baseStart_3880080 baseEnd_3880080 := by
    simpa [prefixWord, tailWord_3880080, baseEnd_3880080] using wordTrace_append hprefix tailTrace_3880080
  have hstable : (prefixWord ++ tailWord_3880080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880080).length < 2 ^ (prefixWord ++ tailWord_3880080).sum := by decide
  have hdescent : baseEnd_3880080 < baseStart_3880080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880118 : List Nat := [5, 1, 3, 2, 1, 2, 1, 7]
def baseStart_3880118 : Nat := 118140960795 + 3880118 * 2 ^ 59
def prefixEnd_3880118 : Nat := 4983230072969 + 3 ^ 40 * 3880118 * 2
def baseEnd_3880118 : Nat := 147582631863863352161531

theorem tailTrace_3880118 : CollatzResearch.WordTrace tailWord_3880118 prefixEnd_3880118 147582631863863352161531 := by
  unfold tailWord_3880118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844970609812664515096563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94346353171335088161030005 8844970609812664515096563)
  ·
    refine ⟨13267455914718996772644845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844970609812664515096563 13267455914718996772644845)
    ·
      refine ⟨4975295968019623789741817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13267455914718996772644845 4975295968019623789741817)
      ·
        refine ⟨3731471976014717842306363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4975295968019623789741817 3731471976014717842306363)
        ·
          refine ⟨5597207964022076763459545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731471976014717842306363 5597207964022076763459545)
          ·
            refine ⟨4197905973016557572594659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5597207964022076763459545 4197905973016557572594659)
            ·
              refine ⟨6296858959524836358891989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197905973016557572594659 6296858959524836358891989)
              ·
                refine ⟨147582631863863352161531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6296858959524836358891989 147582631863863352161531)
                ·
                  rfl

theorem cell22_3880118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_3880118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880118 prefixEnd_3880118 := by exact prefixLift 3880118
  have htrace : WordTrace (prefixWord ++ tailWord_3880118) baseStart_3880118 baseEnd_3880118 := by
    simpa [prefixWord, tailWord_3880118, baseEnd_3880118] using wordTrace_append hprefix tailTrace_3880118
  have hstable : (prefixWord ++ tailWord_3880118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880118).length < 2 ^ (prefixWord ++ tailWord_3880118).sum := by decide
  have hdescent : baseEnd_3880118 < baseStart_3880118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880221 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3880221 : Nat := 118140960795 + 3880221 * 2 ^ 59
def prefixEnd_3880221 : Nat := 4983230072969 + 3 ^ 40 * 3880221 * 2
def baseEnd_3880221 : Nat := 1328278945779712234128463

theorem tailTrace_3880221 : CollatzResearch.WordTrace tailWord_3880221 prefixEnd_3880221 1328278945779712234128463 := by
  unfold tailWord_3880221
  simp only [CollatzResearch.WordTrace]
  refine ⟨141523286475629480832544517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94348857650419653888363011 141523286475629480832544517)
  ·
    refine ⟨26535616214180527656102097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141523286475629480832544517 26535616214180527656102097)
    ·
      refine ⟨19901712160635395742076573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26535616214180527656102097 19901712160635395742076573)
      ·
        refine ⟨7463142060238273403278715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19901712160635395742076573 7463142060238273403278715)
        ·
          refine ⟨11194713090357410104918073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7463142060238273403278715 11194713090357410104918073)
          ·
            refine ⟨8396034817768057578688555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11194713090357410104918073 8396034817768057578688555)
            ·
              refine ⟨12594052226652086368032833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396034817768057578688555 12594052226652086368032833)
              ·
                refine ⟨9445539169989064776024625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12594052226652086368032833 9445539169989064776024625)
                ·
                  refine ⟨7084154377491798582018469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9445539169989064776024625 7084154377491798582018469)
                  ·
                    refine ⟨1328278945779712234128463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084154377491798582018469 1328278945779712234128463)
                    ·
                      rfl

theorem cell22_3880221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3880221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880221 prefixEnd_3880221 := by exact prefixLift 3880221
  have htrace : WordTrace (prefixWord ++ tailWord_3880221) baseStart_3880221 baseEnd_3880221 := by
    simpa [prefixWord, tailWord_3880221, baseEnd_3880221] using wordTrace_append hprefix tailTrace_3880221
  have hstable : (prefixWord ++ tailWord_3880221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880221).length < 2 ^ (prefixWord ++ tailWord_3880221).sum := by decide
  have hdescent : baseEnd_3880221 < baseStart_3880221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880296 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3880296 : Nat := 118140960795 + 3880296 * 2 ^ 59
def prefixEnd_3880296 : Nat := 4983230072969 + 3 ^ 40 * 3880296 * 2
def baseEnd_3880296 : Nat := 1328304619812437038503233

theorem tailTrace_3880296 : CollatzResearch.WordTrace tailWord_3880296 prefixEnd_3880296 1328304619812437038503233 := by
  unfold tailWord_3880296
  simp only [CollatzResearch.WordTrace]
  refine ⟨70763010975178884320762371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94350681300238512427683161 70763010975178884320762371)
  ·
    refine ⟨106144516462768326481143557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70763010975178884320762371 106144516462768326481143557)
    ·
      refine ⟨19902096836769061215214417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106144516462768326481143557 19902096836769061215214417)
      ·
        refine ⟨14926572627576795911410813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19902096836769061215214417 14926572627576795911410813)
        ·
          refine ⟨5597464735341298466779055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14926572627576795911410813 5597464735341298466779055)
          ·
            refine ⟨8396197103011947700168583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597464735341298466779055 8396197103011947700168583)
            ·
              refine ⟨12594295654517921550252875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396197103011947700168583 12594295654517921550252875)
              ·
                refine ⟨18891443481776882325379313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594295654517921550252875 18891443481776882325379313)
                ·
                  refine ⟨14168582611332661744034485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18891443481776882325379313 14168582611332661744034485)
                  ·
                    refine ⟨1328304619812437038503233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14168582611332661744034485 1328304619812437038503233)
                    ·
                      rfl

theorem cell22_3880296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3880296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880296 prefixEnd_3880296 := by exact prefixLift 3880296
  have htrace : WordTrace (prefixWord ++ tailWord_3880296) baseStart_3880296 baseEnd_3880296 := by
    simpa [prefixWord, tailWord_3880296, baseEnd_3880296] using wordTrace_append hprefix tailTrace_3880296
  have hstable : (prefixWord ++ tailWord_3880296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880296).length < 2 ^ (prefixWord ++ tailWord_3880296).sum := by decide
  have hdescent : baseEnd_3880296 < baseStart_3880296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880328 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 1, 4]
def baseStart_3880328 : Nat := 118140960795 + 3880328 * 2 ^ 59
def prefixEnd_3880328 : Nat := 4983230072969 + 3 ^ 40 * 3880328 * 2
def baseEnd_3880328 : Nat := 1328315574066399621703135

theorem tailTrace_3880328 : CollatzResearch.WordTrace tailWord_3880328 prefixEnd_3880328 1328315574066399621703135 := by
  unfold tailWord_3880328
  simp only [CollatzResearch.WordTrace]
  refine ⟨70763594543120919053344819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94351459390827892071126425 70763594543120919053344819)
  ·
    refine ⟨106145391814681378580017229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70763594543120919053344819 106145391814681378580017229)
    ·
      refine ⟨39804521930505516967506461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106145391814681378580017229 39804521930505516967506461)
      ·
        refine ⟨14926695723939568862814923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39804521930505516967506461 14926695723939568862814923)
        ·
          refine ⟨22390043585909353294222385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14926695723939568862814923 22390043585909353294222385)
          ·
            refine ⟨16792532689432014970666789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22390043585909353294222385 16792532689432014970666789)
            ·
              refine ⟨3148599879268502807000023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16792532689432014970666789 3148599879268502807000023)
              ·
                refine ⟨4722899818902754210500035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148599879268502807000023 4722899818902754210500035)
                ·
                  refine ⟨7084349728354131315750053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722899818902754210500035 7084349728354131315750053)
                  ·
                    refine ⟨1328315574066399621703135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084349728354131315750053 1328315574066399621703135)
                    ·
                      rfl

theorem cell22_3880328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_3880328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880328 prefixEnd_3880328 := by exact prefixLift 3880328
  have htrace : WordTrace (prefixWord ++ tailWord_3880328) baseStart_3880328 baseEnd_3880328 := by
    simpa [prefixWord, tailWord_3880328, baseEnd_3880328] using wordTrace_append hprefix tailTrace_3880328
  have hstable : (prefixWord ++ tailWord_3880328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880328).length < 2 ^ (prefixWord ++ tailWord_3880328).sum := by decide
  have hdescent : baseEnd_3880328 < baseStart_3880328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880369 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_3880369 : Nat := 118140960795 + 3880369 * 2 ^ 59
def prefixEnd_3880369 : Nat := 4983230072969 + 3 ^ 40 * 3880369 * 2
def baseEnd_3880369 : Nat := 1328329609204289181428009

theorem tailTrace_3880369 : CollatzResearch.WordTrace tailWord_3880369 prefixEnd_3880369 1328329609204289181428009 := by
  unfold tailWord_3880369
  simp only [CollatzResearch.WordTrace]
  refine ⟨141528684479093302108932161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94352456319395534739288107 141528684479093302108932161)
  ·
    refine ⟨106146513359319976581699121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141528684479093302108932161 106146513359319976581699121)
    ·
      refine ⟨79609885019489982436274341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106146513359319976581699121 79609885019489982436274341)
      ·
        refine ⟨14926853441154371706801439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79609885019489982436274341 14926853441154371706801439)
        ·
          refine ⟨22390280161731557560202159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14926853441154371706801439 22390280161731557560202159)
          ·
            refine ⟨33585420242597336340303239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22390280161731557560202159 33585420242597336340303239)
            ·
              refine ⟨50378130363896004510454859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33585420242597336340303239 50378130363896004510454859)
              ·
                refine ⟨75567195545844006765682289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50378130363896004510454859 75567195545844006765682289)
                ·
                  refine ⟨56675396659383005074261717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75567195545844006765682289 56675396659383005074261717)
                  ·
                    refine ⟨1328329609204289181428009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56675396659383005074261717 1328329609204289181428009)
                    ·
                      rfl

theorem cell22_3880369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_3880369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880369 prefixEnd_3880369 := by exact prefixLift 3880369
  have htrace : WordTrace (prefixWord ++ tailWord_3880369) baseStart_3880369 baseEnd_3880369 := by
    simpa [prefixWord, tailWord_3880369, baseEnd_3880369] using wordTrace_append hprefix tailTrace_3880369
  have hstable : (prefixWord ++ tailWord_3880369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880369).length < 2 ^ (prefixWord ++ tailWord_3880369).sum := by decide
  have hdescent : baseEnd_3880369 < baseStart_3880369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880399 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 7]
def baseStart_3880399 : Nat := 118140960795 + 3880399 * 2 ^ 59
def prefixEnd_3880399 : Nat := 4983230072969 + 3 ^ 40 * 3880399 * 2
def baseEnd_3880399 : Nat := 442779959605793034392639

theorem tailTrace_3880399 : CollatzResearch.WordTrace tailWord_3880399 prefixEnd_3880399 442779959605793034392639 := by
  unfold tailWord_3880399
  simp only [CollatzResearch.WordTrace]
  refine ⟨141529778668984617232524251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94353185779323078155016167 141529778668984617232524251)
  ·
    refine ⟨212294668003476925848786377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141529778668984617232524251 212294668003476925848786377)
    ·
      refine ⟨159221001002607694386589783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212294668003476925848786377 159221001002607694386589783)
      ·
        refine ⟨238831501503911541579884675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159221001002607694386589783 238831501503911541579884675)
        ·
          refine ⟨358247252255867312369827013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238831501503911541579884675 358247252255867312369827013)
          ·
            refine ⟨67171359797975121069342565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358247252255867312369827013 67171359797975121069342565)
            ·
              refine ⟨12594629962120335200501731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67171359797975121069342565 12594629962120335200501731)
              ·
                refine ⟨18891944943180502800752597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594629962120335200501731 18891944943180502800752597)
                ·
                  refine ⟨442779959605793034392639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18891944943180502800752597 442779959605793034392639)
                  ·
                    rfl

theorem cell22_3880399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 7].length) (baseStart_3880399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880399 prefixEnd_3880399 := by exact prefixLift 3880399
  have htrace : WordTrace (prefixWord ++ tailWord_3880399) baseStart_3880399 baseEnd_3880399 := by
    simpa [prefixWord, tailWord_3880399, baseEnd_3880399] using wordTrace_append hprefix tailTrace_3880399
  have hstable : (prefixWord ++ tailWord_3880399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880399).length < 2 ^ (prefixWord ++ tailWord_3880399).sum := by decide
  have hdescent : baseEnd_3880399 < baseStart_3880399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880450 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3880450 : Nat := 118140960795 + 3880450 * 2 ^ 59
def prefixEnd_3880450 : Nat := 4983230072969 + 3 ^ 40 * 3880450 * 2
def baseEnd_3880450 : Nat := 442785779053210656717587

theorem tailTrace_3880450 : CollatzResearch.WordTrace tailWord_3880450 prefixEnd_3880450 442785779053210656717587 := by
  unfold tailWord_3880450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35382909697949963235657701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94354425861199901961753869 35382909697949963235657701)
  ·
    refine ⟨6634295568365618106685819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35382909697949963235657701 6634295568365618106685819)
    ·
      refine ⟨9951443352548427160028729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6634295568365618106685819 9951443352548427160028729)
      ·
        refine ⟨7463582514411320370021547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9951443352548427160028729 7463582514411320370021547)
        ·
          refine ⟨11195373771616980555032321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7463582514411320370021547 11195373771616980555032321)
          ·
            refine ⟨8396530328712735416274241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11195373771616980555032321 8396530328712735416274241)
            ·
              refine ⟨6297397746534551562205681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8396530328712735416274241 6297397746534551562205681)
              ·
                refine ⟨4723048309900913671654261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6297397746534551562205681 4723048309900913671654261)
                ·
                  refine ⟨442785779053210656717587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723048309900913671654261 442785779053210656717587)
                  ·
                    rfl

theorem cell22_3880450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3880450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880450 prefixEnd_3880450 := by exact prefixLift 3880450
  have htrace : WordTrace (prefixWord ++ tailWord_3880450) baseStart_3880450 baseEnd_3880450 := by
    simpa [prefixWord, tailWord_3880450, baseEnd_3880450] using wordTrace_append hprefix tailTrace_3880450
  have hstable : (prefixWord ++ tailWord_3880450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880450).length < 2 ^ (prefixWord ++ tailWord_3880450).sum := by decide
  have hdescent : baseEnd_3880450 < baseStart_3880450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880540 : List Nat := [2, 2, 4, 1, 2, 3, 2, 6]
def baseStart_3880540 : Nat := 118140960795 + 3880540 * 2 ^ 59
def prefixEnd_3880540 : Nat := 4983230072969 + 3 ^ 40 * 3880540 * 2
def baseEnd_3880540 : Nat := 147598682888766859489165

theorem tailTrace_3880540 : CollatzResearch.WordTrace tailWord_3880540 prefixEnd_3880540 147598682888766859489165 := by
  unfold tailWord_3880540
  simp only [CollatzResearch.WordTrace]
  refine ⟨70767460680736899156703537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94356614240982532208938049 70767460680736899156703537)
  ·
    refine ⟨53075595510552674367527653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70767460680736899156703537 53075595510552674367527653)
    ·
      refine ⟨9951674158228626443911435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53075595510552674367527653 9951674158228626443911435)
      ·
        refine ⟨14927511237342939665867153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951674158228626443911435 14927511237342939665867153)
        ·
          refine ⟨11195633428007204749400365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14927511237342939665867153 11195633428007204749400365)
          ·
            refine ⟨4198362535502701781025137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11195633428007204749400365 4198362535502701781025137)
            ·
              refine ⟨3148771901627026335768853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198362535502701781025137 3148771901627026335768853)
              ·
                refine ⟨147598682888766859489165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3148771901627026335768853 147598682888766859489165)
                ·
                  rfl

theorem cell22_3880540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 6].length) (baseStart_3880540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880540 prefixEnd_3880540 := by exact prefixLift 3880540
  have htrace : WordTrace (prefixWord ++ tailWord_3880540) baseStart_3880540 baseEnd_3880540 := by
    simpa [prefixWord, tailWord_3880540, baseEnd_3880540] using wordTrace_append hprefix tailTrace_3880540
  have hstable : (prefixWord ++ tailWord_3880540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880540).length < 2 ^ (prefixWord ++ tailWord_3880540).sum := by decide
  have hdescent : baseEnd_3880540 < baseStart_3880540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880551 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 7]
def baseStart_3880551 : Nat := 118140960795 + 3880551 * 2 ^ 59
def prefixEnd_3880551 : Nat := 4983230072969 + 3 ^ 40 * 3880551 * 2
def baseEnd_3880551 : Nat := 442797303841233791125817

theorem tailTrace_3880551 : CollatzResearch.WordTrace tailWord_3880551 prefixEnd_3880551 442797303841233791125817 := by
  unfold tailWord_3880551
  simp only [CollatzResearch.WordTrace]
  refine ⟨141535322564433947192057507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94356881709622631461371671 141535322564433947192057507)
  ·
    refine ⟨212302983846650920788086261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141535322564433947192057507 212302983846650920788086261)
    ·
      refine ⟨19903404735623523823883087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212302983846650920788086261 19903404735623523823883087)
      ·
        refine ⟨29855107103435285735824631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19903404735623523823883087 29855107103435285735824631)
        ·
          refine ⟨44782660655152928603736947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29855107103435285735824631 44782660655152928603736947)
          ·
            refine ⟨67173990982729392905605421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44782660655152928603736947 67173990982729392905605421)
            ·
              refine ⟨25190246618523522339602033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67173990982729392905605421 25190246618523522339602033)
              ·
                refine ⟨18892684963892641754701525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25190246618523522339602033 18892684963892641754701525)
                ·
                  refine ⟨442797303841233791125817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18892684963892641754701525 442797303841233791125817)
                  ·
                    rfl

theorem cell22_3880551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_3880551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880551 prefixEnd_3880551 := by exact prefixLift 3880551
  have htrace : WordTrace (prefixWord ++ tailWord_3880551) baseStart_3880551 baseEnd_3880551 := by
    simpa [prefixWord, tailWord_3880551, baseEnd_3880551] using wordTrace_append hprefix tailTrace_3880551
  have hstable : (prefixWord ++ tailWord_3880551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880551).length < 2 ^ (prefixWord ++ tailWord_3880551).sum := by decide
  have hdescent : baseEnd_3880551 < baseStart_3880551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_3880656 : Nat := 118140960795 + 3880656 * 2 ^ 59
def prefixEnd_3880656 : Nat := 4983230072969 + 3 ^ 40 * 3880656 * 2
def baseEnd_3880656 : Nat := 1328427855169516099502129

theorem tailTrace_3880656 : CollatzResearch.WordTrace tailWord_3880656 prefixEnd_3880656 1328427855169516099502129 := by
  unfold tailWord_3880656
  simp only [CollatzResearch.WordTrace]
  refine ⟨70769576114526775062314911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94359434819369033416419881 70769576114526775062314911)
  ·
    refine ⟨106154364171790162593472367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70769576114526775062314911 106154364171790162593472367)
    ·
      refine ⟨159231546257685243890208551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106154364171790162593472367 159231546257685243890208551)
      ·
        refine ⟨238847319386527865835312827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159231546257685243890208551 238847319386527865835312827)
        ·
          refine ⟨358270979079791798752969241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238847319386527865835312827 358270979079791798752969241)
          ·
            refine ⟨268703234309843849064726931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358270979079791798752969241 268703234309843849064726931)
            ·
              refine ⟨403054851464765773597090397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268703234309843849064726931 403054851464765773597090397)
              ·
                refine ⟨151145569299287165098908899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403054851464765773597090397 151145569299287165098908899)
                ·
                  refine ⟨226718353948930747648363349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151145569299287165098908899 226718353948930747648363349)
                  ·
                    refine ⟨1328427855169516099502129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 226718353948930747648363349 1328427855169516099502129)
                    ·
                      rfl

theorem cell22_3880656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_3880656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880656 prefixEnd_3880656 := by exact prefixLift 3880656
  have htrace : WordTrace (prefixWord ++ tailWord_3880656) baseStart_3880656 baseEnd_3880656 := by
    simpa [prefixWord, tailWord_3880656, baseEnd_3880656] using wordTrace_append hprefix tailTrace_3880656
  have hstable : (prefixWord ++ tailWord_3880656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880656).length < 2 ^ (prefixWord ++ tailWord_3880656).sum := by decide
  have hdescent : baseEnd_3880656 < baseStart_3880656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880660 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_3880660 : Nat := 118140960795 + 3880660 * 2 ^ 59
def prefixEnd_3880660 : Nat := 4983230072969 + 3 ^ 40 * 3880660 * 2
def baseEnd_3880660 : Nat := 1328429224451261422402117

theorem tailTrace_3880660 : CollatzResearch.WordTrace tailWord_3880660 prefixEnd_3880660 1328429224451261422402117 := by
  unfold tailWord_3880660
  simp only [CollatzResearch.WordTrace]
  refine ⟨70769649060519529403887717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94359532080692705871850289 70769649060519529403887717)
  ·
    refine ⟨13269309198847411763228947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70769649060519529403887717 13269309198847411763228947)
    ·
      refine ⟨19903963798271117644843421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13269309198847411763228947 19903963798271117644843421)
      ·
        refine ⟨7463986424351669116816283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19903963798271117644843421 7463986424351669116816283)
        ·
          refine ⟨11195979636527503675224425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7463986424351669116816283 11195979636527503675224425)
          ·
            refine ⟨8396984727395627756418319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11195979636527503675224425 8396984727395627756418319)
            ·
              refine ⟨12595477091093441634627479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396984727395627756418319 12595477091093441634627479)
              ·
                refine ⟨18893215636640162451941219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12595477091093441634627479 18893215636640162451941219)
                ·
                  refine ⟨28339823454960243677911829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18893215636640162451941219 28339823454960243677911829)
                  ·
                    refine ⟨1328429224451261422402117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28339823454960243677911829 1328429224451261422402117)
                    ·
                      rfl

theorem cell22_3880660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_3880660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880660 prefixEnd_3880660 := by exact prefixLift 3880660
  have htrace : WordTrace (prefixWord ++ tailWord_3880660) baseStart_3880660 baseEnd_3880660 := by
    simpa [prefixWord, tailWord_3880660, baseEnd_3880660] using wordTrace_append hprefix tailTrace_3880660
  have hstable : (prefixWord ++ tailWord_3880660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880660).length < 2 ^ (prefixWord ++ tailWord_3880660).sum := by decide
  have hdescent : baseEnd_3880660 < baseStart_3880660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880703 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 5]
def baseStart_3880703 : Nat := 118140960795 + 3880703 * 2 ^ 59
def prefixEnd_3880703 : Nat := 4983230072969 + 3 ^ 40 * 3880703 * 2
def baseEnd_3880703 : Nat := 442814648076674547858995

theorem tailTrace_3880703 : CollatzResearch.WordTrace tailWord_3880703 prefixEnd_3880703 442814648076674547858995 := by
  unfold tailWord_3880703
  simp only [CollatzResearch.WordTrace]
  refine ⟨141540866459883277151590763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94360577639922184767727175 141540866459883277151590763)
  ·
    refine ⟨212311299689824915727386145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141540866459883277151590763 212311299689824915727386145)
    ·
      refine ⟨159233474767368686795539609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212311299689824915727386145 159233474767368686795539609)
      ·
        refine ⟨119425106075526515096654707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159233474767368686795539609 119425106075526515096654707)
        ·
          refine ⟨179137659113289772644982061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119425106075526515096654707 179137659113289772644982061)
          ·
            refine ⟨67176622167483664741868273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179137659113289772644982061 67176622167483664741868273)
            ·
              refine ⟨50382466625612748556401205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67176622167483664741868273 50382466625612748556401205)
              ·
                refine ⟨4723356246151195177162613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50382466625612748556401205 4723356246151195177162613)
                ·
                  refine ⟨442814648076674547858995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723356246151195177162613 442814648076674547858995)
                  ·
                    rfl

theorem cell22_3880703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 5].length) (baseStart_3880703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880703 prefixEnd_3880703 := by exact prefixLift 3880703
  have htrace : WordTrace (prefixWord ++ tailWord_3880703) baseStart_3880703 baseEnd_3880703 := by
    simpa [prefixWord, tailWord_3880703, baseEnd_3880703] using wordTrace_append hprefix tailTrace_3880703
  have hstable : (prefixWord ++ tailWord_3880703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880703).length < 2 ^ (prefixWord ++ tailWord_3880703).sum := by decide
  have hdescent : baseEnd_3880703 < baseStart_3880703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880718 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_3880718 : Nat := 118140960795 + 3880718 * 2 ^ 59
def prefixEnd_3880718 : Nat := 4983230072969 + 3 ^ 40 * 3880718 * 2
def baseEnd_3880718 : Nat := 1328449079036568604451939

theorem tailTrace_3880718 : CollatzResearch.WordTrace tailWord_3880718 prefixEnd_3880718 1328449079036568604451939 := by
  unfold tailWord_3880718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692676694353616839173351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94360942369885956475591205 17692676694353616839173351)
  ·
    refine ⟨26539015041530425258760027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692676694353616839173351 26539015041530425258760027)
    ·
      refine ⟨39808522562295637888140041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26539015041530425258760027 39808522562295637888140041)
      ·
        refine ⟨29856391921721728416105031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39808522562295637888140041 29856391921721728416105031)
        ·
          refine ⟨44784587882582592624157547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29856391921721728416105031 44784587882582592624157547)
          ·
            refine ⟨67176881823873888936236321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44784587882582592624157547 67176881823873888936236321)
            ·
              refine ⟨50382661367905416702177241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67176881823873888936236321 50382661367905416702177241)
              ·
                refine ⟨37786996025929062526632931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50382661367905416702177241 37786996025929062526632931)
                ·
                  refine ⟨56680494038893593789949397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37786996025929062526632931 56680494038893593789949397)
                  ·
                    refine ⟨1328449079036568604451939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56680494038893593789949397 1328449079036568604451939)
                    ·
                      rfl

theorem cell22_3880718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_3880718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880718 prefixEnd_3880718 := by exact prefixLift 3880718
  have htrace : WordTrace (prefixWord ++ tailWord_3880718) baseStart_3880718 baseEnd_3880718 := by
    simpa [prefixWord, tailWord_3880718, baseEnd_3880718] using wordTrace_append hprefix tailTrace_3880718
  have hstable : (prefixWord ++ tailWord_3880718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880718).length < 2 ^ (prefixWord ++ tailWord_3880718).sum := by decide
  have hdescent : baseEnd_3880718 < baseStart_3880718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880799 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 4]
def baseStart_3880799 : Nat := 118140960795 + 3880799 * 2 ^ 59
def prefixEnd_3880799 : Nat := 4983230072969 + 3 ^ 40 * 3880799 * 2
def baseEnd_3880799 : Nat := 442825602330637131058897

theorem tailTrace_3880799 : CollatzResearch.WordTrace tailWord_3880799 prefixEnd_3880799 442825602330637131058897 := by
  unfold tailWord_3880799
  simp only [CollatzResearch.WordTrace]
  refine ⟨141544367867535485547085451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94362911911690323698056967 141544367867535485547085451)
  ·
    refine ⟨212316551801303228320628177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141544367867535485547085451 212316551801303228320628177)
    ·
      refine ⟨159237413850977421240471133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212316551801303228320628177 159237413850977421240471133)
      ·
        refine ⟨59714030194116532965176675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159237413850977421240471133 59714030194116532965176675)
        ·
          refine ⟨89571045291174799447765013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59714030194116532965176675 89571045291174799447765013)
          ·
            refine ⟨4198642748023818724113985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89571045291174799447765013 4198642748023818724113985)
            ·
              refine ⟨3148982061017864043085489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198642748023818724113985 3148982061017864043085489)
              ·
                refine ⟨2361736545763398032314117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148982061017864043085489 2361736545763398032314117)
                ·
                  refine ⟨442825602330637131058897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361736545763398032314117 442825602330637131058897)
                  ·
                    rfl

theorem cell22_3880799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 4].length) (baseStart_3880799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880799 prefixEnd_3880799 := by exact prefixLift 3880799
  have htrace : WordTrace (prefixWord ++ tailWord_3880799) baseStart_3880799 baseEnd_3880799 := by
    simpa [prefixWord, tailWord_3880799, baseEnd_3880799] using wordTrace_append hprefix tailTrace_3880799
  have hstable : (prefixWord ++ tailWord_3880799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880799).length < 2 ^ (prefixWord ++ tailWord_3880799).sum := by decide
  have hdescent : baseEnd_3880799 < baseStart_3880799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880814 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_3880814 : Nat := 118140960795 + 3880814 * 2 ^ 59
def prefixEnd_3880814 : Nat := 4983230072969 + 3 ^ 40 * 3880814 * 2
def baseEnd_3880814 : Nat := 1328481941798456354051645

theorem tailTrace_3880814 : CollatzResearch.WordTrace tailWord_3880814 prefixEnd_3880814 1328481941798456354051645 := by
  unfold tailWord_3880814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693114370310142888610187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94363276641654095405920997 17693114370310142888610187)
  ·
    refine ⟨26539671555465214332915281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17693114370310142888610187 26539671555465214332915281)
    ·
      refine ⟨19904753666598910749686461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26539671555465214332915281 19904753666598910749686461)
      ·
        refine ⟨7464282624974591531132423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19904753666598910749686461 7464282624974591531132423)
        ·
          refine ⟨11196423937461887296698635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464282624974591531132423 11196423937461887296698635)
          ·
            refine ⟨16794635906192830945047953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196423937461887296698635 16794635906192830945047953)
            ·
              refine ⟨12595976929644623208785965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16794635906192830945047953 12595976929644623208785965)
              ·
                refine ⟨4723491348616733703294737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12595976929644623208785965 4723491348616733703294737)
                ·
                  refine ⟨3542618511462550277471053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723491348616733703294737 3542618511462550277471053)
                  ·
                    refine ⟨1328481941798456354051645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3542618511462550277471053 1328481941798456354051645)
                    ·
                      rfl

theorem cell22_3880814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_3880814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880814 prefixEnd_3880814 := by exact prefixLift 3880814
  have htrace : WordTrace (prefixWord ++ tailWord_3880814) baseStart_3880814 baseEnd_3880814 := by
    simpa [prefixWord, tailWord_3880814, baseEnd_3880814] using wordTrace_append hprefix tailTrace_3880814
  have hstable : (prefixWord ++ tailWord_3880814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880814).length < 2 ^ (prefixWord ++ tailWord_3880814).sum := by decide
  have hdescent : baseEnd_3880814 < baseStart_3880814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880855 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 7]
def baseStart_3880855 : Nat := 118140960795 + 3880855 * 2 ^ 59
def prefixEnd_3880855 : Nat := 4983230072969 + 3 ^ 40 * 3880855 * 2
def baseEnd_3880855 : Nat := 442831992312115304592173

theorem tailTrace_3880855 : CollatzResearch.WordTrace tailWord_3880855 prefixEnd_3880855 442831992312115304592173 := by
  unfold tailWord_3880855
  simp only [CollatzResearch.WordTrace]
  refine ⟨141546410355332607111124019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94364273570221738074082679 141546410355332607111124019)
  ·
    refine ⟨212319615532998910666686029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141546410355332607111124019 212319615532998910666686029)
    ·
      refine ⟨79619855824874591500007261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212319615532998910666686029 79619855824874591500007261)
      ·
        refine ⟨29857445934327971812502723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79619855824874591500007261 29857445934327971812502723)
        ·
          refine ⟨44786168901491957718754085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29857445934327971812502723 44786168901491957718754085)
          ·
            refine ⟨8397406669029742072266391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44786168901491957718754085 8397406669029742072266391)
            ·
              refine ⟨12596110003544613108399587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397406669029742072266391 12596110003544613108399587)
              ·
                refine ⟨18894165005316919662599381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596110003544613108399587 18894165005316919662599381)
                ·
                  refine ⟨442831992312115304592173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18894165005316919662599381 442831992312115304592173)
                  ·
                    rfl

theorem cell22_3880855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 7].length) (baseStart_3880855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880855 prefixEnd_3880855 := by exact prefixLift 3880855
  have htrace : WordTrace (prefixWord ++ tailWord_3880855) baseStart_3880855 baseEnd_3880855 := by
    simpa [prefixWord, tailWord_3880855, baseEnd_3880855] using wordTrace_append hprefix tailTrace_3880855
  have hstable : (prefixWord ++ tailWord_3880855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880855).length < 2 ^ (prefixWord ++ tailWord_3880855).sum := by decide
  have hdescent : baseEnd_3880855 < baseStart_3880855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880878 : List Nat := [4, 1, 5, 1, 1, 2, 2, 6]
def baseStart_3880878 : Nat := 118140960795 + 3880878 * 2 ^ 59
def prefixEnd_3880878 : Nat := 4983230072969 + 3 ^ 40 * 3880878 * 2
def baseEnd_3880878 : Nat := 147611538922931280050161

theorem tailTrace_3880878 : CollatzResearch.WordTrace tailWord_3880878 prefixEnd_3880878 147611538922931280050161 := by
  unfold tailWord_3880878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693406154281160254901411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94364832822832854692807525 17693406154281160254901411)
  ·
    refine ⟨26540109231421740382352117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17693406154281160254901411 26540109231421740382352117)
    ·
      refine ⟨2488135240445788160845511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26540109231421740382352117 2488135240445788160845511)
      ·
        refine ⟨3732202860668682241268267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488135240445788160845511 3732202860668682241268267)
        ·
          refine ⟨5598304291003023361902401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732202860668682241268267 5598304291003023361902401)
          ·
            refine ⟨4198728218252267521426801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598304291003023361902401 4198728218252267521426801)
            ·
              refine ⟨3149046163689200641070101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198728218252267521426801 3149046163689200641070101)
              ·
                refine ⟨147611538922931280050161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3149046163689200641070101 147611538922931280050161)
                ·
                  rfl

theorem cell22_3880878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_3880878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880878 prefixEnd_3880878 := by exact prefixLift 3880878
  have htrace : WordTrace (prefixWord ++ tailWord_3880878) baseStart_3880878 baseEnd_3880878 := by
    simpa [prefixWord, tailWord_3880878, baseEnd_3880878] using wordTrace_append hprefix tailTrace_3880878
  have hstable : (prefixWord ++ tailWord_3880878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880878).length < 2 ^ (prefixWord ++ tailWord_3880878).sum := by decide
  have hdescent : baseEnd_3880878 < baseStart_3880878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880917 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 6]
def baseStart_3880917 : Nat := 118140960795 + 3880917 * 2 ^ 59
def prefixEnd_3880917 : Nat := 4983230072969 + 3 ^ 40 * 3880917 * 2
def baseEnd_3880917 : Nat := 442839066934466139575443

theorem tailTrace_3880917 : CollatzResearch.WordTrace tailWord_3880917 prefixEnd_3880917 442839066934466139575443 := by
  unfold tailWord_3880917
  simp only [CollatzResearch.WordTrace]
  refine ⟨141548671681107991699881005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94365781120738661133254003 141548671681107991699881005)
  ·
    refine ⟨53080751880415496887455377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141548671681107991699881005 53080751880415496887455377)
    ·
      refine ⟨39810563910311622665591533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53080751880415496887455377 39810563910311622665591533)
      ·
        refine ⟨14928961466366858499596825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39810563910311622665591533 14928961466366858499596825)
        ·
          refine ⟨11196721099775143874697619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14928961466366858499596825 11196721099775143874697619)
          ·
            refine ⟨16795081649662715812046429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196721099775143874697619 16795081649662715812046429)
            ·
              refine ⟨6298155618623518429517411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16795081649662715812046429 6298155618623518429517411)
              ·
                refine ⟨9447233427935277644276117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298155618623518429517411 9447233427935277644276117)
                ·
                  refine ⟨442839066934466139575443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9447233427935277644276117 442839066934466139575443)
                  ·
                    rfl

theorem cell22_3880917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_3880917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880917 prefixEnd_3880917 := by exact prefixLift 3880917
  have htrace : WordTrace (prefixWord ++ tailWord_3880917) baseStart_3880917 baseEnd_3880917 := by
    simpa [prefixWord, tailWord_3880917, baseEnd_3880917] using wordTrace_append hprefix tailTrace_3880917
  have hstable : (prefixWord ++ tailWord_3880917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880917).length < 2 ^ (prefixWord ++ tailWord_3880917).sum := by decide
  have hdescent : baseEnd_3880917 < baseStart_3880917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880994 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3880994 : Nat := 118140960795 + 3880994 * 2 ^ 59
def prefixEnd_3880994 : Nat := 4983230072969 + 3 ^ 40 * 3880994 * 2
def baseEnd_3880994 : Nat := 1328543559476995884551093

theorem tailTrace_3880994 : CollatzResearch.WordTrace tailWord_3880994 prefixEnd_3880994 1328543559476995884551093 := by
  unfold tailWord_3880994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35387870025457258462608509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94367653401219355900289357 35387870025457258462608509)
  ·
    refine ⟨13270451259546471923478191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35387870025457258462608509 13270451259546471923478191)
    ·
      refine ⟨19905676889319707885217287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13270451259546471923478191 19905676889319707885217287)
      ·
        refine ⟨29858515333979561827825931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19905676889319707885217287 29858515333979561827825931)
        ·
          refine ⟨44787773000969342741738897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29858515333979561827825931 44787773000969342741738897)
          ·
            refine ⟨33590829750727007056304173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44787773000969342741738897 33590829750727007056304173)
            ·
              refine ⟨12596561156522627646114065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33590829750727007056304173 12596561156522627646114065)
              ·
                refine ⟨9447420867391970734585549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12596561156522627646114065 9447420867391970734585549)
                ·
                  refine ⟨3542782825271989025469581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9447420867391970734585549 3542782825271989025469581)
                  ·
                    refine ⟨1328543559476995884551093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3542782825271989025469581 1328543559476995884551093)
                    ·
                      rfl

theorem cell22_3880994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3880994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3880994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3880994 prefixEnd_3880994 := by exact prefixLift 3880994
  have htrace : WordTrace (prefixWord ++ tailWord_3880994) baseStart_3880994 baseEnd_3880994 := by
    simpa [prefixWord, tailWord_3880994, baseEnd_3880994] using wordTrace_append hprefix tailTrace_3880994
  have hstable : (prefixWord ++ tailWord_3880994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880994).length < 2 ^ (prefixWord ++ tailWord_3880994).sum := by decide
  have hdescent : baseEnd_3880994 < baseStart_3880994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881024 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 5]
def baseStart_3881024 : Nat := 118140960795 + 3881024 * 2 ^ 59
def prefixEnd_3881024 : Nat := 4983230072969 + 3 ^ 40 * 3881024 * 2
def baseEnd_3881024 : Nat := 442851276363361935433667

theorem tailTrace_3881024 : CollatzResearch.WordTrace tailWord_3881024 prefixEnd_3881024 442851276363361935433667 := by
  unfold tailWord_3881024
  simp only [CollatzResearch.WordTrace]
  refine ⟨70776287145860174487013063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94368382861146899316017417 70776287145860174487013063)
  ·
    refine ⟨106164430718790261730519595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70776287145860174487013063 106164430718790261730519595)
    ·
      refine ⟨159246646078185392595779393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106164430718790261730519595 159246646078185392595779393)
      ·
        refine ⟨119434984558639044446834545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159246646078185392595779393 119434984558639044446834545)
        ·
          refine ⟨89576238418979283335125909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119434984558639044446834545 89576238418979283335125909)
          ·
            refine ⟨4198886175889653906334027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89576238418979283335125909 4198886175889653906334027)
            ·
              refine ⟨6298329263834480859501041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198886175889653906334027 6298329263834480859501041)
              ·
                refine ⟨4723746947875860644625781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298329263834480859501041 4723746947875860644625781)
                ·
                  refine ⟨442851276363361935433667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723746947875860644625781 442851276363361935433667)
                  ·
                    rfl

theorem cell22_3881024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_3881024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881024 prefixEnd_3881024 := by exact prefixLift 3881024
  have htrace : WordTrace (prefixWord ++ tailWord_3881024) baseStart_3881024 baseEnd_3881024 := by
    simpa [prefixWord, tailWord_3881024, baseEnd_3881024] using wordTrace_append hprefix tailTrace_3881024
  have hstable : (prefixWord ++ tailWord_3881024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881024).length < 2 ^ (prefixWord ++ tailWord_3881024).sum := by decide
  have hdescent : baseEnd_3881024 < baseStart_3881024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881035 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 10]
def baseStart_3881035 : Nat := 118140960795 + 3881035 * 2 ^ 59
def prefixEnd_3881035 : Nat := 4983230072969 + 3 ^ 40 * 3881035 * 2
def baseEnd_3881035 : Nat := 442852531538295148091989

theorem tailTrace_3881035 : CollatzResearch.WordTrace tailWord_3881035 prefixEnd_3881035 442852531538295148091989 := by
  unfold tailWord_3881035
  simp only [CollatzResearch.WordTrace]
  refine ⟨141552975494680497852676559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94368650329786998568451039 141552975494680497852676559)
  ·
    refine ⟨212329463242020746779014839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141552975494680497852676559 212329463242020746779014839)
    ·
      refine ⟨318494194863031120168522259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212329463242020746779014839 318494194863031120168522259)
      ·
        refine ⟨477741292294546680252783389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318494194863031120168522259 477741292294546680252783389)
        ·
          refine ⟨179152984610455005094793771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477741292294546680252783389 179152984610455005094793771)
          ·
            refine ⟨268729476915682507642190657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179152984610455005094793771 268729476915682507642190657)
            ·
              refine ⟨201547107686761880731642993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268729476915682507642190657 201547107686761880731642993)
              ·
                refine ⟨151160330765071410548732245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201547107686761880731642993 151160330765071410548732245)
                ·
                  refine ⟨442852531538295148091989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151160330765071410548732245 442852531538295148091989)
                  ·
                    rfl

theorem cell22_3881035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_3881035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881035 prefixEnd_3881035 := by exact prefixLift 3881035
  have htrace : WordTrace (prefixWord ++ tailWord_3881035) baseStart_3881035 baseEnd_3881035 := by
    simpa [prefixWord, tailWord_3881035, baseEnd_3881035] using wordTrace_append hprefix tailTrace_3881035
  have hstable : (prefixWord ++ tailWord_3881035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881035).length < 2 ^ (prefixWord ++ tailWord_3881035).sum := by decide
  have hdescent : baseEnd_3881035 < baseStart_3881035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881084 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_3881084 : Nat := 118140960795 + 3881084 * 2 ^ 59
def prefixEnd_3881084 : Nat := 4983230072969 + 3 ^ 40 * 3881084 * 2
def baseEnd_3881084 : Nat := 1328574368316265649800817

theorem tailTrace_3881084 : CollatzResearch.WordTrace tailWord_3881084 prefixEnd_3881084 1328574368316265649800817 := by
  unfold tailWord_3881084
  simp only [CollatzResearch.WordTrace]
  refine ⟨70777381335751489610605153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94369841781001986147473537 70777381335751489610605153)
  ·
    refine ⟨53083036001813617207953865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70777381335751489610605153 53083036001813617207953865)
    ·
      refine ⟨39812277001360212905965399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53083036001813617207953865 39812277001360212905965399)
      ·
        refine ⟨59718415502040319358948099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39812277001360212905965399 59718415502040319358948099)
        ·
          refine ⟨89577623253060479038422149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59718415502040319358948099 89577623253060479038422149)
          ·
            refine ⟨16795804359948839819704153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89577623253060479038422149 16795804359948839819704153)
            ·
              refine ⟨12596853269961629864778115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16795804359948839819704153 12596853269961629864778115)
              ·
                refine ⟨18895279904942444797167173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596853269961629864778115 18895279904942444797167173)
                ·
                  refine ⟨3542864982176708399468845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18895279904942444797167173 3542864982176708399468845)
                  ·
                    refine ⟨1328574368316265649800817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3542864982176708399468845 1328574368316265649800817)
                    ·
                      rfl

theorem cell22_3881084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_3881084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881084 prefixEnd_3881084 := by exact prefixLift 3881084
  have htrace : WordTrace (prefixWord ++ tailWord_3881084) baseStart_3881084 baseEnd_3881084 := by
    simpa [prefixWord, tailWord_3881084, baseEnd_3881084] using wordTrace_append hprefix tailTrace_3881084
  have hstable : (prefixWord ++ tailWord_3881084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881084).length < 2 ^ (prefixWord ++ tailWord_3881084).sum := by decide
  have hdescent : baseEnd_3881084 < baseStart_3881084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881097 : List Nat := [1, 2, 1, 1, 4, 2, 4, 7]
def baseStart_3881097 : Nat := 118140960795 + 3881097 * 2 ^ 59
def prefixEnd_3881097 : Nat := 4983230072969 + 3 ^ 40 * 3881097 * 2
def baseEnd_3881097 : Nat := 147619868720215327691753

theorem tailTrace_3881097 : CollatzResearch.WordTrace tailWord_3881097 prefixEnd_3881097 147619868720215327691753 := by
  unfold tailWord_3881097
  simp only [CollatzResearch.WordTrace]
  refine ⟨141555236820455882441433545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94370157880303921627622363 141555236820455882441433545)
  ·
    refine ⟨106166427615341911831075159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141555236820455882441433545 106166427615341911831075159)
    ·
      refine ⟨159249641423012867746612739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106166427615341911831075159 159249641423012867746612739)
      ·
        refine ⟨238874462134519301619919109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159249641423012867746612739 238874462134519301619919109)
        ·
          refine ⟨44788961650222369053734833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238874462134519301619919109 44788961650222369053734833)
          ·
            refine ⟨33591721237666776790301125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44788961650222369053734833 33591721237666776790301125)
            ·
              refine ⟨6298447732062520648181461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33591721237666776790301125 6298447732062520648181461)
              ·
                refine ⟨147619868720215327691753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6298447732062520648181461 147619868720215327691753)
                ·
                  rfl

theorem cell22_3881097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 7].length) (baseStart_3881097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881097 prefixEnd_3881097 := by exact prefixLift 3881097
  have htrace : WordTrace (prefixWord ++ tailWord_3881097) baseStart_3881097 baseEnd_3881097 := by
    simpa [prefixWord, tailWord_3881097, baseEnd_3881097] using wordTrace_append hprefix tailTrace_3881097
  have hstable : (prefixWord ++ tailWord_3881097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881097).length < 2 ^ (prefixWord ++ tailWord_3881097).sum := by decide
  have hdescent : baseEnd_3881097 < baseStart_3881097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881157 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3881157 : Nat := 118140960795 + 3881157 * 2 ^ 59
def prefixEnd_3881157 : Nat := 4983230072969 + 3 ^ 40 * 3881157 * 2
def baseEnd_3881157 : Nat := 1328599357708117792725593

theorem tailTrace_3881157 : CollatzResearch.WordTrace tailWord_3881157 prefixEnd_3881157 1328599357708117792725593 := by
  unfold tailWord_3881157
  simp only [CollatzResearch.WordTrace]
  refine ⟨141557425200238512688617725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94371616800159008459078483 141557425200238512688617725)
  ·
    refine ⟨53084034450089442258231647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141557425200238512688617725 53084034450089442258231647)
    ·
      refine ⟨79626051675134163387347471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53084034450089442258231647 79626051675134163387347471)
      ·
        refine ⟨119439077512701245081021207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79626051675134163387347471 119439077512701245081021207)
        ·
          refine ⟨179158616269051867621531811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119439077512701245081021207 179158616269051867621531811)
          ·
            refine ⟨268737924403577801432297717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179158616269051867621531811 268737924403577801432297717)
            ·
              refine ⟨25194180412835418884277911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268737924403577801432297717 25194180412835418884277911)
              ·
                refine ⟨37791270619253128326416867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25194180412835418884277911 37791270619253128326416867)
                ·
                  refine ⟨56686905928879692489625301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37791270619253128326416867 56686905928879692489625301)
                  ·
                    refine ⟨1328599357708117792725593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56686905928879692489625301 1328599357708117792725593)
                    ·
                      rfl

theorem cell22_3881157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3881157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881157 prefixEnd_3881157 := by exact prefixLift 3881157
  have htrace : WordTrace (prefixWord ++ tailWord_3881157) baseStart_3881157 baseEnd_3881157 := by
    simpa [prefixWord, tailWord_3881157, baseEnd_3881157] using wordTrace_append hprefix tailTrace_3881157
  have hstable : (prefixWord ++ tailWord_3881157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881157).length < 2 ^ (prefixWord ++ tailWord_3881157).sum := by decide
  have hdescent : baseEnd_3881157 < baseStart_3881157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881266 : List Nat := [3, 2, 1, 1, 5, 1, 2, 7]
def baseStart_3881266 : Nat := 118140960795 + 3881266 * 2 ^ 59
def prefixEnd_3881266 : Nat := 4983230072969 + 3 ^ 40 * 3881266 * 2
def baseEnd_3881266 : Nat := 147626296737297537972251

theorem tailTrace_3881266 : CollatzResearch.WordTrace tailWord_3881266 prefixEnd_3881266 147626296737297537972251 := by
  unfold tailWord_3881266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35390350189210906076083913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94374267171229082869557101 35390350189210906076083913)
  ·
    refine ⟨26542762641908179557062935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35390350189210906076083913 26542762641908179557062935)
    ·
      refine ⟨39814143962862269335594403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26542762641908179557062935 39814143962862269335594403)
      ·
        refine ⟨59721215944293404003391605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39814143962862269335594403 59721215944293404003391605)
        ·
          refine ⟨5598863994777506625317963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59721215944293404003391605 5598863994777506625317963)
          ·
            refine ⟨8398295992166259937976945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598863994777506625317963 8398295992166259937976945)
            ·
              refine ⟨6298721994124694953482709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398295992166259937976945 6298721994124694953482709)
              ·
                refine ⟨147626296737297537972251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6298721994124694953482709 147626296737297537972251)
                ·
                  rfl

theorem cell22_3881266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_3881266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881266 prefixEnd_3881266 := by exact prefixLift 3881266
  have htrace : WordTrace (prefixWord ++ tailWord_3881266) baseStart_3881266 baseEnd_3881266 := by
    simpa [prefixWord, tailWord_3881266, baseEnd_3881266] using wordTrace_append hprefix tailTrace_3881266
  have hstable : (prefixWord ++ tailWord_3881266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881266).length < 2 ^ (prefixWord ++ tailWord_3881266).sum := by decide
  have hdescent : baseEnd_3881266 < baseStart_3881266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881294 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_3881294 : Nat := 118140960795 + 3881294 * 2 ^ 59
def prefixEnd_3881294 : Nat := 4983230072969 + 3 ^ 40 * 3881294 * 2
def baseEnd_3881294 : Nat := 442882085202631700683391

theorem tailTrace_3881294 : CollatzResearch.WordTrace tailWord_3881294 prefixEnd_3881294 442882085202631700683391 := by
  unfold tailWord_3881294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17695302750092773135794367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94374948000494790057569957 17695302750092773135794367)
  ·
    refine ⟨26542954125139159703691551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17695302750092773135794367 26542954125139159703691551)
    ·
      refine ⟨39814431187708739555537327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26542954125139159703691551 39814431187708739555537327)
      ·
        refine ⟨59721646781563109333305991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39814431187708739555537327 59721646781563109333305991)
        ·
          refine ⟨89582470172344663999958987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59721646781563109333305991 89582470172344663999958987)
          ·
            refine ⟨134373705258516995999938481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89582470172344663999958987 134373705258516995999938481)
            ·
              refine ⟨100780278943887746999953861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134373705258516995999938481 100780278943887746999953861)
              ·
                refine ⟨18896302301978952562491349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100780278943887746999953861 18896302301978952562491349)
                ·
                  refine ⟨442882085202631700683391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18896302301978952562491349 442882085202631700683391)
                  ·
                    rfl

theorem cell22_3881294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_3881294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881294 prefixEnd_3881294 := by exact prefixLift 3881294
  have htrace : WordTrace (prefixWord ++ tailWord_3881294) baseStart_3881294 baseEnd_3881294 := by
    simpa [prefixWord, tailWord_3881294, baseEnd_3881294] using wordTrace_append hprefix tailTrace_3881294
  have hstable : (prefixWord ++ tailWord_3881294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881294).length < 2 ^ (prefixWord ++ tailWord_3881294).sum := by decide
  have hdescent : baseEnd_3881294 < baseStart_3881294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881339 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 8]
def baseStart_3881339 : Nat := 118140960795 + 3881339 * 2 ^ 59
def prefixEnd_3881339 : Nat := 4983230072969 + 3 ^ 40 * 3881339 * 2
def baseEnd_3881339 : Nat := 442887220009176661558345

theorem tailTrace_3881339 : CollatzResearch.WordTrace tailWord_3881339 prefixEnd_3881339 442887220009176661558345 := by
  unfold tailWord_3881339
  simp only [CollatzResearch.WordTrace]
  refine ⟨141564063285579157771743071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94376042190386105181162047 141564063285579157771743071)
  ·
    refine ⟨212346094928368736657614607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141564063285579157771743071 212346094928368736657614607)
    ·
      refine ⟨318519142392553104986421911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212346094928368736657614607 318519142392553104986421911)
      ·
        refine ⟨477778713588829657479632867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318519142392553104986421911 477778713588829657479632867)
        ·
          refine ⟨716668070383244486219449301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477778713588829657479632867 716668070383244486219449301)
          ·
            refine ⟨16796907899607292645768343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 716668070383244486219449301 16796907899607292645768343)
            ·
              refine ⟨25195361849410938968652515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16796907899607292645768343 25195361849410938968652515)
              ·
                refine ⟨37793042774116408452978773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25195361849410938968652515 37793042774116408452978773)
                ·
                  refine ⟨442887220009176661558345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37793042774116408452978773 442887220009176661558345)
                  ·
                    rfl

theorem cell22_3881339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_3881339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881339 prefixEnd_3881339 := by exact prefixLift 3881339
  have htrace : WordTrace (prefixWord ++ tailWord_3881339) baseStart_3881339 baseEnd_3881339 := by
    simpa [prefixWord, tailWord_3881339, baseEnd_3881339] using wordTrace_append hprefix tailTrace_3881339
  have hstable : (prefixWord ++ tailWord_3881339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881339).length < 2 ^ (prefixWord ++ tailWord_3881339).sum := by decide
  have hdescent : baseEnd_3881339 < baseStart_3881339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881341 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3881341 : Nat := 118140960795 + 3881341 * 2 ^ 59
def prefixEnd_3881341 : Nat := 4983230072969 + 3 ^ 40 * 3881341 * 2
def baseEnd_3881341 : Nat := 1328662344668402646125029

theorem tailTrace_3881341 : CollatzResearch.WordTrace tailWord_3881341 prefixEnd_3881341 1328662344668402646125029 := by
  unfold tailWord_3881341
  simp only [CollatzResearch.WordTrace]
  refine ⟨141564136231571912113315877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94376090821047941408877251 141564136231571912113315877)
  ·
    refine ⟨26543275543419733521246727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141564136231571912113315877 26543275543419733521246727)
    ·
      refine ⟨39814913315129600281870091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26543275543419733521246727 39814913315129600281870091)
      ·
        refine ⟨59722369972694400422805137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39814913315129600281870091 59722369972694400422805137)
        ·
          refine ⟨44791777479520800317103853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59722369972694400422805137 44791777479520800317103853)
          ·
            refine ⟨16796916554820300118913945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44791777479520800317103853 16796916554820300118913945)
            ·
              refine ⟨12597687416115225089185459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16796916554820300118913945 12597687416115225089185459)
              ·
                refine ⟨18896531124172837633778189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12597687416115225089185459 18896531124172837633778189)
                ·
                  refine ⟨7086199171564814112666821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18896531124172837633778189 7086199171564814112666821)
                  ·
                    refine ⟨1328662344668402646125029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7086199171564814112666821 1328662344668402646125029)
                    ·
                      rfl

theorem cell22_3881341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3881341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881341 prefixEnd_3881341 := by exact prefixLift 3881341
  have htrace : WordTrace (prefixWord ++ tailWord_3881341) baseStart_3881341 baseEnd_3881341 := by
    simpa [prefixWord, tailWord_3881341, baseEnd_3881341] using wordTrace_append hprefix tailTrace_3881341
  have hstable : (prefixWord ++ tailWord_3881341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881341).length < 2 ^ (prefixWord ++ tailWord_3881341).sum := by decide
  have hdescent : baseEnd_3881341 < baseStart_3881341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881373 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3881373 : Nat := 118140960795 + 3881373 * 2 ^ 59
def prefixEnd_3881373 : Nat := 4983230072969 + 3 ^ 40 * 3881373 * 2
def baseEnd_3881373 : Nat := 442891099640788409774977

theorem tailTrace_3881373 : CollatzResearch.WordTrace tailWord_3881373 prefixEnd_3881373 442891099640788409774977 := by
  unfold tailWord_3881373
  simp only [CollatzResearch.WordTrace]
  refine ⟨141565303367455981578480773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94376868911637321052320515 141565303367455981578480773)
  ·
    refine ⟨26543494381397996545965145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141565303367455981578480773 26543494381397996545965145)
    ·
      refine ⟨19907620786048497409473859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26543494381397996545965145 19907620786048497409473859)
      ·
        refine ⟨29861431179072746114210789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19907620786048497409473859 29861431179072746114210789)
        ·
          refine ⟨5599018346076139896414523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29861431179072746114210789 5599018346076139896414523)
          ·
            refine ⟨8398527519114209844621785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599018346076139896414523 8398527519114209844621785)
            ·
              refine ⟨6298895639335657383466339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398527519114209844621785 6298895639335657383466339)
              ·
                refine ⟨9448343459003486075199509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298895639335657383466339 9448343459003486075199509)
                ·
                  refine ⟨442891099640788409774977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9448343459003486075199509 442891099640788409774977)
                  ·
                    rfl

theorem cell22_3881373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3881373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881373 prefixEnd_3881373 := by exact prefixLift 3881373
  have htrace : WordTrace (prefixWord ++ tailWord_3881373) baseStart_3881373 baseEnd_3881373 := by
    simpa [prefixWord, tailWord_3881373, baseEnd_3881373] using wordTrace_append hprefix tailTrace_3881373
  have hstable : (prefixWord ++ tailWord_3881373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881373).length < 2 ^ (prefixWord ++ tailWord_3881373).sum := by decide
  have hdescent : baseEnd_3881373 < baseStart_3881373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881401 : List Nat := [1, 2, 1, 4, 3, 2, 1, 8]
def baseStart_3881401 : Nat := 118140960795 + 3881401 * 2 ^ 59
def prefixEnd_3881401 : Nat := 4983230072969 + 3 ^ 40 * 3881401 * 2
def baseEnd_3881401 : Nat := 147631431543842498847205

theorem tailTrace_3881401 : CollatzResearch.WordTrace tailWord_3881401 prefixEnd_3881401 147631431543842498847205 := by
  unfold tailWord_3881401
  simp only [CollatzResearch.WordTrace]
  refine ⟨141566324611354542360500057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94377549740903028240333371 141566324611354542360500057)
  ·
    refine ⟨106174743458515906770375043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141566324611354542360500057 106174743458515906770375043)
    ·
      refine ⟨159262115187773860155562565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106174743458515906770375043 159262115187773860155562565)
      ·
        refine ⟨29861646597707598779167981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159262115187773860155562565 29861646597707598779167981)
        ·
          refine ⟨11198117474140349542187993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29861646597707598779167981 11198117474140349542187993)
          ·
            refine ⟨8398588105605262156640995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11198117474140349542187993 8398588105605262156640995)
            ·
              refine ⟨12597882158407893234961493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398588105605262156640995 12597882158407893234961493)
              ·
                refine ⟨147631431543842498847205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12597882158407893234961493 147631431543842498847205)
                ·
                  rfl

theorem cell22_3881401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 8].length) (baseStart_3881401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881401 prefixEnd_3881401 := by exact prefixLift 3881401
  have htrace : WordTrace (prefixWord ++ tailWord_3881401) baseStart_3881401 baseEnd_3881401 := by
    simpa [prefixWord, tailWord_3881401, baseEnd_3881401] using wordTrace_append hprefix tailTrace_3881401
  have hstable : (prefixWord ++ tailWord_3881401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881401).length < 2 ^ (prefixWord ++ tailWord_3881401).sum := by decide
  have hdescent : baseEnd_3881401 < baseStart_3881401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881484 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_3881484 : Nat := 118140960795 + 3881484 * 2 ^ 59
def prefixEnd_3881484 : Nat := 4983230072969 + 3 ^ 40 * 3881484 * 2
def baseEnd_3881484 : Nat := 1328711296490797939799591

theorem tailTrace_3881484 : CollatzResearch.WordTrace tailWord_3881484 prefixEnd_3881484 1328711296490797939799591 := by
  unfold tailWord_3881484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70784675935026923767885753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94379567913369231690514337 70784675935026923767885753)
  ·
    refine ⟨53088506951270192825914315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70784675935026923767885753 53088506951270192825914315)
    ·
      refine ⟨79632760426905289238871473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53088506951270192825914315 79632760426905289238871473)
      ·
        refine ⟨59724570320178966929153605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79632760426905289238871473 59724570320178966929153605)
        ·
          refine ⟨11198356935033556299216301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59724570320178966929153605 11198356935033556299216301)
          ·
            refine ⟨4199383850637583612206113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11198356935033556299216301 4199383850637583612206113)
            ·
              refine ⟨3149537887978187709154585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4199383850637583612206113 3149537887978187709154585)
              ·
                refine ⟨2362153415983640781865939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149537887978187709154585 2362153415983640781865939)
                ·
                  refine ⟨3543230123975461172798909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362153415983640781865939 3543230123975461172798909)
                  ·
                    refine ⟨1328711296490797939799591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543230123975461172798909 1328711296490797939799591)
                    ·
                      rfl

theorem cell22_3881484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_3881484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881484 prefixEnd_3881484 := by exact prefixLift 3881484
  have htrace : WordTrace (prefixWord ++ tailWord_3881484) baseStart_3881484 baseEnd_3881484 := by
    simpa [prefixWord, tailWord_3881484, baseEnd_3881484] using wordTrace_append hprefix tailTrace_3881484
  have hstable : (prefixWord ++ tailWord_3881484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881484).length < 2 ^ (prefixWord ++ tailWord_3881484).sum := by decide
  have hdescent : baseEnd_3881484 < baseStart_3881484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881491 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 6]
def baseStart_3881491 : Nat := 118140960795 + 3881491 * 2 ^ 59
def prefixEnd_3881491 : Nat := 4983230072969 + 3 ^ 40 * 3881491 * 2
def baseEnd_3881491 : Nat := 442904564244617418291523

theorem tailTrace_3881491 : CollatzResearch.WordTrace tailWord_3881491 prefixEnd_3881491 442904564244617418291523 := by
  unfold tailWord_3881491
  simp only [CollatzResearch.WordTrace]
  refine ⟨141569607181028487731276327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94379738120685658487517551 141569607181028487731276327)
  ·
    refine ⟨212354410771542731596914491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141569607181028487731276327 212354410771542731596914491)
    ·
      refine ⟨318531616157314097395371737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212354410771542731596914491 318531616157314097395371737)
      ·
        refine ⟨238898712117985573046528803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318531616157314097395371737 238898712117985573046528803)
        ·
          refine ⟨358348068176978359569793205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238898712117985573046528803 358348068176978359569793205)
          ·
            refine ⟨33595131391591721209668113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358348068176978359569793205 33595131391591721209668113)
            ·
              refine ⟨25196348543693790907251085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33595131391591721209668113 25196348543693790907251085)
              ·
                refine ⟨9448630703885171590219157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25196348543693790907251085 9448630703885171590219157)
                ·
                  refine ⟨442904564244617418291523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9448630703885171590219157 442904564244617418291523)
                  ·
                    rfl

theorem cell22_3881491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_3881491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881491 prefixEnd_3881491 := by exact prefixLift 3881491
  have htrace : WordTrace (prefixWord ++ tailWord_3881491) baseStart_3881491 baseEnd_3881491 := by
    simpa [prefixWord, tailWord_3881491, baseEnd_3881491] using wordTrace_append hprefix tailTrace_3881491
  have hstable : (prefixWord ++ tailWord_3881491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881491).length < 2 ^ (prefixWord ++ tailWord_3881491).sum := by decide
  have hdescent : baseEnd_3881491 < baseStart_3881491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881495 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 2, 5]
def baseStart_3881495 : Nat := 118140960795 + 3881495 * 2 ^ 59
def prefixEnd_3881495 : Nat := 4983230072969 + 3 ^ 40 * 3881495 * 2
def baseEnd_3881495 : Nat := 1328715062015597577774557

theorem tailTrace_3881495 : CollatzResearch.WordTrace tailWord_3881495 prefixEnd_3881495 1328715062015597577774557 := by
  unfold tailWord_3881495
  simp only [CollatzResearch.WordTrace]
  refine ⟨141569753073013996414421939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94379835382009330942947959 141569753073013996414421939)
  ·
    refine ⟨212354629609520994621632909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141569753073013996414421939 212354629609520994621632909)
    ·
      refine ⟨79632986103570372983112341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212354629609520994621632909 79632986103570372983112341)
      ·
        refine ⟨3732796223604861233583391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79632986103570372983112341 3732796223604861233583391)
        ·
          refine ⟨5599194335407291850375087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732796223604861233583391 5599194335407291850375087)
          ·
            refine ⟨8398791503110937775562631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599194335407291850375087 8398791503110937775562631)
            ·
              refine ⟨12598187254666406663343947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398791503110937775562631 12598187254666406663343947)
              ·
                refine ⟨18897280881999609995015921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12598187254666406663343947 18897280881999609995015921)
                ·
                  refine ⟨14172960661499707496261941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18897280881999609995015921 14172960661499707496261941)
                  ·
                    refine ⟨1328715062015597577774557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14172960661499707496261941 1328715062015597577774557)
                    ·
                      rfl

theorem cell22_3881495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_3881495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881495 prefixEnd_3881495 := by exact prefixLift 3881495
  have htrace : WordTrace (prefixWord ++ tailWord_3881495) baseStart_3881495 baseEnd_3881495 := by
    simpa [prefixWord, tailWord_3881495, baseEnd_3881495] using wordTrace_append hprefix tailTrace_3881495
  have hstable : (prefixWord ++ tailWord_3881495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881495).length < 2 ^ (prefixWord ++ tailWord_3881495).sum := by decide
  have hdescent : baseEnd_3881495 < baseStart_3881495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881523 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 4, 3]
def baseStart_3881523 : Nat := 118140960795 + 3881523 * 2 ^ 59
def prefixEnd_3881523 : Nat := 4983230072969 + 3 ^ 40 * 3881523 * 2
def baseEnd_3881523 : Nat := 1328724646987814838074471

theorem tailTrace_3881523 : CollatzResearch.WordTrace tailWord_3881523 prefixEnd_3881523 1328724646987814838074471 := by
  unfold tailWord_3881523
  simp only [CollatzResearch.WordTrace]
  refine ⟨141570774316912557196441223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94380516211275038130960815 141570774316912557196441223)
  ·
    refine ⟨212356161475368835794661835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141570774316912557196441223 212356161475368835794661835)
    ·
      refine ⟨318534242213053253691992753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212356161475368835794661835 318534242213053253691992753)
      ·
        refine ⟨238900681659789940268994565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318534242213053253691992753 238900681659789940268994565)
        ·
          refine ⟨44793877811210613800436481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238900681659789940268994565 44793877811210613800436481)
          ·
            refine ⟨33595408358407960350327361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44793877811210613800436481 33595408358407960350327361)
            ·
              refine ⟨25196556268805970262745521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33595408358407960350327361 25196556268805970262745521)
              ·
                refine ⟨18897417201604477697059141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25196556268805970262745521 18897417201604477697059141)
                ·
                  refine ⟨3543265725300839568198589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18897417201604477697059141 3543265725300839568198589)
                  ·
                    refine ⟨1328724646987814838074471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543265725300839568198589 1328724646987814838074471)
                    ·
                      rfl

theorem cell22_3881523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 3].length) (baseStart_3881523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881523 prefixEnd_3881523 := by exact prefixLift 3881523
  have htrace : WordTrace (prefixWord ++ tailWord_3881523) baseStart_3881523 baseEnd_3881523 := by
    simpa [prefixWord, tailWord_3881523, baseEnd_3881523] using wordTrace_append hprefix tailTrace_3881523
  have hstable : (prefixWord ++ tailWord_3881523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881523).length < 2 ^ (prefixWord ++ tailWord_3881523).sum := by decide
  have hdescent : baseEnd_3881523 < baseStart_3881523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881525 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 4]
def baseStart_3881525 : Nat := 118140960795 + 3881525 * 2 ^ 59
def prefixEnd_3881525 : Nat := 4983230072969 + 3 ^ 40 * 3881525 * 2
def baseEnd_3881525 : Nat := 442908443876229166508155

theorem tailTrace_3881525 : CollatzResearch.WordTrace tailWord_3881525 prefixEnd_3881525 442908443876229166508155 := by
  unfold tailWord_3881525
  simp only [CollatzResearch.WordTrace]
  refine ⟨141570847262905311538014029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94380564841936874358676019 141570847262905311538014029)
  ·
    refine ⟨53089067723589491826755261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141570847262905311538014029 53089067723589491826755261)
    ·
      refine ⟨19908400396346059435033223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53089067723589491826755261 19908400396346059435033223)
      ·
        refine ⟨29862600594519089152549835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19908400396346059435033223 29862600594519089152549835)
        ·
          refine ⟨44793900891778633728824753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29862600594519089152549835 44793900891778633728824753)
          ·
            refine ⟨33595425668833975296618565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44793900891778633728824753 33595425668833975296618565)
            ·
              refine ⟨6299142312906370368115981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33595425668833975296618565 6299142312906370368115981)
              ·
                refine ⟨2362178367339888888043493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6299142312906370368115981 2362178367339888888043493)
                ·
                  refine ⟨442908443876229166508155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362178367339888888043493 442908443876229166508155)
                  ·
                    rfl

theorem cell22_3881525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_3881525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881525 prefixEnd_3881525 := by exact prefixLift 3881525
  have htrace : WordTrace (prefixWord ++ tailWord_3881525) baseStart_3881525 baseEnd_3881525 := by
    simpa [prefixWord, tailWord_3881525, baseEnd_3881525] using wordTrace_append hprefix tailTrace_3881525
  have hstable : (prefixWord ++ tailWord_3881525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881525).length < 2 ^ (prefixWord ++ tailWord_3881525).sum := by decide
  have hdescent : baseEnd_3881525 < baseStart_3881525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881542 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3881542 : Nat := 118140960795 + 3881542 * 2 ^ 59
def prefixEnd_3881542 : Nat := 4983230072969 + 3 ^ 40 * 3881542 * 2
def baseEnd_3881542 : Nat := 442910383692035040616471

theorem tailTrace_3881542 : CollatzResearch.WordTrace tailWord_3881542 prefixEnd_3881542 442910383692035040616471 := by
  unfold tailWord_3881542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424108353245116357543215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94380978202562482294255253 4424108353245116357543215)
  ·
    refine ⟨6636162529867674536314823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424108353245116357543215 6636162529867674536314823)
    ·
      refine ⟨9954243794801511804472235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6636162529867674536314823 9954243794801511804472235)
      ·
        refine ⟨14931365692202267706708353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9954243794801511804472235 14931365692202267706708353)
        ·
          refine ⟨11198524269151700780031265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14931365692202267706708353 11198524269151700780031265)
          ·
            refine ⟨8398893201863775585023449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11198524269151700780031265 8398893201863775585023449)
            ·
              refine ⟨6299169901397831688767587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398893201863775585023449 6299169901397831688767587)
              ·
                refine ⟨9448754852096747533151381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299169901397831688767587 9448754852096747533151381)
                ·
                  refine ⟨442910383692035040616471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9448754852096747533151381 442910383692035040616471)
                  ·
                    rfl

theorem cell22_3881542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3881542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881542 prefixEnd_3881542 := by exact prefixLift 3881542
  have htrace : WordTrace (prefixWord ++ tailWord_3881542) baseStart_3881542 baseEnd_3881542 := by
    simpa [prefixWord, tailWord_3881542, baseEnd_3881542] using wordTrace_append hprefix tailTrace_3881542
  have hstable : (prefixWord ++ tailWord_3881542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881542).length < 2 ^ (prefixWord ++ tailWord_3881542).sum := by decide
  have hdescent : baseEnd_3881542 < baseStart_3881542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881658 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_3881658 : Nat := 118140960795 + 3881658 * 2 ^ 59
def prefixEnd_3881658 : Nat := 4983230072969 + 3 ^ 40 * 3881658 * 2
def baseEnd_3881658 : Nat := 1328770860246719485949057

theorem tailTrace_3881658 : CollatzResearch.WordTrace tailWord_3881658 prefixEnd_3881658 1328770860246719485949057 := by
  unfold tailWord_3881658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35393924542855868813151407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94383798780948983501737085 35393924542855868813151407)
  ·
    refine ⟨53090886814283803219727111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35393924542855868813151407 53090886814283803219727111)
    ·
      refine ⟨79636330221425704829590667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53090886814283803219727111 79636330221425704829590667)
      ·
        refine ⟨119454495332138557244386001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79636330221425704829590667 119454495332138557244386001)
        ·
          refine ⟨89590871499103917933289501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119454495332138557244386001 89590871499103917933289501)
          ·
            refine ⟨33596576812163969224983563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89590871499103917933289501 33596576812163969224983563)
            ·
              refine ⟨50394865218245953837475345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33596576812163969224983563 50394865218245953837475345)
              ·
                refine ⟨37796148913684465378106509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50394865218245953837475345 37796148913684465378106509)
                ·
                  refine ⟨14173555842631674516789941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37796148913684465378106509 14173555842631674516789941)
                  ·
                    refine ⟨1328770860246719485949057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14173555842631674516789941 1328770860246719485949057)
                    ·
                      rfl

theorem cell22_3881658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_3881658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881658 prefixEnd_3881658 := by exact prefixLift 3881658
  have htrace : WordTrace (prefixWord ++ tailWord_3881658) baseStart_3881658 baseEnd_3881658 := by
    simpa [prefixWord, tailWord_3881658, baseEnd_3881658] using wordTrace_append hprefix tailTrace_3881658
  have hstable : (prefixWord ++ tailWord_3881658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881658).length < 2 ^ (prefixWord ++ tailWord_3881658).sum := by decide
  have hdescent : baseEnd_3881658 < baseStart_3881658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881692 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3881692 : Nat := 118140960795 + 3881692 * 2 ^ 59
def prefixEnd_3881692 : Nat := 4983230072969 + 3 ^ 40 * 3881692 * 2
def baseEnd_3881692 : Nat := 1328782499141554730598953

theorem tailTrace_3881692 : CollatzResearch.WordTrace tailWord_3881692 prefixEnd_3881692 1328782499141554730598953 := by
  unfold tailWord_3881692
  simp only [CollatzResearch.WordTrace]
  refine ⟨70788469126650149529671665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94384625502200199372895553 70788469126650149529671665)
  ·
    refine ⟨53091351844987612147253749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70788469126650149529671665 53091351844987612147253749)
    ·
      refine ⟨4977314235467588638805039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53091351844987612147253749 4977314235467588638805039)
      ·
        refine ⟨7465971353201382958207559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977314235467588638805039 7465971353201382958207559)
        ·
          refine ⟨11198957029802074437311339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7465971353201382958207559 11198957029802074437311339)
          ·
            refine ⟨16798435544703111655967009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11198957029802074437311339 16798435544703111655967009)
            ·
              refine ⟨12598826658527333741975257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16798435544703111655967009 12598826658527333741975257)
              ·
                refine ⟨9449119993895500306481443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12598826658527333741975257 9449119993895500306481443)
                ·
                  refine ⟨14173679990843250459722165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449119993895500306481443 14173679990843250459722165)
                  ·
                    refine ⟨1328782499141554730598953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14173679990843250459722165 1328782499141554730598953)
                    ·
                      rfl

theorem cell22_3881692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3881692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881692 prefixEnd_3881692 := by exact prefixLift 3881692
  have htrace : WordTrace (prefixWord ++ tailWord_3881692) baseStart_3881692 baseEnd_3881692 := by
    simpa [prefixWord, tailWord_3881692, baseEnd_3881692] using wordTrace_append hprefix tailTrace_3881692
  have hstable : (prefixWord ++ tailWord_3881692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881692).length < 2 ^ (prefixWord ++ tailWord_3881692).sum := by decide
  have hdescent : baseEnd_3881692 < baseStart_3881692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881726 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3881726 : Nat := 118140960795 + 3881726 * 2 ^ 59
def prefixEnd_3881726 : Nat := 4983230072969 + 3 ^ 40 * 3881726 * 2
def baseEnd_3881726 : Nat := 1328794138036389975248849

theorem tailTrace_3881726 : CollatzResearch.WordTrace tailWord_3881726 prefixEnd_3881726 1328794138036389975248849 := by
  unfold tailWord_3881726
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697272291897140358260129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94385452223451415244054021 17697272291897140358260129)
  ·
    refine ⟨13272954218922855268695097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17697272291897140358260129 13272954218922855268695097)
    ·
      refine ⟨9954715664192141451521323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13272954218922855268695097 9954715664192141451521323)
      ·
        refine ⟨14932073496288212177281985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9954715664192141451521323 14932073496288212177281985)
        ·
          refine ⟨11199055122216159132961489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14932073496288212177281985 11199055122216159132961489)
          ·
            refine ⟨8399291341662119349721117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199055122216159132961489 8399291341662119349721117)
            ·
              refine ⟨3149734253123294756145419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8399291341662119349721117 3149734253123294756145419)
              ·
                refine ⟨4724601379684942134218129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149734253123294756145419 4724601379684942134218129)
                ·
                  refine ⟨3543451034763706600663597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4724601379684942134218129 3543451034763706600663597)
                  ·
                    refine ⟨1328794138036389975248849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543451034763706600663597 1328794138036389975248849)
                    ·
                      rfl

theorem cell22_3881726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3881726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881726 prefixEnd_3881726 := by exact prefixLift 3881726
  have htrace : WordTrace (prefixWord ++ tailWord_3881726) baseStart_3881726 baseEnd_3881726 := by
    simpa [prefixWord, tailWord_3881726, baseEnd_3881726] using wordTrace_append hprefix tailTrace_3881726
  have hstable : (prefixWord ++ tailWord_3881726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881726).length < 2 ^ (prefixWord ++ tailWord_3881726).sum := by decide
  have hdescent : baseEnd_3881726 < baseStart_3881726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881825 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_3881825 : Nat := 118140960795 + 3881825 * 2 ^ 59
def prefixEnd_3881825 : Nat := 4983230072969 + 3 ^ 40 * 3881825 * 2
def baseEnd_3881825 : Nat := 1328828027759586717023545

theorem tailTrace_3881825 : CollatzResearch.WordTrace tailWord_3881825 prefixEnd_3881825 1328828027759586717023545 := by
  unfold tailWord_3881825
  simp only [CollatzResearch.WordTrace]
  refine ⟨141581789161818462773934929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94387859441212308515956619 141581789161818462773934929)
  ·
    refine ⟨106186341871363847080451197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141581789161818462773934929 106186341871363847080451197)
    ·
      refine ⟨39819878201761442655169199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106186341871363847080451197 39819878201761442655169199)
      ·
        refine ⟨59729817302642163982753799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39819878201761442655169199 59729817302642163982753799)
        ·
          refine ⟨89594725953963245974130699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59729817302642163982753799 89594725953963245974130699)
          ·
            refine ⟨134392088930944868961196049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89594725953963245974130699 134392088930944868961196049)
            ·
              refine ⟨100794066698208651720897037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134392088930944868961196049 100794066698208651720897037)
              ·
                refine ⟨37797775011828244395336389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100794066698208651720897037 37797775011828244395336389)
                ·
                  refine ⟨7087082814717795824125573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37797775011828244395336389 7087082814717795824125573)
                  ·
                    refine ⟨1328828027759586717023545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7087082814717795824125573 1328828027759586717023545)
                    ·
                      rfl

theorem cell22_3881825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_3881825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881825 prefixEnd_3881825 := by exact prefixLift 3881825
  have htrace : WordTrace (prefixWord ++ tailWord_3881825) baseStart_3881825 baseEnd_3881825 := by
    simpa [prefixWord, tailWord_3881825, baseEnd_3881825] using wordTrace_append hprefix tailTrace_3881825
  have hstable : (prefixWord ++ tailWord_3881825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881825).length < 2 ^ (prefixWord ++ tailWord_3881825).sum := by decide
  have hdescent : baseEnd_3881825 < baseStart_3881825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881829 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 4]
def baseStart_3881829 : Nat := 118140960795 + 3881829 * 2 ^ 59
def prefixEnd_3881829 : Nat := 4983230072969 + 3 ^ 40 * 3881829 * 2
def baseEnd_3881829 : Nat := 442943132347110679974511

theorem tailTrace_3881829 : CollatzResearch.WordTrace tailWord_3881829 prefixEnd_3881829 442943132347110679974511 := by
  unfold tailWord_3881829
  simp only [CollatzResearch.WordTrace]
  refine ⟨141581935053803971457080541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94387956702535980971387027 141581935053803971457080541)
  ·
    refine ⟨53093225645176489296405203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141581935053803971457080541 53093225645176489296405203)
    ·
      refine ⟨79639838467764733944607805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53093225645176489296405203 79639838467764733944607805)
      ·
        refine ⟨29864939425411775229227927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79639838467764733944607805 29864939425411775229227927)
        ·
          refine ⟨44797409138117662843841891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29864939425411775229227927 44797409138117662843841891)
          ·
            refine ⟨67196113707176494265762837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44797409138117662843841891 67196113707176494265762837)
            ·
              refine ⟨3149817830023898168707633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67196113707176494265762837 3149817830023898168707633)
              ·
                refine ⟨2362363372517923626530725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149817830023898168707633 2362363372517923626530725)
                ·
                  refine ⟨442943132347110679974511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362363372517923626530725 442943132347110679974511)
                  ·
                    rfl

theorem cell22_3881829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_3881829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881829 prefixEnd_3881829 := by exact prefixLift 3881829
  have htrace : WordTrace (prefixWord ++ tailWord_3881829) baseStart_3881829 baseEnd_3881829 := by
    simpa [prefixWord, tailWord_3881829, baseEnd_3881829] using wordTrace_append hprefix tailTrace_3881829
  have hstable : (prefixWord ++ tailWord_3881829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881829).length < 2 ^ (prefixWord ++ tailWord_3881829).sum := by decide
  have hdescent : baseEnd_3881829 < baseStart_3881829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881840 : List Nat := [2, 1, 1, 1, 4, 1, 5, 7]
def baseStart_3881840 : Nat := 118140960795 + 3881840 * 2 ^ 59
def prefixEnd_3881840 : Nat := 4983230072969 + 3 ^ 40 * 3881840 * 2
def baseEnd_3881840 : Nat := 147648129174014630877611

theorem tailTrace_3881840 : CollatzResearch.WordTrace tailWord_3881840 prefixEnd_3881840 147648129174014630877611 := by
  unfold tailWord_3881840
  simp only [CollatzResearch.WordTrace]
  refine ⟨70791168128382060167865487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94388224171176080223820649 70791168128382060167865487)
  ·
    refine ⟨106186752192573090251798231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70791168128382060167865487 106186752192573090251798231)
    ·
      refine ⟨159280128288859635377697347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106186752192573090251798231 159280128288859635377697347)
      ·
        refine ⟨238920192433289453066546021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159280128288859635377697347 238920192433289453066546021)
        ·
          refine ⟨44797536081241772449977379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238920192433289453066546021 44797536081241772449977379)
          ·
            refine ⟨67196304121862658674966069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44797536081241772449977379 67196304121862658674966069)
            ·
              refine ⟨6299653511424624250778069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67196304121862658674966069 6299653511424624250778069)
              ·
                refine ⟨147648129174014630877611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6299653511424624250778069 147648129174014630877611)
                ·
                  rfl

theorem cell22_3881840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_3881840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881840 prefixEnd_3881840 := by exact prefixLift 3881840
  have htrace : WordTrace (prefixWord ++ tailWord_3881840) baseStart_3881840 baseEnd_3881840 := by
    simpa [prefixWord, tailWord_3881840, baseEnd_3881840] using wordTrace_append hprefix tailTrace_3881840
  have hstable : (prefixWord ++ tailWord_3881840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881840).length < 2 ^ (prefixWord ++ tailWord_3881840).sum := by decide
  have hdescent : baseEnd_3881840 < baseStart_3881840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881878 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3881878 : Nat := 118140960795 + 3881878 * 2 ^ 59
def prefixEnd_3881878 : Nat := 4983230072969 + 3 ^ 40 * 3881878 * 2
def baseEnd_3881878 : Nat := 1328846170742712245448383

theorem tailTrace_3881878 : CollatzResearch.WordTrace tailWord_3881878 prefixEnd_3881878 1328846170742712245448383 := by
  unfold tailWord_3881878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8848982639414153301600893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94389148153750968550409525 8848982639414153301600893)
  ·
    refine ⟨3318368489780307488100335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8848982639414153301600893 3318368489780307488100335)
    ·
      refine ⟨4977552734670461232150503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3318368489780307488100335 4977552734670461232150503)
      ·
        refine ⟨7466329102005691848225755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977552734670461232150503 7466329102005691848225755)
        ·
          refine ⟨11199493653008537772338633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466329102005691848225755 11199493653008537772338633)
          ·
            refine ⟨8399620239756403329253975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199493653008537772338633 8399620239756403329253975)
            ·
              refine ⟨12599430359634604993880963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8399620239756403329253975 12599430359634604993880963)
              ·
                refine ⟨18899145539451907490821445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12599430359634604993880963 18899145539451907490821445)
                ·
                  refine ⟨3543589788647232654529021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18899145539451907490821445 3543589788647232654529021)
                  ·
                    refine ⟨1328846170742712245448383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543589788647232654529021 1328846170742712245448383)
                    ·
                      rfl

theorem cell22_3881878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3881878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881878 prefixEnd_3881878 := by exact prefixLift 3881878
  have htrace : WordTrace (prefixWord ++ tailWord_3881878) baseStart_3881878 baseEnd_3881878 := by
    simpa [prefixWord, tailWord_3881878, baseEnd_3881878] using wordTrace_append hprefix tailTrace_3881878
  have hstable : (prefixWord ++ tailWord_3881878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881878).length < 2 ^ (prefixWord ++ tailWord_3881878).sum := by decide
  have hdescent : baseEnd_3881878 < baseStart_3881878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881889 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3881889 : Nat := 118140960795 + 3881889 * 2 ^ 59
def prefixEnd_3881889 : Nat := 4983230072969 + 3 ^ 40 * 3881889 * 2
def baseEnd_3881889 : Nat := 1328849936267511883423349

theorem tailTrace_3881889 : CollatzResearch.WordTrace tailWord_3881889 prefixEnd_3881889 1328849936267511883423349 := by
  unfold tailWord_3881889
  simp only [CollatzResearch.WordTrace]
  refine ⟨141584123433586601704264721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94389415622391067802843147 141584123433586601704264721)
  ·
    refine ⟨106188092575189951278198541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141584123433586601704264721 106188092575189951278198541)
    ·
      refine ⟨39820534715696231729324453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106188092575189951278198541 39820534715696231729324453)
      ·
        refine ⟨7466350259193043449248335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39820534715696231729324453 7466350259193043449248335)
        ·
          refine ⟨11199525388789565173872503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466350259193043449248335 11199525388789565173872503)
          ·
            refine ⟨16799288083184347760808755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199525388789565173872503 16799288083184347760808755)
            ·
              refine ⟨25198932124776521641213133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16799288083184347760808755 25198932124776521641213133)
              ·
                refine ⟨9449599546791195615454925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25198932124776521641213133 9449599546791195615454925)
                ·
                  refine ⟨3543599830046698355795597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9449599546791195615454925 3543599830046698355795597)
                  ·
                    refine ⟨1328849936267511883423349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543599830046698355795597 1328849936267511883423349)
                    ·
                      rfl

theorem cell22_3881889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3881889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881889 prefixEnd_3881889 := by exact prefixLift 3881889
  have htrace : WordTrace (prefixWord ++ tailWord_3881889) baseStart_3881889 baseEnd_3881889 := by
    simpa [prefixWord, tailWord_3881889, baseEnd_3881889] using wordTrace_append hprefix tailTrace_3881889
  have hstable : (prefixWord ++ tailWord_3881889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881889).length < 2 ^ (prefixWord ++ tailWord_3881889).sum := by decide
  have hdescent : baseEnd_3881889 < baseStart_3881889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881994 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3881994 : Nat := 118140960795 + 3881994 * 2 ^ 59
def prefixEnd_3881994 : Nat := 4983230072969 + 3 ^ 40 * 3881994 * 2
def baseEnd_3881994 : Nat := 1328885879913326609548027

theorem tailTrace_3881994 : CollatzResearch.WordTrace tailWord_3881994 prefixEnd_3881994 1328885879913326609548027 := by
  unfold tailWord_3881994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35396988274551551159209259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94391968732137469757891357 35396988274551551159209259)
  ·
    refine ⟨53095482411827326738813889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35396988274551551159209259 53095482411827326738813889)
    ·
      refine ⟨39821611808870495054110417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53095482411827326738813889 39821611808870495054110417)
      ·
        refine ⟨29866208856652871290582813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39821611808870495054110417 29866208856652871290582813)
        ·
          refine ⟨11199828321244826733968555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29866208856652871290582813 11199828321244826733968555)
          ·
            refine ⟨16799742481867240100952833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199828321244826733968555 16799742481867240100952833)
            ·
              refine ⟨12599806861400430075714625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16799742481867240100952833 12599806861400430075714625)
              ·
                refine ⟨9449855146050322556785969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12599806861400430075714625 9449855146050322556785969)
                ·
                  refine ⟨7087391359537741917589477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9449855146050322556785969 7087391359537741917589477)
                  ·
                    refine ⟨1328885879913326609548027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7087391359537741917589477 1328885879913326609548027)
                    ·
                      rfl

theorem cell22_3881994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3881994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881994 prefixEnd_3881994 := by exact prefixLift 3881994
  have htrace : WordTrace (prefixWord ++ tailWord_3881994) baseStart_3881994 baseEnd_3881994 := by
    simpa [prefixWord, tailWord_3881994, baseEnd_3881994] using wordTrace_append hprefix tailTrace_3881994
  have hstable : (prefixWord ++ tailWord_3881994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881994).length < 2 ^ (prefixWord ++ tailWord_3881994).sum := by decide
  have hdescent : baseEnd_3881994 < baseStart_3881994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881996 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_3881996 : Nat := 118140960795 + 3881996 * 2 ^ 59
def prefixEnd_3881996 : Nat := 4983230072969 + 3 ^ 40 * 3881996 * 2
def baseEnd_3881996 : Nat := 1328886564554199270998021

theorem tailTrace_3881996 : CollatzResearch.WordTrace tailWord_3881996 prefixEnd_3881996 1328886564554199270998021 := by
  unfold tailWord_3881996
  simp only [CollatzResearch.WordTrace]
  refine ⟨70794013022099479489204921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94392017362799305985606561 70794013022099479489204921)
  ·
    refine ⟨53095509766574609616903691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70794013022099479489204921 53095509766574609616903691)
    ·
      refine ⟨79643264649861914425355537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53095509766574609616903691 79643264649861914425355537)
      ·
        refine ⟨59732448487396435819016653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79643264649861914425355537 59732448487396435819016653)
        ·
          refine ⟨22399668182773663432131245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59732448487396435819016653 22399668182773663432131245)
          ·
            refine ⟨8399875568540123787049217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22399668182773663432131245 8399875568540123787049217)
            ·
              refine ⟨6299906676405092840286913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8399875568540123787049217 6299906676405092840286913)
              ·
                refine ⟨4724930007303819630215185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299906676405092840286913 4724930007303819630215185)
                ·
                  refine ⟨3543697505477864722661389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4724930007303819630215185 3543697505477864722661389)
                  ·
                    refine ⟨1328886564554199270998021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543697505477864722661389 1328886564554199270998021)
                    ·
                      rfl

theorem cell22_3881996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_3881996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881996 prefixEnd_3881996 := by exact prefixLift 3881996
  have htrace : WordTrace (prefixWord ++ tailWord_3881996) baseStart_3881996 baseEnd_3881996 := by
    simpa [prefixWord, tailWord_3881996, baseEnd_3881996] using wordTrace_append hprefix tailTrace_3881996
  have hstable : (prefixWord ++ tailWord_3881996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881996).length < 2 ^ (prefixWord ++ tailWord_3881996).sum := by decide
  have hdescent : baseEnd_3881996 < baseStart_3881996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881998 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3881998 : Nat := 118140960795 + 3881998 * 2 ^ 59
def prefixEnd_3881998 : Nat := 4983230072969 + 3 ^ 40 * 3881998 * 2
def baseEnd_3881998 : Nat := 442962416398357310816005

theorem tailTrace_3881998 : CollatzResearch.WordTrace tailWord_3881998 prefixEnd_3881998 442962416398357310816005 := by
  unfold tailWord_3881998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17698512373773964164997831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94392065993461142213321765 17698512373773964164997831)
  ·
    refine ⟨26547768560660946247496747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17698512373773964164997831 26547768560660946247496747)
    ·
      refine ⟨39821652840991419371245121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26547768560660946247496747 39821652840991419371245121)
      ·
        refine ⟨29866239630743564528433841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39821652840991419371245121 29866239630743564528433841)
        ·
          refine ⟨22399679723057673396325381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29866239630743564528433841 22399679723057673396325381)
          ·
            refine ⟨4199939948073313761811009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22399679723057673396325381 4199939948073313761811009)
            ·
              refine ⟨3149954961054985321358257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4199939948073313761811009 3149954961054985321358257)
              ·
                refine ⟨2362466220791238991018693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149954961054985321358257 2362466220791238991018693)
                ·
                  refine ⟨442962416398357310816005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362466220791238991018693 442962416398357310816005)
                  ·
                    rfl

theorem cell22_3881998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3881998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3881998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3881998 prefixEnd_3881998 := by exact prefixLift 3881998
  have htrace : WordTrace (prefixWord ++ tailWord_3881998) baseStart_3881998 baseEnd_3881998 := by
    simpa [prefixWord, tailWord_3881998, baseEnd_3881998] using wordTrace_append hprefix tailTrace_3881998
  have hstable : (prefixWord ++ tailWord_3881998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881998).length < 2 ^ (prefixWord ++ tailWord_3881998).sum := by decide
  have hdescent : baseEnd_3881998 < baseStart_3881998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882026 : List Nat := [3, 1, 4, 1, 3, 1, 3, 6]
def baseStart_3882026 : Nat := 118140960795 + 3882026 * 2 ^ 59
def prefixEnd_3882026 : Nat := 4983230072969 + 3 ^ 40 * 3882026 * 2
def baseEnd_3882026 : Nat := 147655203796365465860881

theorem tailTrace_3882026 : CollatzResearch.WordTrace tailWord_3882026 prefixEnd_3882026 147655203796365465860881 := by
  unfold tailWord_3882026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35397280058522568525500483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94392746822726849401334621 35397280058522568525500483)
  ·
    refine ⟨53095920087783852788250725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35397280058522568525500483 53095920087783852788250725)
    ·
      refine ⟨9955485016459472397797011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53095920087783852788250725 9955485016459472397797011)
      ·
        refine ⟨14933227524689208596695517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9955485016459472397797011 14933227524689208596695517)
        ·
          refine ⟨5599960321758453223760819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14933227524689208596695517 5599960321758453223760819)
          ·
            refine ⟨8399940482637679835641229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599960321758453223760819 8399940482637679835641229)
            ·
              refine ⟨3149977680989129938365461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8399940482637679835641229 3149977680989129938365461)
              ·
                refine ⟨147655203796365465860881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3149977680989129938365461 147655203796365465860881)
                ·
                  rfl

theorem cell22_3882026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_3882026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882026 prefixEnd_3882026 := by exact prefixLift 3882026
  have htrace : WordTrace (prefixWord ++ tailWord_3882026) baseStart_3882026 baseEnd_3882026 := by
    simpa [prefixWord, tailWord_3882026, baseEnd_3882026] using wordTrace_append hprefix tailTrace_3882026
  have hstable : (prefixWord ++ tailWord_3882026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882026).length < 2 ^ (prefixWord ++ tailWord_3882026).sum := by decide
  have hdescent : baseEnd_3882026 < baseStart_3882026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882037 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 7]
def baseStart_3882037 : Nat := 118140960795 + 3882037 * 2 ^ 59
def prefixEnd_3882037 : Nat := 4983230072969 + 3 ^ 40 * 3882037 * 2
def baseEnd_3882037 : Nat := 442966866564029610240965

theorem tailTrace_3882037 : CollatzResearch.WordTrace tailWord_3882037 prefixEnd_3882037 442966866564029610240965 := by
  unfold tailWord_3882037
  simp only [CollatzResearch.WordTrace]
  refine ⟨141589521437050422980652365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94393014291366948653768243 141589521437050422980652365)
  ·
    refine ⟨53096070538893908617744637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141589521437050422980652365 53096070538893908617744637)
    ·
      refine ⟨19911026452085215731654239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53096070538893908617744637 19911026452085215731654239)
      ·
        refine ⟨29866539678127823597481359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19911026452085215731654239 29866539678127823597481359)
        ·
          refine ⟨44799809517191735396222039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29866539678127823597481359 44799809517191735396222039)
          ·
            refine ⟨67199714275787603094333059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44799809517191735396222039 67199714275787603094333059)
            ·
              refine ⟨100799571413681404641499589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67199714275787603094333059 100799571413681404641499589)
              ·
                refine ⟨18899919640065263370281173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100799571413681404641499589 18899919640065263370281173)
                ·
                  refine ⟨442966866564029610240965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18899919640065263370281173 442966866564029610240965)
                  ·
                    rfl

theorem cell22_3882037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_3882037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882037 prefixEnd_3882037 := by exact prefixLift 3882037
  have htrace : WordTrace (prefixWord ++ tailWord_3882037) baseStart_3882037 baseEnd_3882037 := by
    simpa [prefixWord, tailWord_3882037, baseEnd_3882037] using wordTrace_append hprefix tailTrace_3882037
  have hstable : (prefixWord ++ tailWord_3882037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882037).length < 2 ^ (prefixWord ++ tailWord_3882037).sum := by decide
  have hdescent : baseEnd_3882037 < baseStart_3882037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882116 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 6]
def baseStart_3882116 : Nat := 118140960795 + 3882116 * 2 ^ 59
def prefixEnd_3882116 : Nat := 4983230072969 + 3 ^ 40 * 3882116 * 2
def baseEnd_3882116 : Nat := 442975881002186319332551

theorem tailTrace_3882116 : CollatzResearch.WordTrace tailWord_3882116 prefixEnd_3882116 442975881002186319332551 := by
  unfold tailWord_3882116
  simp only [CollatzResearch.WordTrace]
  refine ⟨70796201401882109736389101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94394935202509479648518801 70796201401882109736389101)
  ·
    refine ⟨26548575525705791151145913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70796201401882109736389101 26548575525705791151145913)
    ·
      refine ⟨19911431644279343363359435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26548575525705791151145913 19911431644279343363359435)
      ·
        refine ⟨29867147466419015045039153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19911431644279343363359435 29867147466419015045039153)
        ·
          refine ⟨22400360599814261283779365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29867147466419015045039153 22400360599814261283779365)
          ·
            refine ⟨4200067612465173990708631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22400360599814261283779365 4200067612465173990708631)
            ·
              refine ⟨6300101418697760986062947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200067612465173990708631 6300101418697760986062947)
              ·
                refine ⟨9450152128046641479094421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300101418697760986062947 9450152128046641479094421)
                ·
                  refine ⟨442975881002186319332551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9450152128046641479094421 442975881002186319332551)
                  ·
                    rfl

theorem cell22_3882116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_3882116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882116 prefixEnd_3882116 := by exact prefixLift 3882116
  have htrace : WordTrace (prefixWord ++ tailWord_3882116) baseStart_3882116 baseEnd_3882116 := by
    simpa [prefixWord, tailWord_3882116, baseEnd_3882116] using wordTrace_append hprefix tailTrace_3882116
  have hstable : (prefixWord ++ tailWord_3882116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882116).length < 2 ^ (prefixWord ++ tailWord_3882116).sum := by decide
  have hdescent : baseEnd_3882116 < baseStart_3882116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882182 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3882182 : Nat := 118140960795 + 3882182 * 2 ^ 59
def prefixEnd_3882182 : Nat := 4983230072969 + 3 ^ 40 * 3882182 * 2
def baseEnd_3882182 : Nat := 1328950236155356785847451

theorem tailTrace_3882182 : CollatzResearch.WordTrace tailWord_3882182 prefixEnd_3882182 1328950236155356785847451 := by
  unfold tailWord_3882182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424837813172659773271275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94396540014350075163120533 4424837813172659773271275)
  ·
    refine ⟨6637256719758989659906913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424837813172659773271275 6637256719758989659906913)
    ·
      refine ⟨4977942539819242244930185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6637256719758989659906913 4977942539819242244930185)
      ·
        refine ⟨3733456904864431683697639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4977942539819242244930185 3733456904864431683697639)
        ·
          refine ⟨5600185357296647525546459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733456904864431683697639 5600185357296647525546459)
          ·
            refine ⟨8400278035944971288319689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600185357296647525546459 8400278035944971288319689)
            ·
              refine ⟨6300208526958728466239767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8400278035944971288319689 6300208526958728466239767)
              ·
                refine ⟨9450312790438092699359651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300208526958728466239767 9450312790438092699359651)
                ·
                  refine ⟨14175469185657139049039477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9450312790438092699359651 14175469185657139049039477)
                  ·
                    refine ⟨1328950236155356785847451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14175469185657139049039477 1328950236155356785847451)
                    ·
                      rfl

theorem cell22_3882182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3882182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882182 prefixEnd_3882182 := by exact prefixLift 3882182
  have htrace : WordTrace (prefixWord ++ tailWord_3882182) baseStart_3882182 baseEnd_3882182 := by
    simpa [prefixWord, tailWord_3882182, baseEnd_3882182] using wordTrace_append hprefix tailTrace_3882182
  have hstable : (prefixWord ++ tailWord_3882182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882182).length < 2 ^ (prefixWord ++ tailWord_3882182).sum := by decide
  have hdescent : baseEnd_3882182 < baseStart_3882182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882221 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3882221 : Nat := 118140960795 + 3882221 * 2 ^ 59
def prefixEnd_3882221 : Nat := 4983230072969 + 3 ^ 40 * 3882221 * 2
def baseEnd_3882221 : Nat := 1328963586652373684122331

theorem tailTrace_3882221 : CollatzResearch.WordTrace tailWord_3882221 prefixEnd_3882221 1328963586652373684122331 := by
  unfold tailWord_3882221
  simp only [CollatzResearch.WordTrace]
  refine ⟨141596232468383822405350517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94397488312255881603567011 141596232468383822405350517)
  ·
    refine ⟨13274646793910983350501611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141596232468383822405350517 13274646793910983350501611)
    ·
      refine ⟨19911970190866475025752417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13274646793910983350501611 19911970190866475025752417)
      ·
        refine ⟨14933977643149856269314313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19911970190866475025752417 14933977643149856269314313)
        ·
          refine ⟨11200483232362392201985735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14933977643149856269314313 11200483232362392201985735)
          ·
            refine ⟨16800724848543588302978603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200483232362392201985735 16800724848543588302978603)
            ·
              refine ⟨25201087272815382454467905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16800724848543588302978603 25201087272815382454467905)
              ·
                refine ⟨18900815454611536840850929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25201087272815382454467905 18900815454611536840850929)
                ·
                  refine ⟨14175611590958652630638197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18900815454611536840850929 14175611590958652630638197)
                  ·
                    refine ⟨1328963586652373684122331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14175611590958652630638197 1328963586652373684122331)
                    ·
                      rfl

theorem cell22_3882221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3882221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882221 prefixEnd_3882221 := by exact prefixLift 3882221
  have htrace : WordTrace (prefixWord ++ tailWord_3882221) baseStart_3882221 baseEnd_3882221 := by
    simpa [prefixWord, tailWord_3882221, baseEnd_3882221] using wordTrace_append hprefix tailTrace_3882221
  have hstable : (prefixWord ++ tailWord_3882221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882221).length < 2 ^ (prefixWord ++ tailWord_3882221).sum := by decide
  have hdescent : baseEnd_3882221 < baseStart_3882221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882223 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 5]
def baseStart_3882223 : Nat := 118140960795 + 3882223 * 2 ^ 59
def prefixEnd_3882223 : Nat := 4983230072969 + 3 ^ 40 * 3882223 * 2
def baseEnd_3882223 : Nat := 442988090431082115190775

theorem tailTrace_3882223 : CollatzResearch.WordTrace tailWord_3882223 prefixEnd_3882223 442988090431082115190775 := by
  unfold tailWord_3882223
  simp only [CollatzResearch.WordTrace]
  refine ⟨141596305414376576746923323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94397536942917717831282215 141596305414376576746923323)
  ·
    refine ⟨212394458121564865120384985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141596305414376576746923323 212394458121564865120384985)
    ·
      refine ⟨159295843591173648840288739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212394458121564865120384985 159295843591173648840288739)
      ·
        refine ⟨238943765386760473260433109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159295843591173648840288739 238943765386760473260433109)
        ·
          refine ⟨5600244501252198592041401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 238943765386760473260433109 5600244501252198592041401)
          ·
            refine ⟨4200183375939148944031051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5600244501252198592041401 4200183375939148944031051)
            ·
              refine ⟨6300275063908723416046577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200183375939148944031051 6300275063908723416046577)
              ·
                refine ⟨4725206297931542562034933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300275063908723416046577 4725206297931542562034933)
                ·
                  refine ⟨442988090431082115190775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725206297931542562034933 442988090431082115190775)
                  ·
                    rfl

theorem cell22_3882223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 5].length) (baseStart_3882223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882223 prefixEnd_3882223 := by exact prefixLift 3882223
  have htrace : WordTrace (prefixWord ++ tailWord_3882223) baseStart_3882223 baseEnd_3882223 := by
    simpa [prefixWord, tailWord_3882223, baseEnd_3882223] using wordTrace_append hprefix tailTrace_3882223
  have hstable : (prefixWord ++ tailWord_3882223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882223).length < 2 ^ (prefixWord ++ tailWord_3882223).sum := by decide
  have hdescent : baseEnd_3882223 < baseStart_3882223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882268 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 4]
def baseStart_3882268 : Nat := 118140960795 + 3882268 * 2 ^ 59
def prefixEnd_3882268 : Nat := 4983230072969 + 3 ^ 40 * 3882268 * 2
def baseEnd_3882268 : Nat := 442993225237627076065729

theorem tailTrace_3882268 : CollatzResearch.WordTrace tailWord_3882268 prefixEnd_3882268 442993225237627076065729 := by
  unfold tailWord_3882268
  simp only [CollatzResearch.WordTrace]
  refine ⟨70798973349606774716155729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94398631132809032954874305 70798973349606774716155729)
  ·
    refine ⟨53099230012205081037116797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70798973349606774716155729 53099230012205081037116797)
    ·
      refine ⟨19912211254576905388918799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53099230012205081037116797 19912211254576905388918799)
      ·
        refine ⟨29868316881865358083378199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19912211254576905388918799 29868316881865358083378199)
        ·
          refine ⟨44802475322798037125067299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29868316881865358083378199 44802475322798037125067299)
          ·
            refine ⟨67203712984197055687600949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44802475322798037125067299 67203712984197055687600949)
            ·
              refine ⟨6300348092268473970712589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67203712984197055687600949 6300348092268473970712589)
              ·
                refine ⟨2362630534600677739017221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6300348092268473970712589 2362630534600677739017221)
                ·
                  refine ⟨442993225237627076065729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362630534600677739017221 442993225237627076065729)
                  ·
                    rfl

theorem cell22_3882268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_3882268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882268 prefixEnd_3882268 := by exact prefixLift 3882268
  have htrace : WordTrace (prefixWord ++ tailWord_3882268) baseStart_3882268 baseEnd_3882268 := by
    simpa [prefixWord, tailWord_3882268, baseEnd_3882268] using wordTrace_append hprefix tailTrace_3882268
  have hstable : (prefixWord ++ tailWord_3882268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882268).length < 2 ^ (prefixWord ++ tailWord_3882268).sum := by decide
  have hdescent : baseEnd_3882268 < baseStart_3882268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882285 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3882285 : Nat := 118140960795 + 3882285 * 2 ^ 59
def prefixEnd_3882285 : Nat := 4983230072969 + 3 ^ 40 * 3882285 * 2
def baseEnd_3882285 : Nat := 442995165053432950174045

theorem tailTrace_3882285 : CollatzResearch.WordTrace tailWord_3882285 prefixEnd_3882285 442995165053432950174045 := by
  unfold tailWord_3882285
  simp only [CollatzResearch.WordTrace]
  refine ⟨141598566740151961335680309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94399044493434640890453539 141598566740151961335680309)
  ·
    refine ⟨13274865631889246375220029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141598566740151961335680309 13274865631889246375220029)
    ·
      refine ⟨4978074611958467390707511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13274865631889246375220029 4978074611958467390707511)
      ·
        refine ⟨7467111917937701086061267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978074611958467390707511 7467111917937701086061267)
        ·
          refine ⟨11200667876906551629091901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467111917937701086061267 11200667876906551629091901)
          ·
            refine ⟨4200250453839956860909463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11200667876906551629091901 4200250453839956860909463)
            ·
              refine ⟨6300375680759935291364195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200250453839956860909463 6300375680759935291364195)
              ·
                refine ⟨9450563521139902937046293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300375680759935291364195 9450563521139902937046293)
                ·
                  refine ⟨442995165053432950174045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9450563521139902937046293 442995165053432950174045)
                  ·
                    rfl

theorem cell22_3882285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3882285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882285 prefixEnd_3882285 := by exact prefixLift 3882285
  have htrace : WordTrace (prefixWord ++ tailWord_3882285) baseStart_3882285 baseEnd_3882285 := by
    simpa [prefixWord, tailWord_3882285, baseEnd_3882285] using wordTrace_append hprefix tailTrace_3882285
  have hstable : (prefixWord ++ tailWord_3882285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882285).length < 2 ^ (prefixWord ++ tailWord_3882285).sum := by decide
  have hdescent : baseEnd_3882285 < baseStart_3882285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882300 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_3882300 : Nat := 118140960795 + 3882300 * 2 ^ 59
def prefixEnd_3882300 : Nat := 4983230072969 + 3 ^ 40 * 3882300 * 2
def baseEnd_3882300 : Nat := 1328990629966843811397089

theorem tailTrace_3882300 : CollatzResearch.WordTrace tailWord_3882300 prefixEnd_3882300 1328990629966843811397089 := by
  unfold tailWord_3882300
  simp only [CollatzResearch.WordTrace]
  refine ⟨70799556917548809448738177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94399409223398412598317569 70799556917548809448738177)
  ·
    refine ⟨53099667688161607086553633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70799556917548809448738177 53099667688161607086553633)
    ·
      refine ⟨39824750766121205314915225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53099667688161607086553633 39824750766121205314915225)
      ·
        refine ⟨29868563074590903986186419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39824750766121205314915225 29868563074590903986186419)
        ·
          refine ⟨44802844611886355979279629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29868563074590903986186419 44802844611886355979279629)
          ·
            refine ⟨16801066729457383492229861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44802844611886355979279629 16801066729457383492229861)
            ·
              refine ⟨3150200011773259404793099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16801066729457383492229861 3150200011773259404793099)
              ·
                refine ⟨4725300017659889107189649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150200011773259404793099 4725300017659889107189649)
                ·
                  refine ⟨3543975013244916830392237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725300017659889107189649 3543975013244916830392237)
                  ·
                    refine ⟨1328990629966843811397089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543975013244916830392237 1328990629966843811397089)
                    ·
                      rfl

theorem cell22_3882300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_3882300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882300 prefixEnd_3882300 := by exact prefixLift 3882300
  have htrace : WordTrace (prefixWord ++ tailWord_3882300) baseStart_3882300 baseEnd_3882300 := by
    simpa [prefixWord, tailWord_3882300, baseEnd_3882300] using wordTrace_append hprefix tailTrace_3882300
  have hstable : (prefixWord ++ tailWord_3882300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882300).length < 2 ^ (prefixWord ++ tailWord_3882300).sum := by decide
  have hdescent : baseEnd_3882300 < baseStart_3882300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882392 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 5]
def baseStart_3882392 : Nat := 118140960795 + 3882392 * 2 ^ 59
def prefixEnd_3882392 : Nat := 4983230072969 + 3 ^ 40 * 3882392 * 2
def baseEnd_3882392 : Nat := 443007374482328746032269

theorem tailTrace_3882392 : CollatzResearch.WordTrace tailWord_3882392 prefixEnd_3882392 443007374482328746032269 := by
  unfold tailWord_3882392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70801234675382159304912715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94401646233842879073216953 70801234675382159304912715)
  ·
    refine ⟨106201852013073238957369073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70801234675382159304912715 106201852013073238957369073)
    ·
      refine ⟨79651389009804929218026805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106201852013073238957369073 79651389009804929218026805)
      ·
        refine ⟨7467317719669212114190013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79651389009804929218026805 7467317719669212114190013)
        ·
          refine ⟨2800244144875954542821255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7467317719669212114190013 2800244144875954542821255)
          ·
            refine ⟨4200366217313931814231883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800244144875954542821255 4200366217313931814231883)
            ·
              refine ⟨6300549325970897721347825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200366217313931814231883 6300549325970897721347825)
              ·
                refine ⟨4725411994478173291010869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300549325970897721347825 4725411994478173291010869)
                ·
                  refine ⟨443007374482328746032269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725411994478173291010869 443007374482328746032269)
                  ·
                    rfl

theorem cell22_3882392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_3882392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882392 prefixEnd_3882392 := by exact prefixLift 3882392
  have htrace : WordTrace (prefixWord ++ tailWord_3882392) baseStart_3882392 baseEnd_3882392 := by
    simpa [prefixWord, tailWord_3882392, baseEnd_3882392] using wordTrace_append hprefix tailTrace_3882392
  have hstable : (prefixWord ++ tailWord_3882392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882392).length < 2 ^ (prefixWord ++ tailWord_3882392).sum := by decide
  have hdescent : baseEnd_3882392 < baseStart_3882392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882403 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 4]
def baseStart_3882403 : Nat := 118140960795 + 3882403 * 2 ^ 59
def prefixEnd_3882403 : Nat := 4983230072969 + 3 ^ 40 * 3882403 * 2
def baseEnd_3882403 : Nat := 443008629657261958690591

theorem tailTrace_3882403 : CollatzResearch.WordTrace tailWord_3882403 prefixEnd_3882403 443008629657261958690591 := by
  unfold tailWord_3882403
  simp only [CollatzResearch.WordTrace]
  refine ⟨141602870553724467488475863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94401913702482978325650575 141602870553724467488475863)
  ·
    refine ⟨212404305830586701232713795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141602870553724467488475863 212404305830586701232713795)
    ·
      refine ⟨318606458745880051849070693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212404305830586701232713795 318606458745880051849070693)
      ·
        refine ⟨59738711014852509721700755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318606458745880051849070693 59738711014852509721700755)
        ·
          refine ⟨89608066522278764582551133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59738711014852509721700755 89608066522278764582551133)
          ·
            refine ⟨33603024945854536718456675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89608066522278764582551133 33603024945854536718456675)
            ·
              refine ⟨50404537418781805077685013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33603024945854536718456675 50404537418781805077685013)
              ·
                refine ⟨2362712691505397113016485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50404537418781805077685013 2362712691505397113016485)
                ·
                  refine ⟨443008629657261958690591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362712691505397113016485 443008629657261958690591)
                  ·
                    rfl

theorem cell22_3882403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 4].length) (baseStart_3882403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882403 prefixEnd_3882403 := by exact prefixLift 3882403
  have htrace : WordTrace (prefixWord ++ tailWord_3882403) baseStart_3882403 baseEnd_3882403 := by
    simpa [prefixWord, tailWord_3882403, baseEnd_3882403] using wordTrace_append hprefix tailTrace_3882403
  have hstable : (prefixWord ++ tailWord_3882403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882403).length < 2 ^ (prefixWord ++ tailWord_3882403).sum := by decide
  have hdescent : baseEnd_3882403 < baseStart_3882403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882416 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_3882416 : Nat := 118140960795 + 3882416 * 2 ^ 59
def prefixEnd_3882416 : Nat := 4983230072969 + 3 ^ 40 * 3882416 * 2
def baseEnd_3882416 : Nat := 1329030339137458175496733

theorem tailTrace_3882416 : CollatzResearch.WordTrace tailWord_3882416 prefixEnd_3882416 1329030339137458175496733 := by
  unfold tailWord_3882416
  simp only [CollatzResearch.WordTrace]
  refine ⟨70801672351338685354349551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94402229801784913805799401 70801672351338685354349551)
  ·
    refine ⟨106202508527008028031524327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70801672351338685354349551 106202508527008028031524327)
    ·
      refine ⟨159303762790512042047286491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106202508527008028031524327 159303762790512042047286491)
      ·
        refine ⟨238955644185768063070929737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159303762790512042047286491 238955644185768063070929737)
        ·
          refine ⟨179216733139326047303197303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238955644185768063070929737 179216733139326047303197303)
          ·
            refine ⟨268825099708989070954795955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179216733139326047303197303 268825099708989070954795955)
            ·
              refine ⟨403237649563483606432193933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268825099708989070954795955 403237649563483606432193933)
              ·
                refine ⟨151214118586306352412072725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403237649563483606432193933 151214118586306352412072725)
                ·
                  refine ⟨7088161808733110269315909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151214118586306352412072725 7088161808733110269315909)
                  ·
                    refine ⟨1329030339137458175496733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7088161808733110269315909 1329030339137458175496733)
                    ·
                      rfl

theorem cell22_3882416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_3882416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882416 prefixEnd_3882416 := by exact prefixLift 3882416
  have htrace : WordTrace (prefixWord ++ tailWord_3882416) baseStart_3882416 baseEnd_3882416 := by
    simpa [prefixWord, tailWord_3882416, baseEnd_3882416] using wordTrace_append hprefix tailTrace_3882416
  have hstable : (prefixWord ++ tailWord_3882416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882416).length < 2 ^ (prefixWord ++ tailWord_3882416).sum := by decide
  have hdescent : baseEnd_3882416 < baseStart_3882416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882454 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3882454 : Nat := 118140960795 + 3882454 * 2 ^ 59
def prefixEnd_3882454 : Nat := 4983230072969 + 3 ^ 40 * 3882454 * 2
def baseEnd_3882454 : Nat := 443014449104679581015539

theorem tailTrace_3882454 : CollatzResearch.WordTrace tailWord_3882454 prefixEnd_3882454 443014449104679581015539 := by
  unfold tailWord_3882454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850295667283731449911401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94403153784359802132388277 8850295667283731449911401)
  ·
    refine ⟨6637721750462798587433551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8850295667283731449911401 6637721750462798587433551)
    ·
      refine ⟨9956582625694197881150327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6637721750462798587433551 9956582625694197881150327)
      ·
        refine ⟨14934873938541296821725491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956582625694197881150327 14934873938541296821725491)
        ·
          refine ⟨22402310907811945232588237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14934873938541296821725491 22402310907811945232588237)
          ·
            refine ⟨8400866590429479462220589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22402310907811945232588237 8400866590429479462220589)
            ·
              refine ⟨3150324971411054798332721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8400866590429479462220589 3150324971411054798332721)
              ·
                refine ⟨2362743728558291098749541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150324971411054798332721 2362743728558291098749541)
                ·
                  refine ⟨443014449104679581015539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362743728558291098749541 443014449104679581015539)
                  ·
                    rfl

theorem cell22_3882454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3882454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882454 prefixEnd_3882454 := by exact prefixLift 3882454
  have htrace : WordTrace (prefixWord ++ tailWord_3882454) baseStart_3882454 baseEnd_3882454 := by
    simpa [prefixWord, tailWord_3882454, baseEnd_3882454] using wordTrace_append hprefix tailTrace_3882454
  have hstable : (prefixWord ++ tailWord_3882454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882454).length < 2 ^ (prefixWord ++ tailWord_3882454).sum := by decide
  have hdescent : baseEnd_3882454 < baseStart_3882454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882469 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_3882469 : Nat := 118140960795 + 3882469 * 2 ^ 59
def prefixEnd_3882469 : Nat := 4983230072969 + 3 ^ 40 * 3882469 * 2
def baseEnd_3882469 : Nat := 1329048482120583703921571

theorem tailTrace_3882469 : CollatzResearch.WordTrace tailWord_3882469 prefixEnd_3882469 1329048482120583703921571 := by
  unfold tailWord_3882469
  simp only [CollatzResearch.WordTrace]
  refine ⟨141605277771485360760378461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94403518514323573840252307 141605277771485360760378461)
  ·
    refine ⟨53101979164307010285141923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141605277771485360760378461 53101979164307010285141923)
    ·
      refine ⟨79652968746460515427712885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53101979164307010285141923 79652968746460515427712885)
      ·
        refine ⟨7467465819980673321348083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79652968746460515427712885 7467465819980673321348083)
        ·
          refine ⟨11201198729971009982022125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467465819980673321348083 11201198729971009982022125)
          ·
            refine ⟨4200449523739128743258297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11201198729971009982022125 4200449523739128743258297)
            ·
              refine ⟨3150337142804346557443723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200449523739128743258297 3150337142804346557443723)
              ·
                refine ⟨4725505714206519836165585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150337142804346557443723 4725505714206519836165585)
                ·
                  refine ⟨3544129285654889877124189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725505714206519836165585 3544129285654889877124189)
                  ·
                    refine ⟨1329048482120583703921571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544129285654889877124189 1329048482120583703921571)
                    ·
                      rfl

theorem cell22_3882469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_3882469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882469 prefixEnd_3882469 := by exact prefixLift 3882469
  have htrace : WordTrace (prefixWord ++ tailWord_3882469) baseStart_3882469 baseEnd_3882469 := by
    simpa [prefixWord, tailWord_3882469, baseEnd_3882469] using wordTrace_append hprefix tailTrace_3882469
  have hstable : (prefixWord ++ tailWord_3882469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882469).length < 2 ^ (prefixWord ++ tailWord_3882469).sum := by decide
  have hdescent : baseEnd_3882469 < baseStart_3882469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882476 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_3882476 : Nat := 118140960795 + 3882476 * 2 ^ 59
def prefixEnd_3882476 : Nat := 4983230072969 + 3 ^ 40 * 3882476 * 2
def baseEnd_3882476 : Nat := 443016959454546006332183

theorem tailTrace_3882476 : CollatzResearch.WordTrace tailWord_3882476 prefixEnd_3882476 443016959454546006332183 := by
  unfold tailWord_3882476
  simp only [CollatzResearch.WordTrace]
  refine ⟨70802766541230000477941641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94403688721640000637255521 70802766541230000477941641)
  ·
    refine ⟨53102074905922500358456231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70802766541230000477941641 53102074905922500358456231)
    ·
      refine ⟨79653112358883750537684347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53102074905922500358456231 79653112358883750537684347)
      ·
        refine ⟨119479668538325625806526521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79653112358883750537684347 119479668538325625806526521)
        ·
          refine ⟨89609751403744219354894891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119479668538325625806526521 89609751403744219354894891)
          ·
            refine ⟨134414627105616329032342337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89609751403744219354894891 134414627105616329032342337)
            ·
              refine ⟨100810970329212246774256753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134414627105616329032342337 100810970329212246774256753)
              ·
                refine ⟨75608227746909185080692565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100810970329212246774256753 75608227746909185080692565)
                ·
                  refine ⟨443016959454546006332183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75608227746909185080692565 443016959454546006332183)
                  ·
                    rfl

theorem cell22_3882476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_3882476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882476 prefixEnd_3882476 := by exact prefixLift 3882476
  have htrace : WordTrace (prefixWord ++ tailWord_3882476) baseStart_3882476 baseEnd_3882476 := by
    simpa [prefixWord, tailWord_3882476, baseEnd_3882476] using wordTrace_append hprefix tailTrace_3882476
  have hstable : (prefixWord ++ tailWord_3882476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882476).length < 2 ^ (prefixWord ++ tailWord_3882476).sum := by decide
  have hdescent : baseEnd_3882476 < baseStart_3882476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882491 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_3882491 : Nat := 118140960795 + 3882491 * 2 ^ 59
def prefixEnd_3882491 : Nat := 4983230072969 + 3 ^ 40 * 3882491 * 2
def baseEnd_3882491 : Nat := 1329056013170182979871503

theorem tailTrace_3882491 : CollatzResearch.WordTrace tailWord_3882491 prefixEnd_3882491 1329056013170182979871503 := by
  unfold tailWord_3882491
  simp only [CollatzResearch.WordTrace]
  refine ⟨141606080177405658517679327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94404053451603772345119551 141606080177405658517679327)
  ·
    refine ⟨212409120266108487776518991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141606080177405658517679327 212409120266108487776518991)
    ·
      refine ⟨318613680399162731664778487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212409120266108487776518991 318613680399162731664778487)
      ·
        refine ⟨477920520598744097497167731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318613680399162731664778487 477920520598744097497167731)
        ·
          refine ⟨716880780898116146245751597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477920520598744097497167731 716880780898116146245751597)
          ·
            refine ⟨268830292836793554842156849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 716880780898116146245751597 268830292836793554842156849)
            ·
              refine ⟨201622719627595166131617637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268830292836793554842156849 201622719627595166131617637)
              ·
                refine ⟨37804259930174093649678307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201622719627595166131617637 37804259930174093649678307)
                ·
                  refine ⟨56706389895261140474517461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37804259930174093649678307 56706389895261140474517461)
                  ·
                    refine ⟨1329056013170182979871503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56706389895261140474517461 1329056013170182979871503)
                    ·
                      rfl

theorem cell22_3882491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_3882491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882491 prefixEnd_3882491 := by exact prefixLift 3882491
  have htrace : WordTrace (prefixWord ++ tailWord_3882491) baseStart_3882491 baseEnd_3882491 := by
    simpa [prefixWord, tailWord_3882491, baseEnd_3882491] using wordTrace_append hprefix tailTrace_3882491
  have hstable : (prefixWord ++ tailWord_3882491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882491).length < 2 ^ (prefixWord ++ tailWord_3882491).sum := by decide
  have hdescent : baseEnd_3882491 < baseStart_3882491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882557 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3882557 : Nat := 118140960795 + 3882557 * 2 ^ 59
def prefixEnd_3882557 : Nat := 4983230072969 + 3 ^ 40 * 3882557 * 2
def baseEnd_3882557 : Nat := 1329078606318980807721301

theorem tailTrace_3882557 : CollatzResearch.WordTrace tailWord_3882557 prefixEnd_3882557 1329078606318980807721301 := by
  unfold tailWord_3882557
  simp only [CollatzResearch.WordTrace]
  refine ⟨141608487395166551789581925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94405658263444367859721283 141608487395166551789581925)
  ·
    refine ⟨26551591386593728460546611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141608487395166551789581925 26551591386593728460546611)
    ·
      refine ⟨39827387079890592690819917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26551591386593728460546611 39827387079890592690819917)
      ·
        refine ⟨14935270154958972259057469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39827387079890592690819917 14935270154958972259057469)
        ·
          refine ⟨5600726308109614597146551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14935270154958972259057469 5600726308109614597146551)
          ·
            refine ⟨8401089462164421895719827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600726308109614597146551 8401089462164421895719827)
            ·
              refine ⟨12601634193246632843579741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401089462164421895719827 12601634193246632843579741)
              ·
                refine ⟨4725612822467487316342403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12601634193246632843579741 4725612822467487316342403)
                ·
                  refine ⟨7088419233701230974513605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725612822467487316342403 7088419233701230974513605)
                  ·
                    refine ⟨1329078606318980807721301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7088419233701230974513605 1329078606318980807721301)
                    ·
                      rfl

theorem cell22_3882557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3882557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882557 prefixEnd_3882557 := by exact prefixLift 3882557
  have htrace : WordTrace (prefixWord ++ tailWord_3882557) baseStart_3882557 baseEnd_3882557 := by
    simpa [prefixWord, tailWord_3882557, baseEnd_3882557] using wordTrace_append hprefix tailTrace_3882557
  have hstable : (prefixWord ++ tailWord_3882557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882557).length < 2 ^ (prefixWord ++ tailWord_3882557).sum := by decide
  have hdescent : baseEnd_3882557 < baseStart_3882557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882570 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_3882570 : Nat := 118140960795 + 3882570 * 2 ^ 59
def prefixEnd_3882570 : Nat := 4983230072969 + 3 ^ 40 * 3882570 * 2
def baseEnd_3882570 : Nat := 1329083056484653107146261

theorem tailTrace_3882570 : CollatzResearch.WordTrace tailWord_3882570 prefixEnd_3882570 1329083056484653107146261 := by
  unfold tailWord_3882570
  simp only [CollatzResearch.WordTrace]
  refine ⟨35402240386029863752451291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94405974362746303339870109 35402240386029863752451291)
  ·
    refine ⟨53103360579044795628676937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35402240386029863752451291 53103360579044795628676937)
    ·
      refine ⟨39827520434283596721507703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53103360579044795628676937 39827520434283596721507703)
      ·
        refine ⟨59741280651425395082261555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39827520434283596721507703 59741280651425395082261555)
        ·
          refine ⟨89611920977138092623392333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59741280651425395082261555 89611920977138092623392333)
          ·
            refine ⟨33604470366426784733772125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89611920977138092623392333 33604470366426784733772125)
            ·
              refine ⟨12601676387410044275164547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33604470366426784733772125 12601676387410044275164547)
              ·
                refine ⟨18902514581115066412746821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12601676387410044275164547 18902514581115066412746821)
                ·
                  refine ⟨3544221483959074952390029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18902514581115066412746821 3544221483959074952390029)
                  ·
                    refine ⟨1329083056484653107146261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544221483959074952390029 1329083056484653107146261)
                    ·
                      rfl

theorem cell22_3882570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_3882570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882570 prefixEnd_3882570 := by exact prefixLift 3882570
  have htrace : WordTrace (prefixWord ++ tailWord_3882570) baseStart_3882570 baseEnd_3882570 := by
    simpa [prefixWord, tailWord_3882570, baseEnd_3882570] using wordTrace_append hprefix tailTrace_3882570
  have hstable : (prefixWord ++ tailWord_3882570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882570).length < 2 ^ (prefixWord ++ tailWord_3882570).sum := by decide
  have hdescent : baseEnd_3882570 < baseStart_3882570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882600 : List Nat := [2, 1, 4, 3, 1, 2, 1, 8]
def baseStart_3882600 : Nat := 118140960795 + 3882600 * 2 ^ 59
def prefixEnd_3882600 : Nat := 4983230072969 + 3 ^ 40 * 3882600 * 2
def baseEnd_3882600 : Nat := 147677036233082558766241

theorem tailTrace_3882600 : CollatzResearch.WordTrace tailWord_3882600 prefixEnd_3882600 147677036233082558766241 := by
  unfold tailWord_3882600
  simp only [CollatzResearch.WordTrace]
  refine ⟨70805027867005385066698627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94406703822673846755598169 70805027867005385066698627)
  ·
    refine ⟨106207541800508077600047941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70805027867005385066698627 106207541800508077600047941)
    ·
      refine ⟨19913914087595264550008989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106207541800508077600047941 19913914087595264550008989)
      ·
        refine ⟨7467717782848224206253371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19913914087595264550008989 7467717782848224206253371)
        ·
          refine ⟨11201576674272336309380057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467717782848224206253371 11201576674272336309380057)
          ·
            refine ⟨8401182505704252232035043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11201576674272336309380057 8401182505704252232035043)
            ·
              refine ⟨12601773758556378348052565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401182505704252232035043 12601773758556378348052565)
              ·
                refine ⟨147677036233082558766241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12601773758556378348052565 147677036233082558766241)
                ·
                  rfl

theorem cell22_3882600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_3882600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882600 prefixEnd_3882600 := by exact prefixLift 3882600
  have htrace : WordTrace (prefixWord ++ tailWord_3882600) baseStart_3882600 baseEnd_3882600 := by
    simpa [prefixWord, tailWord_3882600, baseEnd_3882600] using wordTrace_append hprefix tailTrace_3882600
  have hstable : (prefixWord ++ tailWord_3882600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882600).length < 2 ^ (prefixWord ++ tailWord_3882600).sum := by decide
  have hdescent : baseEnd_3882600 < baseStart_3882600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882606 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_3882606 : Nat := 118140960795 + 3882606 * 2 ^ 59
def prefixEnd_3882606 : Nat := 4983230072969 + 3 ^ 40 * 3882606 * 2
def baseEnd_3882606 : Nat := 443031793340120337748717

theorem tailTrace_3882606 : CollatzResearch.WordTrace tailWord_3882606 prefixEnd_3882606 443031793340120337748717 := by
  unfold tailWord_3882606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701284321498629144764459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94406849714659355438743781 17701284321498629144764459)
  ·
    refine ⟨26551926482247943717146689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17701284321498629144764459 26551926482247943717146689)
    ·
      refine ⟨19913944861685957787860017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26551926482247943717146689 19913944861685957787860017)
      ·
        refine ⟨14935458646264468340895013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19913944861685957787860017 14935458646264468340895013)
        ·
          refine ⟨2800398496174587813917815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14935458646264468340895013 2800398496174587813917815)
          ·
            refine ⟨4200597744261881720876723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800398496174587813917815 4200597744261881720876723)
            ·
              refine ⟨6300896616392822581315085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200597744261881720876723 6300896616392822581315085)
              ·
                refine ⟨2362836231147308467993157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6300896616392822581315085 2362836231147308467993157)
                ·
                  refine ⟨443031793340120337748717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362836231147308467993157 443031793340120337748717)
                  ·
                    rfl

theorem cell22_3882606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_3882606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882606 prefixEnd_3882606 := by exact prefixLift 3882606
  have htrace : WordTrace (prefixWord ++ tailWord_3882606) baseStart_3882606 baseEnd_3882606 := by
    simpa [prefixWord, tailWord_3882606, baseEnd_3882606] using wordTrace_append hprefix tailTrace_3882606
  have hstable : (prefixWord ++ tailWord_3882606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882606).length < 2 ^ (prefixWord ++ tailWord_3882606).sum := by decide
  have hdescent : baseEnd_3882606 < baseStart_3882606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882694 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3882694 : Nat := 118140960795 + 3882694 * 2 ^ 59
def prefixEnd_3882694 : Nat := 4983230072969 + 3 ^ 40 * 3882694 * 2
def baseEnd_3882694 : Nat := 1329125504218758117045881

theorem tailTrace_3882694 : CollatzResearch.WordTrace tailWord_3882694 prefixEnd_3882694 1329125504218758117045881 := by
  unfold tailWord_3882694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425421381114694505853723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94408989463780149458212757 4425421381114694505853723)
  ·
    refine ⟨6638132071672041758780585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425421381114694505853723 6638132071672041758780585)
    ·
      refine ⟨4978599053754031319085439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6638132071672041758780585 4978599053754031319085439)
      ·
        refine ⟨7467898580631046978628159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978599053754031319085439 7467898580631046978628159)
        ·
          refine ⟨11201847870946570467942239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467898580631046978628159 11201847870946570467942239)
          ·
            refine ⟨16802771806419855701913359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201847870946570467942239 16802771806419855701913359)
            ·
              refine ⟨25204157709629783552870039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16802771806419855701913359 25204157709629783552870039)
              ·
                refine ⟨37806236564444675329305059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25204157709629783552870039 37806236564444675329305059)
                ·
                  refine ⟨56709354846667012993957589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37806236564444675329305059 56709354846667012993957589)
                  ·
                    refine ⟨1329125504218758117045881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56709354846667012993957589 1329125504218758117045881)
                    ·
                      rfl

theorem cell22_3882694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3882694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882694 prefixEnd_3882694 := by exact prefixLift 3882694
  have htrace : WordTrace (prefixWord ++ tailWord_3882694) baseStart_3882694 baseEnd_3882694 := by
    simpa [prefixWord, tailWord_3882694, baseEnd_3882694] using wordTrace_append hprefix tailTrace_3882694
  have hstable : (prefixWord ++ tailWord_3882694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882694).length < 2 ^ (prefixWord ++ tailWord_3882694).sum := by decide
  have hdescent : baseEnd_3882694 < baseStart_3882694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882705 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3882705 : Nat := 118140960795 + 3882705 * 2 ^ 59
def prefixEnd_3882705 : Nat := 4983230072969 + 3 ^ 40 * 3882705 * 2
def baseEnd_3882705 : Nat := 1329129269743557755020847

theorem tailTrace_3882705 : CollatzResearch.WordTrace tailWord_3882705 prefixEnd_3882705 1329129269743557755020847 := by
  unfold tailWord_3882705
  simp only [CollatzResearch.WordTrace]
  refine ⟨141613885398630373065969569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94409256932420248710646379 141613885398630373065969569)
  ·
    refine ⟨106210414048972779799477177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141613885398630373065969569 106210414048972779799477177)
    ·
      refine ⟨79657810536729584849607883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106210414048972779799477177 79657810536729584849607883)
      ·
        refine ⟨119486715805094377274411825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79657810536729584849607883 119486715805094377274411825)
        ·
          refine ⟨89615036853820782955808869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119486715805094377274411825 89615036853820782955808869)
          ·
            refine ⟨16802819410091396804214163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89615036853820782955808869 16802819410091396804214163)
            ·
              refine ⟨25204229115137095206321245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16802819410091396804214163 25204229115137095206321245)
              ·
                refine ⟨9451585918176410702370467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25204229115137095206321245 9451585918176410702370467)
                ·
                  refine ⟨14177378877264616053555701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451585918176410702370467 14177378877264616053555701)
                  ·
                    refine ⟨1329129269743557755020847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14177378877264616053555701 1329129269743557755020847)
                    ·
                      rfl

theorem cell22_3882705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3882705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882705 prefixEnd_3882705 := by exact prefixLift 3882705
  have htrace : WordTrace (prefixWord ++ tailWord_3882705) baseStart_3882705 baseEnd_3882705 := by
    simpa [prefixWord, tailWord_3882705, baseEnd_3882705] using wordTrace_append hprefix tailTrace_3882705
  have hstable : (prefixWord ++ tailWord_3882705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882705).length < 2 ^ (prefixWord ++ tailWord_3882705).sum := by decide
  have hdescent : baseEnd_3882705 < baseStart_3882705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882756 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_3882756 : Nat := 118140960795 + 3882756 * 2 ^ 59
def prefixEnd_3882756 : Nat := 4983230072969 + 3 ^ 40 * 3882756 * 2
def baseEnd_3882756 : Nat := 1329146728085810621995691

theorem tailTrace_3882756 : CollatzResearch.WordTrace tailWord_3882756 prefixEnd_3882756 1329146728085810621995691 := by
  unfold tailWord_3882756
  simp only [CollatzResearch.WordTrace]
  refine ⟨70807872760722804388038061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94410497014297072517384081 70807872760722804388038061)
  ·
    refine ⟨26552952285271051645514273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70807872760722804388038061 26552952285271051645514273)
    ·
      refine ⟨19914714213953288734135705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26552952285271051645514273 19914714213953288734135705)
      ·
        refine ⟨14936035660464966550601779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19914714213953288734135705 14936035660464966550601779)
        ·
          refine ⟨22404053490697449825902669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14936035660464966550601779 22404053490697449825902669)
          ·
            refine ⟨8401520059011543684713501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22404053490697449825902669 8401520059011543684713501)
            ·
              refine ⟨3150570022129328881767563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8401520059011543684713501 3150570022129328881767563)
              ·
                refine ⟨4725855033193993322651345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150570022129328881767563 4725855033193993322651345)
                ·
                  refine ⟨3544391274895494991988509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725855033193993322651345 3544391274895494991988509)
                  ·
                    refine ⟨1329146728085810621995691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544391274895494991988509 1329146728085810621995691)
                    ·
                      rfl

theorem cell22_3882756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_3882756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882756 prefixEnd_3882756 := by exact prefixLift 3882756
  have htrace : WordTrace (prefixWord ++ tailWord_3882756) baseStart_3882756 baseEnd_3882756 := by
    simpa [prefixWord, tailWord_3882756, baseEnd_3882756] using wordTrace_append hprefix tailTrace_3882756
  have hstable : (prefixWord ++ tailWord_3882756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882756).length < 2 ^ (prefixWord ++ tailWord_3882756).sum := by decide
  have hdescent : baseEnd_3882756 < baseStart_3882756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882780 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_3882780 : Nat := 118140960795 + 3882780 * 2 ^ 59
def prefixEnd_3882780 : Nat := 4983230072969 + 3 ^ 40 * 3882780 * 2
def baseEnd_3882780 : Nat := 443051647925427519798539

theorem tailTrace_3882780 : CollatzResearch.WordTrace tailWord_3882780 prefixEnd_3882780 443051647925427519798539 := by
  unfold tailWord_3882780
  simp only [CollatzResearch.WordTrace]
  refine ⟨70808310436679330437474897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94411080582239107249966529 70808310436679330437474897)
  ·
    refine ⟨53106232827509497828106173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70808310436679330437474897 53106232827509497828106173)
    ·
      refine ⟨19914837310316061685539815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53106232827509497828106173 19914837310316061685539815)
      ·
        refine ⟨29872255965474092528309723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19914837310316061685539815 29872255965474092528309723)
        ·
          refine ⟨44808383948211138792464585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29872255965474092528309723 44808383948211138792464585)
          ·
            refine ⟨33606287961158354094348439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44808383948211138792464585 33606287961158354094348439)
            ·
              refine ⟨50409431941737531141522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33606287961158354094348439 50409431941737531141522659)
              ·
                refine ⟨75614147912606296712283989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50409431941737531141522659 75614147912606296712283989)
                ·
                  refine ⟨443051647925427519798539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75614147912606296712283989 443051647925427519798539)
                  ·
                    rfl

theorem cell22_3882780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_3882780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882780 prefixEnd_3882780 := by exact prefixLift 3882780
  have htrace : WordTrace (prefixWord ++ tailWord_3882780) baseStart_3882780 baseEnd_3882780 := by
    simpa [prefixWord, tailWord_3882780, baseEnd_3882780] using wordTrace_append hprefix tailTrace_3882780
  have hstable : (prefixWord ++ tailWord_3882780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882780).length < 2 ^ (prefixWord ++ tailWord_3882780).sum := by decide
  have hdescent : baseEnd_3882780 < baseStart_3882780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882814 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3882814 : Nat := 118140960795 + 3882814 * 2 ^ 59
def prefixEnd_3882814 : Nat := 4983230072969 + 3 ^ 40 * 3882814 * 2
def baseEnd_3882814 : Nat := 443055527557039268015171

theorem tailTrace_3882814 : CollatzResearch.WordTrace tailWord_3882814 prefixEnd_3882814 443055527557039268015171 := by
  unfold tailWord_3882814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702232619404435585210937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94411907303490323121124997 17702232619404435585210937)
  ·
    refine ⟨13276674464553326688908203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17702232619404435585210937 13276674464553326688908203)
    ·
      refine ⟨19915011696829990033362305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13276674464553326688908203 19915011696829990033362305)
      ·
        refine ⟨14936258772622492525021729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19915011696829990033362305 14936258772622492525021729)
        ·
          refine ⟨11202194079466869393766297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14936258772622492525021729 11202194079466869393766297)
          ·
            refine ⟨8401645559600152045324723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11202194079466869393766297 8401645559600152045324723)
            ·
              refine ⟨12602468339400228067987085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401645559600152045324723 12602468339400228067987085)
              ·
                refine ⟨4725925627275085525495157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12602468339400228067987085 4725925627275085525495157)
                ·
                  refine ⟨443055527557039268015171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725925627275085525495157 443055527557039268015171)
                  ·
                    rfl

theorem cell22_3882814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3882814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882814 prefixEnd_3882814 := by exact prefixLift 3882814
  have htrace : WordTrace (prefixWord ++ tailWord_3882814) baseStart_3882814 baseEnd_3882814 := by
    simpa [prefixWord, tailWord_3882814, baseEnd_3882814] using wordTrace_append hprefix tailTrace_3882814
  have hstable : (prefixWord ++ tailWord_3882814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882814).length < 2 ^ (prefixWord ++ tailWord_3882814).sum := by decide
  have hdescent : baseEnd_3882814 < baseStart_3882814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882825 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 8]
def baseStart_3882825 : Nat := 118140960795 + 3882825 * 2 ^ 59
def prefixEnd_3882825 : Nat := 4983230072969 + 3 ^ 40 * 3882825 * 2
def baseEnd_3882825 : Nat := 443056782731972480673493

theorem tailTrace_3882825 : CollatzResearch.WordTrace tailWord_3882825 prefixEnd_3882825 443056782731972480673493 := by
  unfold tailWord_3882825
  simp only [CollatzResearch.WordTrace]
  refine ⟨141618262158195633560337929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94412174772130422373558619 141618262158195633560337929)
  ·
    refine ⟨106213696618646725170253447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141618262158195633560337929 106213696618646725170253447)
    ·
      refine ⟨159320544927970087755380171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106213696618646725170253447 159320544927970087755380171)
      ·
        refine ⟨238980817391955131633070257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159320544927970087755380171 238980817391955131633070257)
        ·
          refine ⟨179235613043966348724802693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238980817391955131633070257 179235613043966348724802693)
          ·
            refine ⟨33606677445743690385900505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179235613043966348724802693 33606677445743690385900505)
            ·
              refine ⟨25205008084307767789425379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33606677445743690385900505 25205008084307767789425379)
              ·
                refine ⟨37807512126461651684138069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25205008084307767789425379 37807512126461651684138069)
                ·
                  refine ⟨443056782731972480673493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37807512126461651684138069 443056782731972480673493)
                  ·
                    rfl

theorem cell22_3882825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_3882825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882825 prefixEnd_3882825 := by exact prefixLift 3882825
  have htrace : WordTrace (prefixWord ++ tailWord_3882825) baseStart_3882825 baseEnd_3882825 := by
    simpa [prefixWord, tailWord_3882825, baseEnd_3882825] using wordTrace_append hprefix tailTrace_3882825
  have hstable : (prefixWord ++ tailWord_3882825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882825).length < 2 ^ (prefixWord ++ tailWord_3882825).sum := by decide
  have hdescent : baseEnd_3882825 < baseStart_3882825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882857 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_3882857 : Nat := 118140960795 + 3882857 * 2 ^ 59
def prefixEnd_3882857 : Nat := 4983230072969 + 3 ^ 40 * 3882857 * 2
def baseEnd_3882857 : Nat := 1329181302449880025220381

theorem tailTrace_3882857 : CollatzResearch.WordTrace tailWord_3882857 prefixEnd_3882857 1329181302449880025220381 := by
  unfold tailWord_3882857
  simp only [CollatzResearch.WordTrace]
  refine ⟨141619429294079703025502825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94412952862719802017001883 141619429294079703025502825)
  ·
    refine ⟨106214571970559777269127119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141619429294079703025502825 106214571970559777269127119)
    ·
      refine ⟨159321857955839665903690679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106214571970559777269127119 159321857955839665903690679)
      ·
        refine ⟨238982786933759498855536019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159321857955839665903690679 238982786933759498855536019)
        ·
          refine ⟨358474180400639248283304029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238982786933759498855536019 358474180400639248283304029)
          ·
            refine ⟨134427817650239718106239011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358474180400639248283304029 134427817650239718106239011)
            ·
              refine ⟨201641726475359577159358517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134427817650239718106239011 201641726475359577159358517)
              ·
                refine ⟨18903911857064960358689861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201641726475359577159358517 18903911857064960358689861)
                ·
                  refine ⟨3544483473199680067254349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18903911857064960358689861 3544483473199680067254349)
                  ·
                    refine ⟨1329181302449880025220381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544483473199680067254349 1329181302449880025220381)
                    ·
                      rfl

theorem cell22_3882857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_3882857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882857 prefixEnd_3882857 := by exact prefixLift 3882857
  have htrace : WordTrace (prefixWord ++ tailWord_3882857) baseStart_3882857 baseEnd_3882857 := by
    simpa [prefixWord, tailWord_3882857, baseEnd_3882857] using wordTrace_append hprefix tailTrace_3882857
  have hstable : (prefixWord ++ tailWord_3882857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882857).length < 2 ^ (prefixWord ++ tailWord_3882857).sum := by decide
  have hdescent : baseEnd_3882857 < baseStart_3882857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882874 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_3882874 : Nat := 118140960795 + 3882874 * 2 ^ 59
def prefixEnd_3882874 : Nat := 4983230072969 + 3 ^ 40 * 3882874 * 2
def baseEnd_3882874 : Nat := 1329187121897297647545329

theorem tailTrace_3882874 : CollatzResearch.WordTrace tailWord_3882874 prefixEnd_3882874 1329187121897297647545329 := by
  unfold tailWord_3882874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35405012333754528732217919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94413366223345409952581117 35405012333754528732217919)
  ·
    refine ⟨53107518500631793098326879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35405012333754528732217919 53107518500631793098326879)
    ·
      refine ⟨79661277750947689647490319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53107518500631793098326879 79661277750947689647490319)
      ·
        refine ⟨119491916626421534471235479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79661277750947689647490319 119491916626421534471235479)
        ·
          refine ⟨179237874939632301706853219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119491916626421534471235479 179237874939632301706853219)
          ·
            refine ⟨268856812409448452560279829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179237874939632301706853219 268856812409448452560279829)
            ·
              refine ⟨12602663081692896213763117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268856812409448452560279829 12602663081692896213763117)
              ·
                refine ⟨4725998655634836080161169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12602663081692896213763117 4725998655634836080161169)
                ·
                  refine ⟨3544498991726127060120877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725998655634836080161169 3544498991726127060120877)
                  ·
                    refine ⟨1329187121897297647545329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544498991726127060120877 1329187121897297647545329)
                    ·
                      rfl

theorem cell22_3882874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_3882874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882874 prefixEnd_3882874 := by exact prefixLift 3882874
  have htrace : WordTrace (prefixWord ++ tailWord_3882874) baseStart_3882874 baseEnd_3882874 := by
    simpa [prefixWord, tailWord_3882874, baseEnd_3882874] using wordTrace_append hprefix tailTrace_3882874
  have hstable : (prefixWord ++ tailWord_3882874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882874).length < 2 ^ (prefixWord ++ tailWord_3882874).sum := by decide
  have hdescent : baseEnd_3882874 < baseStart_3882874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882904 : List Nat := [2, 1, 2, 6, 1, 1, 9]
def baseStart_3882904 : Nat := 118140960795 + 3882904 * 2 ^ 59
def prefixEnd_3882904 : Nat := 4983230072969 + 3 ^ 40 * 3882904 * 2
def baseEnd_3882904 : Nat := 49229533018903243307231

theorem tailTrace_3882904 : CollatzResearch.WordTrace tailWord_3882904 prefixEnd_3882904 49229533018903243307231 := by
  unfold tailWord_3882904
  simp only [CollatzResearch.WordTrace]
  refine ⟨70810571762454715026231883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94414095683272953368309177 70810571762454715026231883)
  ·
    refine ⟨106215857643682072539347825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70810571762454715026231883 106215857643682072539347825)
    ·
      refine ⟨79661893232761554404510869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106215857643682072539347825 79661893232761554404510869)
      ·
        refine ⟨3734151245285697862711447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79661893232761554404510869 3734151245285697862711447)
        ·
          refine ⟨5601226867928546794067171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734151245285697862711447 5601226867928546794067171)
          ·
            refine ⟨8401840301892820191100757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601226867928546794067171 8401840301892820191100757)
            ·
              refine ⟨49229533018903243307231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8401840301892820191100757 49229533018903243307231)
              ·
                rfl

theorem cell22_3882904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 9].length) (baseStart_3882904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882904 prefixEnd_3882904 := by exact prefixLift 3882904
  have htrace : WordTrace (prefixWord ++ tailWord_3882904) baseStart_3882904 baseEnd_3882904 := by
    simpa [prefixWord, tailWord_3882904, baseEnd_3882904] using wordTrace_append hprefix tailTrace_3882904
  have hstable : (prefixWord ++ tailWord_3882904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882904).length < 2 ^ (prefixWord ++ tailWord_3882904).sum := by decide
  have hdescent : baseEnd_3882904 < baseStart_3882904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882908 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3882908 : Nat := 118140960795 + 3882908 * 2 ^ 59
def prefixEnd_3882908 : Nat := 4983230072969 + 3 ^ 40 * 3882908 * 2
def baseEnd_3882908 : Nat := 1329198760792132892195225

theorem tailTrace_3882908 : CollatzResearch.WordTrace tailWord_3882908 prefixEnd_3882908 1329198760792132892195225 := by
  unfold tailWord_3882908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70810644708447469367804689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94414192944596625823739585 70810644708447469367804689)
  ·
    refine ⟨53107983531335602025853517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70810644708447469367804689 53107983531335602025853517)
    ·
      refine ⟨19915493824250850759695069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53107983531335602025853517 19915493824250850759695069)
      ·
        refine ⟨7468310184094069034885651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19915493824250850759695069 7468310184094069034885651)
        ·
          refine ⟨11202465276141103552328477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7468310184094069034885651 11202465276141103552328477)
          ·
            refine ⟨4200924478552913832123179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11202465276141103552328477 4200924478552913832123179)
            ·
              refine ⟨6301386717829370748184769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200924478552913832123179 6301386717829370748184769)
              ·
                refine ⟨4726040038372028061138577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6301386717829370748184769 4726040038372028061138577)
                ·
                  refine ⟨3544530028779021045853933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4726040038372028061138577 3544530028779021045853933)
                  ·
                    refine ⟨1329198760792132892195225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544530028779021045853933 1329198760792132892195225)
                    ·
                      rfl

theorem cell22_3882908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3882908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882908 prefixEnd_3882908 := by exact prefixLift 3882908
  have htrace : WordTrace (prefixWord ++ tailWord_3882908) baseStart_3882908 baseEnd_3882908 := by
    simpa [prefixWord, tailWord_3882908, baseEnd_3882908] using wordTrace_append hprefix tailTrace_3882908
  have hstable : (prefixWord ++ tailWord_3882908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882908).length < 2 ^ (prefixWord ++ tailWord_3882908).sum := by decide
  have hdescent : baseEnd_3882908 < baseStart_3882908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882970 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_3882970 : Nat := 118140960795 + 3882970 * 2 ^ 59
def prefixEnd_3882970 : Nat := 4983230072969 + 3 ^ 40 * 3882970 * 2
def baseEnd_3882970 : Nat := 1329219984659185397145035

theorem tailTrace_3882970 : CollatzResearch.WordTrace tailWord_3882970 prefixEnd_3882970 1329219984659185397145035 := by
  unfold tailWord_3882970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35405887685667580831091591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94415700495113548882910909 35405887685667580831091591)
  ·
    refine ⟨53108831528501371246637387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35405887685667580831091591 53108831528501371246637387)
    ·
      refine ⟨79663247292752056869956081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53108831528501371246637387 79663247292752056869956081)
      ·
        refine ⟨59747435469564042652467061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79663247292752056869956081 59747435469564042652467061)
        ·
          refine ⟨5601322075271628998668787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59747435469564042652467061 5601322075271628998668787)
          ·
            refine ⟨8401983112907443498003181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601322075271628998668787 8401983112907443498003181)
            ·
              refine ⟨3150743667340291311751193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8401983112907443498003181 3150743667340291311751193)
              ·
                refine ⟨2363057750505218483813395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150743667340291311751193 2363057750505218483813395)
                ·
                  refine ⟨3544586625757827725720093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363057750505218483813395 3544586625757827725720093)
                  ·
                    refine ⟨1329219984659185397145035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544586625757827725720093 1329219984659185397145035)
                    ·
                      rfl

theorem cell22_3882970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_3882970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882970 prefixEnd_3882970 := by exact prefixLift 3882970
  have htrace : WordTrace (prefixWord ++ tailWord_3882970) baseStart_3882970 baseEnd_3882970 := by
    simpa [prefixWord, tailWord_3882970, baseEnd_3882970] using wordTrace_append hprefix tailTrace_3882970
  have hstable : (prefixWord ++ tailWord_3882970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882970).length < 2 ^ (prefixWord ++ tailWord_3882970).sum := by decide
  have hdescent : baseEnd_3882970 < baseStart_3882970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882983 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 5]
def baseStart_3882983 : Nat := 118140960795 + 3882983 * 2 ^ 59
def prefixEnd_3882983 : Nat := 4983230072969 + 3 ^ 40 * 3882983 * 2
def baseEnd_3882983 : Nat := 443074811608285898856665

theorem tailTrace_3882983 : CollatzResearch.WordTrace tailWord_3882983 prefixEnd_3882983 443074811608285898856665 := by
  unfold tailWord_3882983
  simp only [CollatzResearch.WordTrace]
  refine ⟨141624024891623226544589603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94416016594415484363059735 141624024891623226544589603)
  ·
    refine ⟨212436037337434839816884405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141624024891623226544589603 212436037337434839816884405)
    ·
      refine ⟨19915878500384516232832913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212436037337434839816884405 19915878500384516232832913)
      ·
        refine ⟨14936908875288387174624685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19915878500384516232832913 14936908875288387174624685)
        ·
          refine ⟨5601340828233145190484257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14936908875288387174624685 5601340828233145190484257)
          ·
            refine ⟨4201005621174858892863193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5601340828233145190484257 4201005621174858892863193)
            ·
              refine ⟨3150754215881144169647395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201005621174858892863193 3150754215881144169647395)
              ·
                refine ⟨4726131323821716254471093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150754215881144169647395 4726131323821716254471093)
                ·
                  refine ⟨443074811608285898856665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4726131323821716254471093 443074811608285898856665)
                  ·
                    rfl

theorem cell22_3882983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 5].length) (baseStart_3882983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3882983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3882983 prefixEnd_3882983 := by exact prefixLift 3882983
  have htrace : WordTrace (prefixWord ++ tailWord_3882983) baseStart_3882983 baseEnd_3882983 := by
    simpa [prefixWord, tailWord_3882983, baseEnd_3882983] using wordTrace_append hprefix tailTrace_3882983
  have hstable : (prefixWord ++ tailWord_3882983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882983).length < 2 ^ (prefixWord ++ tailWord_3882983).sum := by decide
  have hdescent : baseEnd_3882983 < baseStart_3882983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883007 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_3883007 : Nat := 118140960795 + 3883007 * 2 ^ 59
def prefixEnd_3883007 : Nat := 4983230072969 + 3 ^ 40 * 3883007 * 2
def baseEnd_3883007 : Nat := 1329232650515329633969921

theorem tailTrace_3883007 : CollatzResearch.WordTrace tailWord_3883007 prefixEnd_3883007 1329232650515329633969921 := by
  unfold tailWord_3883007
  simp only [CollatzResearch.WordTrace]
  refine ⟨141624900243536278643463275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94416600162357519095642183 141624900243536278643463275)
  ·
    refine ⟨212437350365304417965194913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141624900243536278643463275 212437350365304417965194913)
    ·
      refine ⟨159328012773978313473896185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212437350365304417965194913 159328012773978313473896185)
      ·
        refine ⟨119496009580483735105422139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159328012773978313473896185 119496009580483735105422139)
        ·
          refine ⟨179244014370725602658133209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119496009580483735105422139 179244014370725602658133209)
          ·
            refine ⟨134433010778044201993599907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179244014370725602658133209 134433010778044201993599907)
            ·
              refine ⟨201649516167066302990399861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134433010778044201993599907 201649516167066302990399861)
              ·
                refine ⟨18904642140662465905349987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201649516167066302990399861 18904642140662465905349987)
                ·
                  refine ⟨28356963210993698858024981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18904642140662465905349987 28356963210993698858024981)
                  ·
                    refine ⟨1329232650515329633969921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28356963210993698858024981 1329232650515329633969921)
                    ·
                      rfl

theorem cell22_3883007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_3883007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883007 prefixEnd_3883007 := by exact prefixLift 3883007
  have htrace : WordTrace (prefixWord ++ tailWord_3883007) baseStart_3883007 baseEnd_3883007 := by
    simpa [prefixWord, tailWord_3883007, baseEnd_3883007] using wordTrace_append hprefix tailTrace_3883007
  have hstable : (prefixWord ++ tailWord_3883007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883007).length < 2 ^ (prefixWord ++ tailWord_3883007).sum := by decide
  have hdescent : baseEnd_3883007 < baseStart_3883007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883009 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3883009 : Nat := 118140960795 + 3883009 * 2 ^ 59
def prefixEnd_3883009 : Nat := 4983230072969 + 3 ^ 40 * 3883009 * 2
def baseEnd_3883009 : Nat := 1329233335156202295419915

theorem tailTrace_3883009 : CollatzResearch.WordTrace tailWord_3883009 prefixEnd_3883009 1329233335156202295419915 := by
  unfold tailWord_3883009
  simp only [CollatzResearch.WordTrace]
  refine ⟨141624973189529032985036081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94416648793019355323357387 141624973189529032985036081)
  ·
    refine ⟨106218729892146774738777061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141624973189529032985036081 106218729892146774738777061)
    ·
      refine ⟨19916011854777520263520699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106218729892146774738777061 19916011854777520263520699)
      ·
        refine ⟨29874017782166280395281049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19916011854777520263520699 29874017782166280395281049)
        ·
          refine ⟨22405513336624710296460787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29874017782166280395281049 22405513336624710296460787)
          ·
            refine ⟨33608270004937065444691181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22405513336624710296460787 33608270004937065444691181)
            ·
              refine ⟨12603101251851399541759193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33608270004937065444691181 12603101251851399541759193)
              ·
                refine ⟨9452325938888549656319395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12603101251851399541759193 9452325938888549656319395)
                ·
                  refine ⟨14178488908332824484479093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9452325938888549656319395 14178488908332824484479093)
                  ·
                    refine ⟨1329233335156202295419915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14178488908332824484479093 1329233335156202295419915)
                    ·
                      rfl

theorem cell22_3883009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3883009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883009 prefixEnd_3883009 := by exact prefixLift 3883009
  have htrace : WordTrace (prefixWord ++ tailWord_3883009) baseStart_3883009 baseEnd_3883009 := by
    simpa [prefixWord, tailWord_3883009, baseEnd_3883009] using wordTrace_append hprefix tailTrace_3883009
  have hstable : (prefixWord ++ tailWord_3883009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883009).length < 2 ^ (prefixWord ++ tailWord_3883009).sum := by decide
  have hdescent : baseEnd_3883009 < baseStart_3883009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883021 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3883021 : Nat := 118140960795 + 3883021 * 2 ^ 59
def prefixEnd_3883021 : Nat := 4983230072969 + 3 ^ 40 * 3883021 * 2
def baseEnd_3883021 : Nat := 1329237443001438264119879

theorem tailTrace_3883021 : CollatzResearch.WordTrace tailWord_3883021 prefixEnd_3883021 1329237443001438264119879 := by
  unfold tailWord_3883021
  simp only [CollatzResearch.WordTrace]
  refine ⟨141625410865485559034472917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94416940576990372689648611 141625410865485559034472917)
  ·
    refine ⟨3319345567159817789870459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141625410865485559034472917 3319345567159817789870459)
    ·
      refine ⟨4979018350739726684805689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319345567159817789870459 4979018350739726684805689)
      ·
        refine ⟨3734263763054795013604267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4979018350739726684805689 3734263763054795013604267)
        ·
          refine ⟨5601395644582192520406401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734263763054795013604267 5601395644582192520406401)
          ·
            refine ⟨4201046733436644390304801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5601395644582192520406401 4201046733436644390304801)
            ·
              refine ⟨3150785050077483292728601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201046733436644390304801 3150785050077483292728601)
              ·
                refine ⟨2363088787558112469546451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150785050077483292728601 2363088787558112469546451)
                ·
                  refine ⟨3544633181337168704319677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363088787558112469546451 3544633181337168704319677)
                  ·
                    refine ⟨1329237443001438264119879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544633181337168704319677 1329237443001438264119879)
                    ·
                      rfl

theorem cell22_3883021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3883021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883021 prefixEnd_3883021 := by exact prefixLift 3883021
  have htrace : WordTrace (prefixWord ++ tailWord_3883021) baseStart_3883021 baseEnd_3883021 := by
    simpa [prefixWord, tailWord_3883021, baseEnd_3883021] using wordTrace_append hprefix tailTrace_3883021
  have hstable : (prefixWord ++ tailWord_3883021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883021).length < 2 ^ (prefixWord ++ tailWord_3883021).sum := by decide
  have hdescent : baseEnd_3883021 < baseStart_3883021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883067 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 9]
def baseStart_3883067 : Nat := 118140960795 + 3883067 * 2 ^ 59
def prefixEnd_3883067 : Nat := 4983230072969 + 3 ^ 40 * 3883067 * 2
def baseEnd_3883067 : Nat := 443084396580503159156579

theorem tailTrace_3883067 : CollatzResearch.WordTrace tailWord_3883067 prefixEnd_3883067 443084396580503159156579 := by
  unfold tailWord_3883067
  simp only [CollatzResearch.WordTrace]
  refine ⟨141627088623318908890647455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94418059082212605927098303 141627088623318908890647455)
  ·
    refine ⟨212440632934978363335971183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141627088623318908890647455 212440632934978363335971183)
    ·
      refine ⟨318660949402467545003956775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212440632934978363335971183 318660949402467545003956775)
      ·
        refine ⟨477991424103701317505935163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318660949402467545003956775 477991424103701317505935163)
        ·
          refine ⟨716987136155551976258902745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477991424103701317505935163 716987136155551976258902745)
          ·
            refine ⟨537740352116663982194177059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716987136155551976258902745 537740352116663982194177059)
            ·
              refine ⟨806610528174995973291265589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537740352116663982194177059 806610528174995973291265589)
              ·
                refine ⟨75619737016405872496056149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806610528174995973291265589 75619737016405872496056149)
                ·
                  refine ⟨443084396580503159156579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75619737016405872496056149 443084396580503159156579)
                  ·
                    rfl

theorem cell22_3883067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_3883067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883067 prefixEnd_3883067 := by exact prefixLift 3883067
  have htrace : WordTrace (prefixWord ++ tailWord_3883067) baseStart_3883067 baseEnd_3883067 := by
    simpa [prefixWord, tailWord_3883067, baseEnd_3883067] using wordTrace_append hprefix tailTrace_3883067
  have hstable : (prefixWord ++ tailWord_3883067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883067).length < 2 ^ (prefixWord ++ tailWord_3883067).sum := by decide
  have hdescent : baseEnd_3883067 < baseStart_3883067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883146 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_3883146 : Nat := 118140960795 + 3883146 * 2 ^ 59
def prefixEnd_3883146 : Nat := 4983230072969 + 3 ^ 40 * 3883146 * 2
def baseEnd_3883146 : Nat := 443093411018659868248165

theorem tailTrace_3883146 : CollatzResearch.WordTrace tailWord_3883146 prefixEnd_3883146 443093411018659868248165 := by
  unfold tailWord_3883146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407492497508176345693323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94419979993355136921848861 35407492497508176345693323)
  ·
    refine ⟨53111238746262264518539985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35407492497508176345693323 53111238746262264518539985)
    ·
      refine ⟨39833429059696698388904989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53111238746262264518539985 39833429059696698388904989)
      ·
        refine ⟨14937535897386261895839371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39833429059696698388904989 14937535897386261895839371)
        ·
          refine ⟨22406303846079392843759057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14937535897386261895839371 22406303846079392843759057)
          ·
            refine ⟨16804727884559544632819293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22406303846079392843759057 16804727884559544632819293)
            ·
              refine ⟨6301772956709829237307235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16804727884559544632819293 6301772956709829237307235)
              ·
                refine ⟨9452659435064743855960853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6301772956709829237307235 9452659435064743855960853)
                ·
                  refine ⟨443093411018659868248165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9452659435064743855960853 443093411018659868248165)
                  ·
                    rfl

theorem cell22_3883146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_3883146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883146 prefixEnd_3883146 := by exact prefixLift 3883146
  have htrace : WordTrace (prefixWord ++ tailWord_3883146) baseStart_3883146 baseEnd_3883146 := by
    simpa [prefixWord, tailWord_3883146, baseEnd_3883146] using wordTrace_append hprefix tailTrace_3883146
  have hstable : (prefixWord ++ tailWord_3883146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883146).length < 2 ^ (prefixWord ++ tailWord_3883146).sum := by decide
  have hdescent : baseEnd_3883146 < baseStart_3883146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883240 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3883240 : Nat := 118140960795 + 3883240 * 2 ^ 59
def prefixEnd_3883240 : Nat := 4983230072969 + 3 ^ 40 * 3883240 * 2
def baseEnd_3883240 : Nat := 1329312411176994692894207

theorem tailTrace_3883240 : CollatzResearch.WordTrace tailWord_3883240 prefixEnd_3883240 1329312411176994692894207 := by
  unfold tailWord_3883240
  simp only [CollatzResearch.WordTrace]
  refine ⟨70816699225846079718347587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94422265634461439624463449 70816699225846079718347587)
  ·
    refine ⟨106225048838769119577521381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70816699225846079718347587 106225048838769119577521381)
    ·
      refine ⟨19917196657269209920785259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106225048838769119577521381 19917196657269209920785259)
      ·
        refine ⟨29875794985903814881177889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19917196657269209920785259 29875794985903814881177889)
        ·
          refine ⟨22406846239427861160883417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29875794985903814881177889 22406846239427861160883417)
          ·
            refine ⟨16805134679570895870662563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22406846239427861160883417 16805134679570895870662563)
            ·
              refine ⟨25207702019356343805993845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16805134679570895870662563 25207702019356343805993845)
              ·
                refine ⟨2363222064314657231811923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25207702019356343805993845 2363222064314657231811923)
                ·
                  refine ⟨3544833096471985847717885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363222064314657231811923 3544833096471985847717885)
                  ·
                    refine ⟨1329312411176994692894207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544833096471985847717885 1329312411176994692894207)
                    ·
                      rfl

theorem cell22_3883240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3883240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883240 prefixEnd_3883240 := by exact prefixLift 3883240
  have htrace : WordTrace (prefixWord ++ tailWord_3883240) baseStart_3883240 baseEnd_3883240 := by
    simpa [prefixWord, tailWord_3883240, baseEnd_3883240] using wordTrace_append hprefix tailTrace_3883240
  have hstable : (prefixWord ++ tailWord_3883240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883240).length < 2 ^ (prefixWord ++ tailWord_3883240).sum := by decide
  have hdescent : baseEnd_3883240 < baseStart_3883240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883281 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 6]
def baseStart_3883281 : Nat := 118140960795 + 3883281 * 2 ^ 59
def prefixEnd_3883281 : Nat := 4983230072969 + 3 ^ 40 * 3883281 * 2
def baseEnd_3883281 : Nat := 443108815438294750873027

theorem tailTrace_3883281 : CollatzResearch.WordTrace tailWord_3883281 prefixEnd_3883281 443108815438294750873027 := by
  unfold tailWord_3883281
  simp only [CollatzResearch.WordTrace]
  refine ⟨141634893844543623438937697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94423262563029082292625131 141634893844543623438937697)
  ·
    refine ⟨106226170383407717579203273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141634893844543623438937697 106226170383407717579203273)
    ·
      refine ⟨79669627787555788184402455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106226170383407717579203273 79669627787555788184402455)
      ·
        refine ⟨119504441681333682276603683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79669627787555788184402455 119504441681333682276603683)
        ·
          refine ⟨179256662522000523414905525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119504441681333682276603683 179256662522000523414905525)
          ·
            refine ⟨16805312111437549070147393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179256662522000523414905525 16805312111437549070147393)
            ·
              refine ⟨12603984083578161802610545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16805312111437549070147393 12603984083578161802610545)
              ·
                refine ⟨9452988062683621351957909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12603984083578161802610545 9452988062683621351957909)
                ·
                  refine ⟨443108815438294750873027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9452988062683621351957909 443108815438294750873027)
                  ·
                    rfl

theorem cell22_3883281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_3883281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883281 prefixEnd_3883281 := by exact prefixLift 3883281
  have htrace : WordTrace (prefixWord ++ tailWord_3883281) baseStart_3883281 baseEnd_3883281 := by
    simpa [prefixWord, tailWord_3883281, baseEnd_3883281] using wordTrace_append hprefix tailTrace_3883281
  have hstable : (prefixWord ++ tailWord_3883281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883281).length < 2 ^ (prefixWord ++ tailWord_3883281).sum := by decide
  have hdescent : baseEnd_3883281 < baseStart_3883281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883311 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 4, 4]
def baseStart_3883311 : Nat := 118140960795 + 3883311 * 2 ^ 59
def prefixEnd_3883311 : Nat := 4983230072969 + 3 ^ 40 * 3883311 * 2
def baseEnd_3883311 : Nat := 1329336715927974174368989

theorem tailTrace_3883311 : CollatzResearch.WordTrace tailWord_3883311 prefixEnd_3883311 1329336715927974174368989 := by
  unfold tailWord_3883311
  simp only [CollatzResearch.WordTrace]
  refine ⟨141635988034434938562529787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94423992022956625708353191 141635988034434938562529787)
  ·
    refine ⟨212453982051652407843794681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141635988034434938562529787 212453982051652407843794681)
    ·
      refine ⟨159340486538739305882846011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212453982051652407843794681 159340486538739305882846011)
      ·
        refine ⟨239010729808108958824269017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159340486538739305882846011 239010729808108958824269017)
        ·
          refine ⟨179258047356081719118201763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239010729808108958824269017 179258047356081719118201763)
          ·
            refine ⟨268887071034122578677302645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179258047356081719118201763 268887071034122578677302645)
            ·
              refine ⟨25208162909448991750997123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268887071034122578677302645 25208162909448991750997123)
              ·
                refine ⟨37812244364173487626495685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25208162909448991750997123 37812244364173487626495685)
                ·
                  refine ⟨7089795818282528929967941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37812244364173487626495685 7089795818282528929967941)
                  ·
                    refine ⟨1329336715927974174368989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7089795818282528929967941 1329336715927974174368989)
                    ·
                      rfl

theorem cell22_3883311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_3883311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883311 prefixEnd_3883311 := by exact prefixLift 3883311
  have htrace : WordTrace (prefixWord ++ tailWord_3883311) baseStart_3883311 baseEnd_3883311 := by
    simpa [prefixWord, tailWord_3883311, baseEnd_3883311] using wordTrace_append hprefix tailTrace_3883311
  have hstable : (prefixWord ++ tailWord_3883311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883311).length < 2 ^ (prefixWord ++ tailWord_3883311).sum := by decide
  have hdescent : baseEnd_3883311 < baseStart_3883311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883315 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 4]
def baseStart_3883315 : Nat := 118140960795 + 3883315 * 2 ^ 59
def prefixEnd_3883315 : Nat := 4983230072969 + 3 ^ 40 * 3883315 * 2
def baseEnd_3883315 : Nat := 443112695069906499089659

theorem tailTrace_3883315 : CollatzResearch.WordTrace tailWord_3883315 prefixEnd_3883315 443112695069906499089659 := by
  unfold tailWord_3883315
  simp only [CollatzResearch.WordTrace]
  refine ⟨141636133926420447245675399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94424089284280298163783599 141636133926420447245675399)
  ·
    refine ⟨212454200889630670868513099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141636133926420447245675399 212454200889630670868513099)
    ·
      refine ⟨318681301334446006302769649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212454200889630670868513099 318681301334446006302769649)
      ·
        refine ⟨239010976000834504727077237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318681301334446006302769649 239010976000834504727077237)
        ·
          refine ⟨22407279000078234818163491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239010976000834504727077237 22407279000078234818163491)
          ·
            refine ⟨33610918500117352227245237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22407279000078234818163491 33610918500117352227245237)
            ·
              refine ⟨3151023609386001771304241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33610918500117352227245237 3151023609386001771304241)
              ·
                refine ⟨2363267707039501328478181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151023609386001771304241 2363267707039501328478181)
                ·
                  refine ⟨443112695069906499089659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363267707039501328478181 443112695069906499089659)
                  ·
                    rfl

theorem cell22_3883315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 4].length) (baseStart_3883315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883315 prefixEnd_3883315 := by exact prefixLift 3883315
  have htrace : WordTrace (prefixWord ++ tailWord_3883315) baseStart_3883315 baseEnd_3883315 := by
    simpa [prefixWord, tailWord_3883315, baseEnd_3883315] using wordTrace_append hprefix tailTrace_3883315
  have hstable : (prefixWord ++ tailWord_3883315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883315).length < 2 ^ (prefixWord ++ tailWord_3883315).sum := by decide
  have hdescent : baseEnd_3883315 < baseStart_3883315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883422 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3883422 : Nat := 118140960795 + 3883422 * 2 ^ 59
def prefixEnd_3883422 : Nat := 4983230072969 + 3 ^ 40 * 3883422 * 2
def baseEnd_3883422 : Nat := 443124904498802294947883

theorem tailTrace_3883422 : CollatzResearch.WordTrace tailWord_3883422 prefixEnd_3883422 443124904498802294947883 := by
  unfold tailWord_3883422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705004567129100564977565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94426691024688536346547013 17705004567129100564977565)
  ·
    refine ⟨6639376712673412711866587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17705004567129100564977565 6639376712673412711866587)
    ·
      refine ⟨9959065069010119067799881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639376712673412711866587 9959065069010119067799881)
      ·
        refine ⟨7469298801757589300849911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9959065069010119067799881 7469298801757589300849911)
        ·
          refine ⟨11203948202636383951274867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469298801757589300849911 11203948202636383951274867)
          ·
            refine ⟨16805922303954575926912301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203948202636383951274867 16805922303954575926912301)
            ·
              refine ⟨6302220863982965972592113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16805922303954575926912301 6302220863982965972592113)
              ·
                refine ⟨4726665647987224479444085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302220863982965972592113 4726665647987224479444085)
                ·
                  refine ⟨443124904498802294947883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4726665647987224479444085 443124904498802294947883)
                  ·
                    rfl

theorem cell22_3883422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3883422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883422 prefixEnd_3883422 := by exact prefixLift 3883422
  have htrace : WordTrace (prefixWord ++ tailWord_3883422) baseStart_3883422 baseEnd_3883422 := by
    simpa [prefixWord, tailWord_3883422, baseEnd_3883422] using wordTrace_append hprefix tailTrace_3883422
  have hstable : (prefixWord ++ tailWord_3883422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883422).length < 2 ^ (prefixWord ++ tailWord_3883422).sum := by decide
  have hdescent : baseEnd_3883422 < baseStart_3883422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883452 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_3883452 : Nat := 118140960795 + 3883452 * 2 ^ 59
def prefixEnd_3883452 : Nat := 4983230072969 + 3 ^ 40 * 3883452 * 2
def baseEnd_3883452 : Nat := 1329384983109496806593557

theorem tailTrace_3883452 : CollatzResearch.WordTrace tailWord_3883452 prefixEnd_3883452 1329384983109496806593557 := by
  unfold tailWord_3883452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70820565363462059821706305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94427420484616079762275073 70820565363462059821706305)
  ·
    refine ⟨53115424022596544866279729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70820565363462059821706305 53115424022596544866279729)
    ·
      refine ⟨39836568016947408649709797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53115424022596544866279729 39836568016947408649709797)
      ·
        refine ⟨7469356503177639121820587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39836568016947408649709797 7469356503177639121820587)
        ·
          refine ⟨11204034754766458682730881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469356503177639121820587 11204034754766458682730881)
          ·
            refine ⟨8403026066074844012048161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11204034754766458682730881 8403026066074844012048161)
            ·
              refine ⟨6302269549556133009036121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8403026066074844012048161 6302269549556133009036121)
              ·
                refine ⟨4726702162167099756777091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302269549556133009036121 4726702162167099756777091)
                ·
                  refine ⟨7090053243250649635165637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726702162167099756777091 7090053243250649635165637)
                  ·
                    refine ⟨1329384983109496806593557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7090053243250649635165637 1329384983109496806593557)
                    ·
                      rfl

theorem cell22_3883452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_3883452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883452 prefixEnd_3883452 := by exact prefixLift 3883452
  have htrace : WordTrace (prefixWord ++ tailWord_3883452) baseStart_3883452 baseEnd_3883452 := by
    simpa [prefixWord, tailWord_3883452, baseEnd_3883452] using wordTrace_append hprefix tailTrace_3883452
  have hstable : (prefixWord ++ tailWord_3883452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883452).length < 2 ^ (prefixWord ++ tailWord_3883452).sum := by decide
  have hdescent : baseEnd_3883452 < baseStart_3883452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883463 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3883463 : Nat := 118140960795 + 3883463 * 2 ^ 59
def prefixEnd_3883463 : Nat := 4983230072969 + 3 ^ 40 * 3883463 * 2
def baseEnd_3883463 : Nat := 1329388748634296444568523

theorem tailTrace_3883463 : CollatzResearch.WordTrace tailWord_3883463 prefixEnd_3883463 1329388748634296444568523 := by
  unfold tailWord_3883463
  simp only [CollatzResearch.WordTrace]
  refine ⟨141641531929884268522063043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94427687953256179014708695 141641531929884268522063043)
  ·
    refine ⟨212462297894826402783094565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141641531929884268522063043 212462297894826402783094565)
    ·
      refine ⟨39836680855279950521830231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212462297894826402783094565 39836680855279950521830231)
      ·
        refine ⟨59755021282919925782745347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39836680855279950521830231 59755021282919925782745347)
        ·
          refine ⟨89632531924379888674118021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59755021282919925782745347 89632531924379888674118021)
          ·
            refine ⟨16806099735821229126397129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89632531924379888674118021 16806099735821229126397129)
            ·
              refine ⟨12604574801865921844797847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16806099735821229126397129 12604574801865921844797847)
              ·
                refine ⟨18906862202798882767196771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604574801865921844797847 18906862202798882767196771)
                ·
                  refine ⟨28360293304198324150795157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18906862202798882767196771 28360293304198324150795157)
                  ·
                    refine ⟨1329388748634296444568523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28360293304198324150795157 1329388748634296444568523)
                    ·
                      rfl

theorem cell22_3883463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3883463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883463 prefixEnd_3883463 := by exact prefixLift 3883463
  have htrace : WordTrace (prefixWord ++ tailWord_3883463) baseStart_3883463 baseEnd_3883463 := by
    simpa [prefixWord, tailWord_3883463, baseEnd_3883463] using wordTrace_append hprefix tailTrace_3883463
  have hstable : (prefixWord ++ tailWord_3883463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883463).length < 2 ^ (prefixWord ++ tailWord_3883463).sum := by decide
  have hdescent : baseEnd_3883463 < baseStart_3883463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883544 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 1, 3]
def baseStart_3883544 : Nat := 118140960795 + 3883544 * 2 ^ 59
def prefixEnd_3883544 : Nat := 4983230072969 + 3 ^ 40 * 3883544 * 2
def baseEnd_3883544 : Nat := 1329416476589639233293275

theorem tailTrace_3883544 : CollatzResearch.WordTrace tailWord_3883544 prefixEnd_3883544 1329416476589639233293275 := by
  unfold tailWord_3883544
  simp only [CollatzResearch.WordTrace]
  refine ⟨70822243121295409677880843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94429657495060546237174457 70822243121295409677880843)
  ·
    refine ⟨106233364681943114516821265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70822243121295409677880843 106233364681943114516821265)
    ·
      refine ⟨79675023511457335887615949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106233364681943114516821265 79675023511457335887615949)
      ·
        refine ⟨29878133816796500957855981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79675023511457335887615949 29878133816796500957855981)
        ·
          refine ⟨11204300181298687859195993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29878133816796500957855981 11204300181298687859195993)
          ·
            refine ⟨8403225135974015894396995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11204300181298687859195993 8403225135974015894396995)
            ·
              refine ⟨12604837703961023841595493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403225135974015894396995 12604837703961023841595493)
              ·
                refine ⟨2363407069492691970299155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12604837703961023841595493 2363407069492691970299155)
                ·
                  refine ⟨3545110604239037955448733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363407069492691970299155 3545110604239037955448733)
                  ·
                    refine ⟨1329416476589639233293275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545110604239037955448733 1329416476589639233293275)
                    ·
                      rfl

theorem cell22_3883544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_3883544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883544 prefixEnd_3883544 := by exact prefixLift 3883544
  have htrace : WordTrace (prefixWord ++ tailWord_3883544) baseStart_3883544 baseEnd_3883544 := by
    simpa [prefixWord, tailWord_3883544, baseEnd_3883544] using wordTrace_append hprefix tailTrace_3883544
  have hstable : (prefixWord ++ tailWord_3883544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883544).length < 2 ^ (prefixWord ++ tailWord_3883544).sum := by decide
  have hdescent : baseEnd_3883544 < baseStart_3883544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883555 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 2, 5]
def baseStart_3883555 : Nat := 118140960795 + 3883555 * 2 ^ 59
def prefixEnd_3883555 : Nat := 4983230072969 + 3 ^ 40 * 3883555 * 2
def baseEnd_3883555 : Nat := 1329420242114438871268241

theorem tailTrace_3883555 : CollatzResearch.WordTrace tailWord_3883555 prefixEnd_3883555 1329420242114438871268241 := by
  unfold tailWord_3883555
  simp only [CollatzResearch.WordTrace]
  refine ⟨141644887445550968234412119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94429924963700645489608079 141644887445550968234412119)
  ·
    refine ⟨212467331168326452351618179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141644887445550968234412119 212467331168326452351618179)
    ·
      refine ⟨318700996752489678527427269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212467331168326452351618179 318700996752489678527427269)
      ·
        refine ⟨59756436891091814723892613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318700996752489678527427269 59756436891091814723892613)
        ·
          refine ⟨11204331917079715260729865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59756436891091814723892613 11204331917079715260729865)
          ·
            refine ⟨8403248937809786445547399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11204331917079715260729865 8403248937809786445547399)
            ·
              refine ⟨12604873406714679668321099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403248937809786445547399 12604873406714679668321099)
              ·
                refine ⟨18907310110072019502481649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604873406714679668321099 18907310110072019502481649)
                ·
                  refine ⟨14180482582554014626861237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18907310110072019502481649 14180482582554014626861237)
                  ·
                    refine ⟨1329420242114438871268241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14180482582554014626861237 1329420242114438871268241)
                    ·
                      rfl

theorem cell22_3883555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_3883555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883555 prefixEnd_3883555 := by exact prefixLift 3883555
  have htrace : WordTrace (prefixWord ++ tailWord_3883555) baseStart_3883555 baseEnd_3883555 := by
    simpa [prefixWord, tailWord_3883555, baseEnd_3883555] using wordTrace_append hprefix tailTrace_3883555
  have hstable : (prefixWord ++ tailWord_3883555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883555).length < 2 ^ (prefixWord ++ tailWord_3883555).sum := by decide
  have hdescent : baseEnd_3883555 < baseStart_3883555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883568 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_3883568 : Nat := 118140960795 + 3883568 * 2 ^ 59
def prefixEnd_3883568 : Nat := 4983230072969 + 3 ^ 40 * 3883568 * 2
def baseEnd_3883568 : Nat := 443141564093370390231067

theorem tailTrace_3883568 : CollatzResearch.WordTrace tailWord_3883568 prefixEnd_3883568 443141564093370390231067 := by
  unfold tailWord_3883568
  simp only [CollatzResearch.WordTrace]
  refine ⟨70822680797251935727317679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94430241063002580969756905 70822680797251935727317679)
  ·
    refine ⟨106234021195877903590976519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70822680797251935727317679 106234021195877903590976519)
    ·
      refine ⟨159351031793816855386464779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106234021195877903590976519 159351031793816855386464779)
      ·
        refine ⟨239026547690725283079697169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159351031793816855386464779 239026547690725283079697169)
        ·
          refine ⟨179269910768043962309772877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239026547690725283079697169 179269910768043962309772877)
          ·
            refine ⟨67226216538016485866164829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179269910768043962309772877 67226216538016485866164829)
            ·
              refine ⟨25209831201756182199811811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67226216538016485866164829 25209831201756182199811811)
              ·
                refine ⟨37814746802634273299717717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25209831201756182199811811 37814746802634273299717717)
                ·
                  refine ⟨443141564093370390231067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37814746802634273299717717 443141564093370390231067)
                  ·
                    rfl

theorem cell22_3883568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_3883568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883568 prefixEnd_3883568 := by exact prefixLift 3883568
  have htrace : WordTrace (prefixWord ++ tailWord_3883568) baseStart_3883568 baseEnd_3883568 := by
    simpa [prefixWord, tailWord_3883568, baseEnd_3883568] using wordTrace_append hprefix tailTrace_3883568
  have hstable : (prefixWord ++ tailWord_3883568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883568).length < 2 ^ (prefixWord ++ tailWord_3883568).sum := by decide
  have hdescent : baseEnd_3883568 < baseStart_3883568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883570 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3883570 : Nat := 118140960795 + 3883570 * 2 ^ 59
def prefixEnd_3883570 : Nat := 4983230072969 + 3 ^ 40 * 3883570 * 2
def baseEnd_3883570 : Nat := 1329425376920983832143195

theorem tailTrace_3883570 : CollatzResearch.WordTrace tailWord_3883570 prefixEnd_3883570 1329425376920983832143195 := by
  unfold tailWord_3883570
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411358635124156449052041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94430289693664417197472109 35411358635124156449052041)
  ·
    refine ⟨26558518976343117336789031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35411358635124156449052041 26558518976343117336789031)
    ·
      refine ⟨39837778464514676005183547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26558518976343117336789031 39837778464514676005183547)
      ·
        refine ⟨59756667696772014007775321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39837778464514676005183547 59756667696772014007775321)
        ·
          refine ⟨44817500772579010505831491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59756667696772014007775321 44817500772579010505831491)
          ·
            refine ⟨67226251158868515758747237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44817500772579010505831491 67226251158868515758747237)
            ·
              refine ⟨12604922092287846704765107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67226251158868515758747237 12604922092287846704765107)
              ·
                refine ⟨18907383138431770057147661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604922092287846704765107 18907383138431770057147661)
                ·
                  refine ⟨7090268676911913771430373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18907383138431770057147661 7090268676911913771430373)
                  ·
                    refine ⟨1329425376920983832143195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7090268676911913771430373 1329425376920983832143195)
                    ·
                      rfl

theorem cell22_3883570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3883570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883570 prefixEnd_3883570 := by exact prefixLift 3883570
  have htrace : WordTrace (prefixWord ++ tailWord_3883570) baseStart_3883570 baseEnd_3883570 := by
    simpa [prefixWord, tailWord_3883570, baseEnd_3883570] using wordTrace_append hprefix tailTrace_3883570
  have hstable : (prefixWord ++ tailWord_3883570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883570).length < 2 ^ (prefixWord ++ tailWord_3883570).sum := by decide
  have hdescent : baseEnd_3883570 < baseStart_3883570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883602 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_3883602 : Nat := 118140960795 + 3883602 * 2 ^ 59
def prefixEnd_3883602 : Nat := 4983230072969 + 3 ^ 40 * 3883602 * 2
def baseEnd_3883602 : Nat := 443145443724982138447699

theorem tailTrace_3883602 : CollatzResearch.WordTrace tailWord_3883602 prefixEnd_3883602 443145443724982138447699 := by
  unfold tailWord_3883602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411650419095173815343265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94431067784253796840915373 35411650419095173815343265)
  ·
    refine ⟨26558737814321380361507449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35411650419095173815343265 26558737814321380361507449)
    ·
      refine ⟨19919053360741035271130587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26558737814321380361507449 19919053360741035271130587)
      ·
        refine ⟨29878580041111552906695881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19919053360741035271130587 29878580041111552906695881)
        ·
          refine ⟨22408935030833664680021911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29878580041111552906695881 22408935030833664680021911)
          ·
            refine ⟨33613402546250497020032867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22408935030833664680021911 33613402546250497020032867)
            ·
              refine ⟨50420103819375745530049301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33613402546250497020032867 50420103819375745530049301)
              ·
                refine ⟨2363442366533238071721061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50420103819375745530049301 2363442366533238071721061)
                ·
                  refine ⟨443145443724982138447699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363442366533238071721061 443145443724982138447699)
                  ·
                    rfl

theorem cell22_3883602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_3883602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883602 prefixEnd_3883602 := by exact prefixLift 3883602
  have htrace : WordTrace (prefixWord ++ tailWord_3883602) baseStart_3883602 baseEnd_3883602 := by
    simpa [prefixWord, tailWord_3883602, baseEnd_3883602] using wordTrace_append hprefix tailTrace_3883602
  have hstable : (prefixWord ++ tailWord_3883602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883602).length < 2 ^ (prefixWord ++ tailWord_3883602).sum := by decide
  have hdescent : baseEnd_3883602 < baseStart_3883602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883617 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3883617 : Nat := 118140960795 + 3883617 * 2 ^ 59
def prefixEnd_3883617 : Nat := 4983230072969 + 3 ^ 40 * 3883617 * 2
def baseEnd_3883617 : Nat := 1329441465981491376218051

theorem tailTrace_3883617 : CollatzResearch.WordTrace tailWord_3883617 prefixEnd_3883617 1329441465981491376218051 := by
  unfold tailWord_3883617
  simp only [CollatzResearch.WordTrace]
  refine ⟨141647148771326352823169105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94431432514217568548779403 141647148771326352823169105)
  ·
    refine ⟨106235361578494764617376829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141647148771326352823169105 106235361578494764617376829)
    ·
      refine ⟨39838260591935536731516311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106235361578494764617376829 39838260591935536731516311)
      ·
        refine ⟨59757390887903305097274467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39838260591935536731516311 59757390887903305097274467)
        ·
          refine ⟨89636086331854957645911701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59757390887903305097274467 89636086331854957645911701)
          ·
            refine ⟨4201691546805701139652111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89636086331854957645911701 4201691546805701139652111)
            ·
              refine ⟨6302537320208551709478167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201691546805701139652111 6302537320208551709478167)
              ·
                refine ⟨9453805980312827564217251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302537320208551709478167 9453805980312827564217251)
                ·
                  refine ⟨14180708970469241346325877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9453805980312827564217251 14180708970469241346325877)
                  ·
                    refine ⟨1329441465981491376218051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14180708970469241346325877 1329441465981491376218051)
                    ·
                      rfl

theorem cell22_3883617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3883617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883617 prefixEnd_3883617 := by exact prefixLift 3883617
  have htrace : WordTrace (prefixWord ++ tailWord_3883617) baseStart_3883617 baseEnd_3883617 := by
    simpa [prefixWord, tailWord_3883617, baseEnd_3883617] using wordTrace_append hprefix tailTrace_3883617
  have hstable : (prefixWord ++ tailWord_3883617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883617).length < 2 ^ (prefixWord ++ tailWord_3883617).sum := by decide
  have hdescent : baseEnd_3883617 < baseStart_3883617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883668 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3883668 : Nat := 118140960795 + 3883668 * 2 ^ 59
def prefixEnd_3883668 : Nat := 4983230072969 + 3 ^ 40 * 3883668 * 2
def baseEnd_3883668 : Nat := 1329458924323744243192895

theorem tailTrace_3883668 : CollatzResearch.WordTrace tailWord_3883668 prefixEnd_3883668 1329458924323744243192895 := by
  unfold tailWord_3883668
  simp only [CollatzResearch.WordTrace]
  refine ⟨70824504447070794266637829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94432672596094392355517105 70824504447070794266637829)
  ·
    refine ⟨13279594583825773924994593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70824504447070794266637829 13279594583825773924994593)
    ·
      refine ⟨9959695937869330443745945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13279594583825773924994593 9959695937869330443745945)
      ·
        refine ⟨7469771953401997832809459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9959695937869330443745945 7469771953401997832809459)
        ·
          refine ⟨11204657930102996749214189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469771953401997832809459 11204657930102996749214189)
          ·
            refine ⟨4201746723788623780955321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11204657930102996749214189 4201746723788623780955321)
            ·
              refine ⟨3151310042841467835716491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201746723788623780955321 3151310042841467835716491)
              ·
                refine ⟨4726965064262201753574737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151310042841467835716491 4726965064262201753574737)
                ·
                  refine ⟨3545223798196651315181053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4726965064262201753574737 3545223798196651315181053)
                  ·
                    refine ⟨1329458924323744243192895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545223798196651315181053 1329458924323744243192895)
                    ·
                      rfl

theorem cell22_3883668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3883668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883668 prefixEnd_3883668 := by exact prefixLift 3883668
  have htrace : WordTrace (prefixWord ++ tailWord_3883668) baseStart_3883668 baseEnd_3883668 := by
    simpa [prefixWord, tailWord_3883668, baseEnd_3883668] using wordTrace_append hprefix tailTrace_3883668
  have hstable : (prefixWord ++ tailWord_3883668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883668).length < 2 ^ (prefixWord ++ tailWord_3883668).sum := by decide
  have hdescent : baseEnd_3883668 < baseStart_3883668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883722 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3883722 : Nat := 118140960795 + 3883722 * 2 ^ 59
def prefixEnd_3883722 : Nat := 4983230072969 + 3 ^ 40 * 3883722 * 2
def baseEnd_3883722 : Nat := 1329477409627306102342729

theorem tailTrace_3883722 : CollatzResearch.WordTrace tailWord_3883722 prefixEnd_3883722 1329477409627306102342729 := by
  unfold tailWord_3883722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412744608986488938935355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94433985623963970503827613 35412744608986488938935355)
  ·
    refine ⟨53119116913479733408403033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35412744608986488938935355 53119116913479733408403033)
    ·
      refine ⟨39839337685109800056302275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53119116913479733408403033 39839337685109800056302275)
      ·
        refine ⟨59759006527664700084453413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39839337685109800056302275 59759006527664700084453413)
        ·
          refine ⟨11204813723937131265835015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59759006527664700084453413 11204813723937131265835015)
          ·
            refine ⟨16807220585905696898752523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11204813723937131265835015 16807220585905696898752523)
            ·
              refine ⟨25210830878858545348128785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16807220585905696898752523 25210830878858545348128785)
              ·
                refine ⟨18908123159143909011096589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25210830878858545348128785 18908123159143909011096589)
                ·
                  refine ⟨7090546184678965879161221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18908123159143909011096589 7090546184678965879161221)
                  ·
                    refine ⟨1329477409627306102342729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7090546184678965879161221 1329477409627306102342729)
                    ·
                      rfl

theorem cell22_3883722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3883722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883722 prefixEnd_3883722 := by exact prefixLift 3883722
  have htrace : WordTrace (prefixWord ++ tailWord_3883722) baseStart_3883722 baseEnd_3883722 := by
    simpa [prefixWord, tailWord_3883722, baseEnd_3883722] using wordTrace_append hprefix tailTrace_3883722
  have hstable : (prefixWord ++ tailWord_3883722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883722).length < 2 ^ (prefixWord ++ tailWord_3883722).sum := by decide
  have hdescent : baseEnd_3883722 < baseStart_3883722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883786 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_3883786 : Nat := 118140960795 + 3883786 * 2 ^ 59
def prefixEnd_3883786 : Nat := 4983230072969 + 3 ^ 40 * 3883786 * 2
def baseEnd_3883786 : Nat := 1329499318135231268742533

theorem tailTrace_3883786 : CollatzResearch.WordTrace tailWord_3883786 prefixEnd_3883786 1329499318135231268742533 := by
  unfold tailWord_3883786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35413328176928523671517803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94435541805142729790714141 35413328176928523671517803)
  ·
    refine ⟨53119992265392785507276705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35413328176928523671517803 53119992265392785507276705)
    ·
      refine ⟨39839994199044589130457529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53119992265392785507276705 39839994199044589130457529)
      ·
        refine ⟨29879995649283441847843147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39839994199044589130457529 29879995649283441847843147)
        ·
          refine ⟨44819993473925162771764721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29879995649283441847843147 44819993473925162771764721)
          ·
            refine ⟨33614995105443872078823541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44819993473925162771764721 33614995105443872078823541)
            ·
              refine ⟨3151405791135363007389707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33614995105443872078823541 3151405791135363007389707)
              ·
                refine ⟨4727108686703044511084561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151405791135363007389707 4727108686703044511084561)
                ·
                  refine ⟨3545331515027283383313421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727108686703044511084561 3545331515027283383313421)
                  ·
                    refine ⟨1329499318135231268742533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545331515027283383313421 1329499318135231268742533)
                    ·
                      rfl

theorem cell22_3883786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_3883786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883786 prefixEnd_3883786 := by exact prefixLift 3883786
  have htrace : WordTrace (prefixWord ++ tailWord_3883786) baseStart_3883786 baseEnd_3883786 := by
    simpa [prefixWord, tailWord_3883786, baseEnd_3883786] using wordTrace_append hprefix tailTrace_3883786
  have hstable : (prefixWord ++ tailWord_3883786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883786).length < 2 ^ (prefixWord ++ tailWord_3883786).sum := by decide
  have hdescent : baseEnd_3883786 < baseStart_3883786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883805 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 4]
def baseStart_3883805 : Nat := 118140960795 + 3883805 * 2 ^ 59
def prefixEnd_3883805 : Nat := 4983230072969 + 3 ^ 40 * 3883805 * 2
def baseEnd_3883805 : Nat := 443168607407840517505825

theorem tailTrace_3883805 : CollatzResearch.WordTrace tailWord_3883805 prefixEnd_3883805 443168607407840517505825 := by
  unfold tailWord_3883805
  simp only [CollatzResearch.WordTrace]
  refine ⟨141654005694645260931012869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94436003796430173954008579 141654005694645260931012869)
  ·
    refine ⟨26560126067745986424564913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141654005694645260931012869 26560126067745986424564913)
    ·
      refine ⟨19920094550809489818423685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26560126067745986424564913 19920094550809489818423685)
      ·
        refine ⟨3735017728276779340954441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19920094550809489818423685 3735017728276779340954441)
        ·
          refine ⟨2801263296207584505715831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3735017728276779340954441 2801263296207584505715831)
          ·
            refine ⟨4201894944311376758573747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801263296207584505715831 4201894944311376758573747)
            ·
              refine ⟨6302842416467065137860621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201894944311376758573747 6302842416467065137860621)
              ·
                refine ⟨2363565906175149426697733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6302842416467065137860621 2363565906175149426697733)
                ·
                  refine ⟨443168607407840517505825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363565906175149426697733 443168607407840517505825)
                  ·
                    rfl

theorem cell22_3883805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_3883805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883805 prefixEnd_3883805 := by exact prefixLift 3883805
  have htrace : WordTrace (prefixWord ++ tailWord_3883805) baseStart_3883805 baseEnd_3883805 := by
    simpa [prefixWord, tailWord_3883805, baseEnd_3883805] using wordTrace_append hprefix tailTrace_3883805
  have hstable : (prefixWord ++ tailWord_3883805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883805).length < 2 ^ (prefixWord ++ tailWord_3883805).sum := by decide
  have hdescent : baseEnd_3883805 < baseStart_3883805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883827 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 7]
def baseStart_3883827 : Nat := 118140960795 + 3883827 * 2 ^ 59
def prefixEnd_3883827 : Nat := 4983230072969 + 3 ^ 40 * 3883827 * 2
def baseEnd_3883827 : Nat := 443171117757706942822469

theorem tailTrace_3883827 : CollatzResearch.WordTrace tailWord_3883827 prefixEnd_3883827 443171117757706942822469 := by
  unfold tailWord_3883827
  simp only [CollatzResearch.WordTrace]
  refine ⟨141654808100565558688313735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94436538733710372458875823 141654808100565558688313735)
  ·
    refine ⟨212482212150848338032470603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141654808100565558688313735 212482212150848338032470603)
    ·
      refine ⟨318723318226272507048705905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212482212150848338032470603 318723318226272507048705905)
      ·
        refine ⟨239042488669704380286529429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318723318226272507048705905 239042488669704380286529429)
        ·
          refine ⟨11205116656392392825931067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239042488669704380286529429 11205116656392392825931067)
          ·
            refine ⟨16807674984588589238896601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205116656392392825931067 16807674984588589238896601)
            ·
              refine ⟨12605756238441441929172451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16807674984588589238896601 12605756238441441929172451)
              ·
                refine ⟨18908634357662162893758677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12605756238441441929172451 18908634357662162893758677)
                ·
                  refine ⟨443171117757706942822469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18908634357662162893758677 443171117757706942822469)
                  ·
                    rfl

theorem cell22_3883827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_3883827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883827 prefixEnd_3883827 := by exact prefixLift 3883827
  have htrace : WordTrace (prefixWord ++ tailWord_3883827) baseStart_3883827 baseEnd_3883827 := by
    simpa [prefixWord, tailWord_3883827, baseEnd_3883827] using wordTrace_append hprefix tailTrace_3883827
  have hstable : (prefixWord ++ tailWord_3883827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883827).length < 2 ^ (prefixWord ++ tailWord_3883827).sum := by decide
  have hdescent : baseEnd_3883827 < baseStart_3883827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883938 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3883938 : Nat := 118140960795 + 3883938 * 2 ^ 59
def prefixEnd_3883938 : Nat := 4983230072969 + 3 ^ 40 * 3883938 * 2
def baseEnd_3883938 : Nat := 1329551350841553538942067

theorem tailTrace_3883938 : CollatzResearch.WordTrace tailWord_3883938 prefixEnd_3883938 1329551350841553538942067 := by
  unfold tailWord_3883938
  simp only [CollatzResearch.WordTrace]
  refine ⟨35414714150790856161401117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94439237735442283097069645 35414714150790856161401117)
  ·
    refine ⟨13280517806546571060525419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35414714150790856161401117 13280517806546571060525419)
    ·
      refine ⟨19920776709819856590788129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13280517806546571060525419 19920776709819856590788129)
      ·
        refine ⟨14940582532364892443091097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19920776709819856590788129 14940582532364892443091097)
        ·
          refine ⟨11205436899273669332318323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14940582532364892443091097 11205436899273669332318323)
          ·
            refine ⟨16808155348910503998477485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205436899273669332318323 16808155348910503998477485)
            ·
              refine ⟨6303058255841438999429057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16808155348910503998477485 6303058255841438999429057)
              ·
                refine ⟨4727293691881079249571793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303058255841438999429057 4727293691881079249571793)
                ·
                  refine ⟨3545470268910809437178845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727293691881079249571793 3545470268910809437178845)
                  ·
                    refine ⟨1329551350841553538942067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545470268910809437178845 1329551350841553538942067)
                    ·
                      rfl

theorem cell22_3883938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3883938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883938 prefixEnd_3883938 := by exact prefixLift 3883938
  have htrace : WordTrace (prefixWord ++ tailWord_3883938) baseStart_3883938 baseEnd_3883938 := by
    simpa [prefixWord, tailWord_3883938, baseEnd_3883938] using wordTrace_append hprefix tailTrace_3883938
  have hstable : (prefixWord ++ tailWord_3883938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883938).length < 2 ^ (prefixWord ++ tailWord_3883938).sum := by decide
  have hdescent : baseEnd_3883938 < baseStart_3883938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883966 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3883966 : Nat := 118140960795 + 3883966 * 2 ^ 59
def prefixEnd_3883966 : Nat := 4983230072969 + 3 ^ 40 * 3883966 * 2
def baseEnd_3883966 : Nat := 1329560935813770799241981

theorem tailTrace_3883966 : CollatzResearch.WordTrace tailWord_3883966 prefixEnd_3883966 1329560935813770799241981 := by
  unfold tailWord_3883966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17707484730882748178452969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94439918564707990285082501 17707484730882748178452969)
  ·
    refine ⟨13280613548162061133839727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17707484730882748178452969 13280613548162061133839727)
    ·
      refine ⟨19920920322243091700759591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13280613548162061133839727 19920920322243091700759591)
      ·
        refine ⟨29881380483364637551139387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19920920322243091700759591 29881380483364637551139387)
        ·
          refine ⟨44822070725046956326709081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29881380483364637551139387 44822070725046956326709081)
          ·
            refine ⟨33616553043785217245031811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44822070725046956326709081 33616553043785217245031811)
            ·
              refine ⟨50424829565677825867547717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33616553043785217245031811 50424829565677825867547717)
              ·
                refine ⟨9454655543564592350165197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50424829565677825867547717 9454655543564592350165197)
                ·
                  refine ⟨3545495828836722131311949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9454655543564592350165197 3545495828836722131311949)
                  ·
                    refine ⟨1329560935813770799241981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545495828836722131311949 1329560935813770799241981)
                    ·
                      rfl

theorem cell22_3883966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3883966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883966 prefixEnd_3883966 := by exact prefixLift 3883966
  have htrace : WordTrace (prefixWord ++ tailWord_3883966) baseStart_3883966 baseEnd_3883966 := by
    simpa [prefixWord, tailWord_3883966, baseEnd_3883966] using wordTrace_append hprefix tailTrace_3883966
  have hstable : (prefixWord ++ tailWord_3883966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883966).length < 2 ^ (prefixWord ++ tailWord_3883966).sum := by decide
  have hdescent : baseEnd_3883966 < baseStart_3883966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883983 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 1, 3]
def baseStart_3883983 : Nat := 118140960795 + 3883983 * 2 ^ 59
def prefixEnd_3883983 : Nat := 4983230072969 + 3 ^ 40 * 3883983 * 2
def baseEnd_3883983 : Nat := 1329566755261188421566929

theorem tailTrace_3883983 : CollatzResearch.WordTrace tailWord_3883983 prefixEnd_3883983 1329566755261188421566929 := by
  unfold tailWord_3883983
  simp only [CollatzResearch.WordTrace]
  refine ⟨141660497888000397330992603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94440331925333598220661735 141660497888000397330992603)
  ·
    refine ⟨212490746832000595996488905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141660497888000397330992603 212490746832000595996488905)
    ·
      refine ⟨159368060124000446997366679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212490746832000595996488905 159368060124000446997366679)
      ·
        refine ⟨239052090186000670496050019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159368060124000446997366679 239052090186000670496050019)
        ·
          refine ⟨358578135279001005744075029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239052090186000670496050019 358578135279001005744075029)
          ·
            refine ⟨16808350091203172144253517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358578135279001005744075029 16808350091203172144253517)
            ·
              refine ⟨6303131284201189554095069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16808350091203172144253517 6303131284201189554095069)
              ·
                refine ⟨2363674231575446082785651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6303131284201189554095069 2363674231575446082785651)
                ·
                  refine ⟨3545511347363169124178477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363674231575446082785651 3545511347363169124178477)
                  ·
                    refine ⟨1329566755261188421566929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545511347363169124178477 1329566755261188421566929)
                    ·
                      rfl

theorem cell22_3883983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_3883983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3883983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3883983 prefixEnd_3883983 := by exact prefixLift 3883983
  have htrace : WordTrace (prefixWord ++ tailWord_3883983) baseStart_3883983 baseEnd_3883983 := by
    simpa [prefixWord, tailWord_3883983, baseEnd_3883983] using wordTrace_append hprefix tailTrace_3883983
  have hstable : (prefixWord ++ tailWord_3883983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883983).length < 2 ^ (prefixWord ++ tailWord_3883983).sum := by decide
  have hdescent : baseEnd_3883983 < baseStart_3883983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884043 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 1, 4]
def baseStart_3884043 : Nat := 118140960795 + 3884043 * 2 ^ 59
def prefixEnd_3884043 : Nat := 4983230072969 + 3 ^ 40 * 3884043 * 2
def baseEnd_3884043 : Nat := 1329587294487368265066745

theorem tailTrace_3884043 : CollatzResearch.WordTrace tailWord_3884043 prefixEnd_3884043 1329587294487368265066745 := by
  unfold tailWord_3884043
  simp only [CollatzResearch.WordTrace]
  refine ⟨141662686267783027578176783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94441790845188685052117855 141662686267783027578176783)
  ·
    refine ⟨212494029401674541367265175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141662686267783027578176783 212494029401674541367265175)
    ·
      refine ⟨318741044102511812050897763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212494029401674541367265175 318741044102511812050897763)
      ·
        refine ⟨478111566153767718076346645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318741044102511812050897763 478111566153767718076346645)
        ·
          refine ⟨22411479663457861784828749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 478111566153767718076346645 22411479663457861784828749)
          ·
            refine ⟨8404304873796698169310781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22411479663457861784828749 8404304873796698169310781)
            ·
              refine ⟨3151614327673761813491543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8404304873796698169310781 3151614327673761813491543)
              ·
                refine ⟨4727421491510642720237315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151614327673761813491543 4727421491510642720237315)
                ·
                  refine ⟨7091132237265964080355973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727421491510642720237315 7091132237265964080355973)
                  ·
                    refine ⟨1329587294487368265066745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091132237265964080355973 1329587294487368265066745)
                    ·
                      rfl

theorem cell22_3884043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 4].length) (baseStart_3884043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884043 prefixEnd_3884043 := by exact prefixLift 3884043
  have htrace : WordTrace (prefixWord ++ tailWord_3884043) baseStart_3884043 baseEnd_3884043 := by
    simpa [prefixWord, tailWord_3884043, baseEnd_3884043] using wordTrace_append hprefix tailTrace_3884043
  have hstable : (prefixWord ++ tailWord_3884043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884043).length < 2 ^ (prefixWord ++ tailWord_3884043).sum := by decide
  have hdescent : baseEnd_3884043 < baseStart_3884043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884088 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_3884088 : Nat := 118140960795 + 3884088 * 2 ^ 59
def prefixEnd_3884088 : Nat := 4983230072969 + 3 ^ 40 * 3884088 * 2
def baseEnd_3884088 : Nat := 1329602698907003147691607

theorem tailTrace_3884088 : CollatzResearch.WordTrace tailWord_3884088 prefixEnd_3884088 1329602698907003147691607 := by
  unfold tailWord_3884088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70832163776310000131782459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94442885035080000175709945 70832163776310000131782459)
  ·
    refine ⟨106248245664465000197673689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70832163776310000131782459 106248245664465000197673689)
    ·
      refine ⟨79686184248348750148255267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106248245664465000197673689 79686184248348750148255267)
      ·
        refine ⟨119529276372523125222382901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79686184248348750148255267 119529276372523125222382901)
        ·
          refine ⟨11205869659924042989598397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119529276372523125222382901 11205869659924042989598397)
          ·
            refine ⟨4202201122471516121099399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11205869659924042989598397 4202201122471516121099399)
            ·
              refine ⟨6303301683707274181649099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202201122471516121099399 6303301683707274181649099)
              ·
                refine ⟨9454952525560911272473649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6303301683707274181649099 9454952525560911272473649)
                ·
                  refine ⟨7091214394170683454355237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9454952525560911272473649 7091214394170683454355237)
                  ·
                    refine ⟨1329602698907003147691607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091214394170683454355237 1329602698907003147691607)
                    ·
                      rfl

theorem cell22_3884088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_3884088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884088 prefixEnd_3884088 := by exact prefixLift 3884088
  have htrace : WordTrace (prefixWord ++ tailWord_3884088) baseStart_3884088 baseEnd_3884088 := by
    simpa [prefixWord, tailWord_3884088, baseEnd_3884088] using wordTrace_append hprefix tailTrace_3884088
  have hstable : (prefixWord ++ tailWord_3884088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884088).length < 2 ^ (prefixWord ++ tailWord_3884088).sum := by decide
  have hdescent : baseEnd_3884088 < baseStart_3884088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884281 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_3884281 : Nat := 118140960795 + 3884281 * 2 ^ 59
def prefixEnd_3884281 : Nat := 4983230072969 + 3 ^ 40 * 3884281 * 2
def baseEnd_3884281 : Nat := 1329668766751214977616015

theorem tailTrace_3884281 : CollatzResearch.WordTrace tailWord_3884281 prefixEnd_3884281 1329668766751214977616015 := by
  unfold tailWord_3884281
  simp only [CollatzResearch.WordTrace]
  refine ⟨141671366840920794225340697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94447577893947196150227131 141671366840920794225340697)
  ·
    refine ⟨106253525130690595669005523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141671366840920794225340697 106253525130690595669005523)
    ·
      refine ⟨159380287696035893503508285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106253525130690595669005523 159380287696035893503508285)
      ·
        refine ⟨59767607886013460063815607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159380287696035893503508285 59767607886013460063815607)
        ·
          refine ⟨89651411829020190095723411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59767607886013460063815607 89651411829020190095723411)
          ·
            refine ⟨134477117743530285143585117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89651411829020190095723411 134477117743530285143585117)
            ·
              refine ⟨50428919153823856928844419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134477117743530285143585117 50428919153823856928844419)
              ·
                refine ⟨75643378730735785393266629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50428919153823856928844419 75643378730735785393266629)
                ·
                  refine ⟨14183133512012959761237493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75643378730735785393266629 14183133512012959761237493)
                  ·
                    refine ⟨1329668766751214977616015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14183133512012959761237493 1329668766751214977616015)
                    ·
                      rfl

theorem cell22_3884281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_3884281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884281 prefixEnd_3884281 := by exact prefixLift 3884281
  have htrace : WordTrace (prefixWord ++ tailWord_3884281) baseStart_3884281 baseEnd_3884281 := by
    simpa [prefixWord, tailWord_3884281, baseEnd_3884281] using wordTrace_append hprefix tailTrace_3884281
  have hstable : (prefixWord ++ tailWord_3884281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884281).length < 2 ^ (prefixWord ++ tailWord_3884281).sum := by decide
  have hdescent : baseEnd_3884281 < baseStart_3884281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884300 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 5]
def baseStart_3884300 : Nat := 118140960795 + 3884300 * 2 ^ 59
def prefixEnd_3884300 : Nat := 4983230072969 + 3 ^ 40 * 3884300 * 2
def baseEnd_3884300 : Nat := 443225090279835087130319

theorem tailTrace_3884300 : CollatzResearch.WordTrace tailWord_3884300 prefixEnd_3884300 443225090279835087130319 := by
  unfold tailWord_3884300
  simp only [CollatzResearch.WordTrace]
  refine ⟨70836029913925980235141177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94448039885234640313521569 70836029913925980235141177)
  ·
    refine ⟨53127022435444485176355883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70836029913925980235141177 53127022435444485176355883)
    ·
      refine ⟨79690533653166727764533825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53127022435444485176355883 79690533653166727764533825)
      ·
        refine ⟨59767900239875045823400369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79690533653166727764533825 59767900239875045823400369)
        ·
          refine ⟨44825925179906284367550277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59767900239875045823400369 44825925179906284367550277)
          ·
            refine ⟨8404860971232428318915677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44825925179906284367550277 8404860971232428318915677)
            ·
              refine ⟨3151822864212160619593379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8404860971232428318915677 3151822864212160619593379)
              ·
                refine ⟨4727734296318240929390069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151822864212160619593379 4727734296318240929390069)
                ·
                  refine ⟨443225090279835087130319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727734296318240929390069 443225090279835087130319)
                  ·
                    rfl

theorem cell22_3884300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_3884300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884300 prefixEnd_3884300 := by exact prefixLift 3884300
  have htrace : WordTrace (prefixWord ++ tailWord_3884300) baseStart_3884300 baseEnd_3884300 := by
    simpa [prefixWord, tailWord_3884300, baseEnd_3884300] using wordTrace_append hprefix tailTrace_3884300
  have hstable : (prefixWord ++ tailWord_3884300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884300).length < 2 ^ (prefixWord ++ tailWord_3884300).sum := by decide
  have hdescent : baseEnd_3884300 < baseStart_3884300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884373 : List Nat := [1, 3, 2, 2, 3, 1, 2, 8]
def baseStart_3884373 : Nat := 118140960795 + 3884373 * 2 ^ 59
def prefixEnd_3884373 : Nat := 4983230072969 + 3 ^ 40 * 3884373 * 2
def baseEnd_3884373 : Nat := 147744473359039711590637

theorem tailTrace_3884373 : CollatzResearch.WordTrace tailWord_3884373 prefixEnd_3884373 147744473359039711590637 := by
  unfold tailWord_3884373
  simp only [CollatzResearch.WordTrace]
  refine ⟨141674722356587493937689773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94449814904391662625126515 141674722356587493937689773)
  ·
    refine ⟨53128020883720310226633665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141674722356587493937689773 53128020883720310226633665)
    ·
      refine ⟨39846015662790232669975249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53128020883720310226633665 39846015662790232669975249)
      ·
        refine ⟨29884511747092674502481437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39846015662790232669975249 29884511747092674502481437)
        ·
          refine ⟨11206691905159752938430539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29884511747092674502481437 11206691905159752938430539)
          ·
            refine ⟨16810037857739629407645809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206691905159752938430539 16810037857739629407645809)
            ·
              refine ⟨12607528393304722055734357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16810037857739629407645809 12607528393304722055734357)
              ·
                refine ⟨147744473359039711590637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12607528393304722055734357 147744473359039711590637)
                ·
                  rfl

theorem cell22_3884373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 8].length) (baseStart_3884373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884373 prefixEnd_3884373 := by exact prefixLift 3884373
  have htrace : WordTrace (prefixWord ++ tailWord_3884373) baseStart_3884373 baseEnd_3884373 := by
    simpa [prefixWord, tailWord_3884373, baseEnd_3884373] using wordTrace_append hprefix tailTrace_3884373
  have hstable : (prefixWord ++ tailWord_3884373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884373).length < 2 ^ (prefixWord ++ tailWord_3884373).sum := by decide
  have hdescent : baseEnd_3884373 < baseStart_3884373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884375 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 2, 4]
def baseStart_3884375 : Nat := 118140960795 + 3884375 * 2 ^ 59
def prefixEnd_3884375 : Nat := 4983230072969 + 3 ^ 40 * 3884375 * 2
def baseEnd_3884375 : Nat := 1329700944872230065765727

theorem tailTrace_3884375 : CollatzResearch.WordTrace tailWord_3884375 prefixEnd_3884375 1329700944872230065765727 := by
  unfold tailWord_3884375
  simp only [CollatzResearch.WordTrace]
  refine ⟨141674795302580248279262579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94449863535053498852841719 141674795302580248279262579)
  ·
    refine ⟨212512192953870372418893869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141674795302580248279262579 212512192953870372418893869)
    ·
      refine ⟨79692072357701389657085201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212512192953870372418893869 79692072357701389657085201)
      ·
        refine ⟨59769054268276042242813901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79692072357701389657085201 59769054268276042242813901)
        ·
          refine ⟨22413395350603515841055213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59769054268276042242813901 22413395350603515841055213)
          ·
            refine ⟨8405023256476318440395705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22413395350603515841055213 8405023256476318440395705)
            ·
              refine ⟨6303767442357238830296779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8405023256476318440395705 6303767442357238830296779)
              ·
                refine ⟨9455651163535858245445169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6303767442357238830296779 9455651163535858245445169)
                ·
                  refine ⟨7091738372651893684083877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9455651163535858245445169 7091738372651893684083877)
                  ·
                    refine ⟨1329700944872230065765727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091738372651893684083877 1329700944872230065765727)
                    ·
                      rfl

theorem cell22_3884375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_3884375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884375 prefixEnd_3884375 := by exact prefixLift 3884375
  have htrace : WordTrace (prefixWord ++ tailWord_3884375) baseStart_3884375 baseEnd_3884375 := by
    simpa [prefixWord, tailWord_3884375, baseEnd_3884375] using wordTrace_append hprefix tailTrace_3884375
  have hstable : (prefixWord ++ tailWord_3884375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884375).length < 2 ^ (prefixWord ++ tailWord_3884375).sum := by decide
  have hdescent : baseEnd_3884375 < baseStart_3884375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884394 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_3884394 : Nat := 118140960795 + 3884394 * 2 ^ 59
def prefixEnd_3884394 : Nat := 4983230072969 + 3 ^ 40 * 3884394 * 2
def baseEnd_3884394 : Nat := 1329707448960520349540669

theorem tailTrace_3884394 : CollatzResearch.WordTrace tailWord_3884394 prefixEnd_3884394 1329707448960520349540669 := by
  unfold tailWord_3884394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35418872072377853631051059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94450325526340943016136157 35418872072377853631051059)
  ·
    refine ⟨53128308108566780446576589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35418872072377853631051059 53128308108566780446576589)
    ·
      refine ⟨19923115540712542667466221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53128308108566780446576589 19923115540712542667466221)
      ·
        refine ⟨7471168327767203500299833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19923115540712542667466221 7471168327767203500299833)
        ·
          refine ⟨5603376245825402625224875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7471168327767203500299833 5603376245825402625224875)
          ·
            refine ⟨8405064368738103937837313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603376245825402625224875 8405064368738103937837313)
            ·
              refine ⟨6303798276553577953377985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8405064368738103937837313 6303798276553577953377985)
              ·
                refine ⟨4727848707415183465033489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303798276553577953377985 4727848707415183465033489)
                ·
                  refine ⟨3545886530561387598775117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727848707415183465033489 3545886530561387598775117)
                  ·
                    refine ⟨1329707448960520349540669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545886530561387598775117 1329707448960520349540669)
                    ·
                      rfl

theorem cell22_3884394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_3884394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884394 prefixEnd_3884394 := by exact prefixLift 3884394
  have htrace : WordTrace (prefixWord ++ tailWord_3884394) baseStart_3884394 baseEnd_3884394 := by
    simpa [prefixWord, tailWord_3884394, baseEnd_3884394] using wordTrace_append hprefix tailTrace_3884394
  have hstable : (prefixWord ++ tailWord_3884394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884394).length < 2 ^ (prefixWord ++ tailWord_3884394).sum := by decide
  have hdescent : baseEnd_3884394 < baseStart_3884394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884450 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3884450 : Nat := 118140960795 + 3884450 * 2 ^ 59
def prefixEnd_3884450 : Nat := 4983230072969 + 3 ^ 40 * 3884450 * 2
def baseEnd_3884450 : Nat := 1329726618904954870140497

theorem tailTrace_3884450 : CollatzResearch.WordTrace tailWord_3884450 prefixEnd_3884450 1329726618904954870140497 := by
  unfold tailWord_3884450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35419382694327134022060701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94451687184872357392161869 35419382694327134022060701)
  ·
    refine ⟨13282268510372675258272763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35419382694327134022060701 13282268510372675258272763)
    ·
      refine ⟨19923402765559012887409145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13282268510372675258272763 19923402765559012887409145)
      ·
        refine ⟨14942552074169259665556859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19923402765559012887409145 14942552074169259665556859)
        ·
          refine ⟨22413828111253889498335289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942552074169259665556859 22413828111253889498335289)
          ·
            refine ⟨16810371083440417123751467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22413828111253889498335289 16810371083440417123751467)
            ·
              refine ⟨25215556625160625685627201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16810371083440417123751467 25215556625160625685627201)
              ·
                refine ⟨18911667468870469264220401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25215556625160625685627201 18911667468870469264220401)
                ·
                  refine ⟨14183750601652851948165301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18911667468870469264220401 14183750601652851948165301)
                  ·
                    refine ⟨1329726618904954870140497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14183750601652851948165301 1329726618904954870140497)
                    ·
                      rfl

theorem cell22_3884450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3884450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884450 prefixEnd_3884450 := by exact prefixLift 3884450
  have htrace : WordTrace (prefixWord ++ tailWord_3884450) baseStart_3884450 baseEnd_3884450 := by
    simpa [prefixWord, tailWord_3884450, baseEnd_3884450] using wordTrace_append hprefix tailTrace_3884450
  have hstable : (prefixWord ++ tailWord_3884450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884450).length < 2 ^ (prefixWord ++ tailWord_3884450).sum := by decide
  have hdescent : baseEnd_3884450 < baseStart_3884450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884495 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 4, 3]
def baseStart_3884495 : Nat := 118140960795 + 3884495 * 2 ^ 59
def prefixEnd_3884495 : Nat := 4983230072969 + 3 ^ 40 * 3884495 * 2
def baseEnd_3884495 : Nat := 1329742023324589752765359

theorem tailTrace_3884495 : CollatzResearch.WordTrace tailWord_3884495 prefixEnd_3884495 1329742023324589752765359 := by
  unfold tailWord_3884495
  simp only [CollatzResearch.WordTrace]
  refine ⟨141679172062145508773630939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94452781374763672515753959 141679172062145508773630939)
  ·
    refine ⟨212518758093218263160446409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141679172062145508773630939 212518758093218263160446409)
    ·
      refine ⟨159389068569913697370334807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212518758093218263160446409 159389068569913697370334807)
      ·
        refine ⟨239083602854870546055502211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159389068569913697370334807 239083602854870546055502211)
        ·
          refine ⟨358625404282305819083253317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239083602854870546055502211 358625404282305819083253317)
          ·
            refine ⟨67242263302932341078109997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358625404282305819083253317 67242263302932341078109997)
            ·
              refine ⟨25215848738599627904291249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67242263302932341078109997 25215848738599627904291249)
              ·
                refine ⟨18911886553949720928218437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25215848738599627904291249 18911886553949720928218437)
                ·
                  refine ⟨3545978728865572674040957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18911886553949720928218437 3545978728865572674040957)
                  ·
                    refine ⟨1329742023324589752765359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3545978728865572674040957 1329742023324589752765359)
                    ·
                      rfl

theorem cell22_3884495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_3884495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884495 prefixEnd_3884495 := by exact prefixLift 3884495
  have htrace : WordTrace (prefixWord ++ tailWord_3884495) baseStart_3884495 baseEnd_3884495 := by
    simpa [prefixWord, tailWord_3884495, baseEnd_3884495] using wordTrace_append hprefix tailTrace_3884495
  have hstable : (prefixWord ++ tailWord_3884495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884495).length < 2 ^ (prefixWord ++ tailWord_3884495).sum := by decide
  have hdescent : baseEnd_3884495 < baseStart_3884495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884523 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_3884523 : Nat := 118140960795 + 3884523 * 2 ^ 59
def prefixEnd_3884523 : Nat := 4983230072969 + 3 ^ 40 * 3884523 * 2
def baseEnd_3884523 : Nat := 1329751608296807013065273

theorem tailTrace_3884523 : CollatzResearch.WordTrace tailWord_3884523 prefixEnd_3884523 1329751608296807013065273 := by
  unfold tailWord_3884523
  simp only [CollatzResearch.WordTrace]
  refine ⟨141680193306044069555650223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94453462204029379703766815 141680193306044069555650223)
  ·
    refine ⟨212520289959066104333475335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141680193306044069555650223 212520289959066104333475335)
    ·
      refine ⟨318780434938599156500213003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212520289959066104333475335 318780434938599156500213003)
      ·
        refine ⟨478170652407898734750319505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318780434938599156500213003 478170652407898734750319505)
        ·
          refine ⟨358627989305924051062739629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478170652407898734750319505 358627989305924051062739629)
          ·
            refine ⟨134485495989721519148527361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358627989305924051062739629 134485495989721519148527361)
            ·
              refine ⟨100864121992291139361395521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134485495989721519148527361 100864121992291139361395521)
              ·
                refine ⟨75648091494218354521046641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100864121992291139361395521 75648091494218354521046641)
                ·
                  refine ⟨56736068620663765890784981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75648091494218354521046641 56736068620663765890784981)
                  ·
                    refine ⟨1329751608296807013065273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56736068620663765890784981 1329751608296807013065273)
                    ·
                      rfl

theorem cell22_3884523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_3884523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884523 prefixEnd_3884523 := by exact prefixLift 3884523
  have htrace : WordTrace (prefixWord ++ tailWord_3884523) baseStart_3884523 baseEnd_3884523 := by
    simpa [prefixWord, tailWord_3884523, baseEnd_3884523] using wordTrace_append hprefix tailTrace_3884523
  have hstable : (prefixWord ++ tailWord_3884523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884523).length < 2 ^ (prefixWord ++ tailWord_3884523).sum := by decide
  have hdescent : baseEnd_3884523 < baseStart_3884523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884529 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 2, 3]
def baseStart_3884529 : Nat := 118140960795 + 3884529 * 2 ^ 59
def prefixEnd_3884529 : Nat := 4983230072969 + 3 ^ 40 * 3884529 * 2
def baseEnd_3884529 : Nat := 1329753662219424997415255

theorem tailTrace_3884529 : CollatzResearch.WordTrace tailWord_3884529 prefixEnd_3884529 1329753662219424997415255 := by
  unfold tailWord_3884529
  simp only [CollatzResearch.WordTrace]
  refine ⟨141680412144022332580368641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94453608096014888386912427 141680412144022332580368641)
  ·
    refine ⟨106260309108016749435276481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141680412144022332580368641 106260309108016749435276481)
    ·
      refine ⟨79695231831012562076457361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106260309108016749435276481 79695231831012562076457361)
      ·
        refine ⟨59771423873259421557343021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79695231831012562076457361 59771423873259421557343021)
        ·
          refine ⟨22414283952472283084003633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59771423873259421557343021 22414283952472283084003633)
          ·
            refine ⟨16810712964354212313002725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22414283952472283084003633 16810712964354212313002725)
            ·
              refine ⟨3152008680816414808688011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16810712964354212313002725 3152008680816414808688011)
              ·
                refine ⟨4728013021224622213032017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152008680816414808688011 4728013021224622213032017)
                ·
                  refine ⟨3546009765918466659774013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728013021224622213032017 3546009765918466659774013)
                  ·
                    refine ⟨1329753662219424997415255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3546009765918466659774013 1329753662219424997415255)
                    ·
                      rfl

theorem cell22_3884529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_3884529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884529 prefixEnd_3884529 := by exact prefixLift 3884529
  have htrace : WordTrace (prefixWord ++ tailWord_3884529) baseStart_3884529 baseEnd_3884529 := by
    simpa [prefixWord, tailWord_3884529, baseEnd_3884529] using wordTrace_append hprefix tailTrace_3884529
  have hstable : (prefixWord ++ tailWord_3884529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884529).length < 2 ^ (prefixWord ++ tailWord_3884529).sum := by decide
  have hdescent : baseEnd_3884529 < baseStart_3884529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884550 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3884550 : Nat := 118140960795 + 3884550 * 2 ^ 59
def prefixEnd_3884550 : Nat := 4983230072969 + 3 ^ 40 * 3884550 * 2
def baseEnd_3884550 : Nat := 1329760850948587942640191

theorem tailTrace_3884550 : CollatzResearch.WordTrace tailWord_3884550 prefixEnd_3884550 1329760850948587942640191 := by
  unfold tailWord_3884550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427536814904570411465097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94454118717964168777922069 4427536814904570411465097)
  ·
    refine ⟨3320652611178427808598823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4427536814904570411465097 3320652611178427808598823)
    ·
      refine ⟨4980978916767641712898235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320652611178427808598823 4980978916767641712898235)
      ·
        refine ⟨7471468375151462569347353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980978916767641712898235 7471468375151462569347353)
        ·
          refine ⟨5603601281363596927010515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7471468375151462569347353 5603601281363596927010515)
          ·
            refine ⟨8405401922045395390515773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603601281363596927010515 8405401922045395390515773)
            ·
              refine ⟨3152025720767023271443415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8405401922045395390515773 3152025720767023271443415)
              ·
                refine ⟨4728038581150534907165123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152025720767023271443415 4728038581150534907165123)
                ·
                  refine ⟨7092057871725802360747685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728038581150534907165123 7092057871725802360747685)
                  ·
                    refine ⟨1329760850948587942640191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092057871725802360747685 1329760850948587942640191)
                    ·
                      rfl

theorem cell22_3884550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3884550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884550 prefixEnd_3884550 := by exact prefixLift 3884550
  have htrace : WordTrace (prefixWord ++ tailWord_3884550) baseStart_3884550 baseEnd_3884550 := by
    simpa [prefixWord, tailWord_3884550, baseEnd_3884550] using wordTrace_append hprefix tailTrace_3884550
  have hstable : (prefixWord ++ tailWord_3884550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884550).length < 2 ^ (prefixWord ++ tailWord_3884550).sum := by decide
  have hdescent : baseEnd_3884550 < baseStart_3884550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884621 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3884621 : Nat := 118140960795 + 3884621 * 2 ^ 59
def prefixEnd_3884621 : Nat := 4983230072969 + 3 ^ 40 * 3884621 * 2
def baseEnd_3884621 : Nat := 443261718566522474704991

theorem tailTrace_3884621 : CollatzResearch.WordTrace tailWord_3884621 prefixEnd_3884621 443261718566522474704991 := by
  unfold tailWord_3884621
  simp only [CollatzResearch.WordTrace]
  refine ⟨141683767659689032292717717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94455845106459354861811811 141683767659689032292717717)
  ·
    refine ⟨6641426609047923388721143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141683767659689032292717717 6641426609047923388721143)
    ·
      refine ⟨9962139913571885083081715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6641426609047923388721143 9962139913571885083081715)
      ·
        refine ⟨14943209870357827624622573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9962139913571885083081715 14943209870357827624622573)
        ·
          refine ⟨5603703701384185359233465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14943209870357827624622573 5603703701384185359233465)
          ·
            refine ⟨4202777776038139019425099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5603703701384185359233465 4202777776038139019425099)
            ·
              refine ⟨6304166664057208529137649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202777776038139019425099 6304166664057208529137649)
              ·
                refine ⟨4728124998042906396853237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304166664057208529137649 4728124998042906396853237)
                ·
                  refine ⟨443261718566522474704991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4728124998042906396853237 443261718566522474704991)
                  ·
                    rfl

theorem cell22_3884621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3884621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884621 prefixEnd_3884621 := by exact prefixLift 3884621
  have htrace : WordTrace (prefixWord ++ tailWord_3884621) baseStart_3884621 baseEnd_3884621 := by
    simpa [prefixWord, tailWord_3884621, baseEnd_3884621] using wordTrace_append hprefix tailTrace_3884621
  have hstable : (prefixWord ++ tailWord_3884621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884621).length < 2 ^ (prefixWord ++ tailWord_3884621).sum := by decide
  have hdescent : baseEnd_3884621 < baseStart_3884621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884647 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3884647 : Nat := 118140960795 + 3884647 * 2 ^ 59
def prefixEnd_3884647 : Nat := 4983230072969 + 3 ^ 40 * 3884647 * 2
def baseEnd_3884647 : Nat := 1329794056030912022964893

theorem tailTrace_3884647 : CollatzResearch.WordTrace tailWord_3884647 prefixEnd_3884647 1329794056030912022964893 := by
  unfold tailWord_3884647
  simp only [CollatzResearch.WordTrace]
  refine ⟨141684715957594838733164195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94456477305063225822109463 141684715957594838733164195)
  ·
    refine ⟨212527073936392258099746293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141684715957594838733164195 212527073936392258099746293)
    ·
      refine ⟨19924413181536774196851215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212527073936392258099746293 19924413181536774196851215)
      ·
        refine ⟨29886619772305161295276823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19924413181536774196851215 29886619772305161295276823)
        ·
          refine ⟨44829929658457741942915235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29886619772305161295276823 44829929658457741942915235)
          ·
            refine ⟨67244894487686612914372853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44829929658457741942915235 67244894487686612914372853)
            ·
              refine ⟨6304208858220619960722455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67244894487686612914372853 6304208858220619960722455)
              ·
                refine ⟨9456313287330929941083683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304208858220619960722455 9456313287330929941083683)
                ·
                  refine ⟨14184469930996394911625525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456313287330929941083683 14184469930996394911625525)
                  ·
                    refine ⟨1329794056030912022964893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14184469930996394911625525 1329794056030912022964893)
                    ·
                      rfl

theorem cell22_3884647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3884647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884647 prefixEnd_3884647 := by exact prefixLift 3884647
  have htrace : WordTrace (prefixWord ++ tailWord_3884647) baseStart_3884647 baseEnd_3884647 := by
    simpa [prefixWord, tailWord_3884647, baseEnd_3884647] using wordTrace_append hprefix tailTrace_3884647
  have hstable : (prefixWord ++ tailWord_3884647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884647).length < 2 ^ (prefixWord ++ tailWord_3884647).sum := by decide
  have hdescent : baseEnd_3884647 < baseStart_3884647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884754 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3884754 : Nat := 118140960795 + 3884754 * 2 ^ 59
def prefixEnd_3884754 : Nat := 4983230072969 + 3 ^ 40 * 3884754 * 2
def baseEnd_3884754 : Nat := 1329830684317599410539565

theorem tailTrace_3884754 : CollatzResearch.WordTrace tailWord_3884754 prefixEnd_3884754 1329830684317599410539565 := by
  unfold tailWord_3884754
  simp only [CollatzResearch.WordTrace]
  refine ⟨35422154642051799001827329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94459079045471464004872877 35422154642051799001827329)
  ·
    refine ⟨26566615981538849251370497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35422154642051799001827329 26566615981538849251370497)
    ·
      refine ⟨19924961986154136938527873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26566615981538849251370497 19924961986154136938527873)
      ·
        refine ⟨14943721489615602703895905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19924961986154136938527873 14943721489615602703895905)
        ·
          refine ⟨11207791117211702027921929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14943721489615602703895905 11207791117211702027921929)
          ·
            refine ⟨8405843337908776520941447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11207791117211702027921929 8405843337908776520941447)
            ·
              refine ⟨12608765006863164781412171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405843337908776520941447 12608765006863164781412171)
              ·
                refine ⟨18913147510294747172118257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12608765006863164781412171 18913147510294747172118257)
                ·
                  refine ⟨14184860632721060379088693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18913147510294747172118257 14184860632721060379088693)
                  ·
                    refine ⟨1329830684317599410539565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14184860632721060379088693 1329830684317599410539565)
                    ·
                      rfl

theorem cell22_3884754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3884754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884754 prefixEnd_3884754 := by exact prefixLift 3884754
  have htrace : WordTrace (prefixWord ++ tailWord_3884754) baseStart_3884754 baseEnd_3884754 := by
    simpa [prefixWord, tailWord_3884754, baseEnd_3884754] using wordTrace_append hprefix tailTrace_3884754
  have hstable : (prefixWord ++ tailWord_3884754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884754).length < 2 ^ (prefixWord ++ tailWord_3884754).sum := by decide
  have hdescent : baseEnd_3884754 < baseStart_3884754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884767 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 6]
def baseStart_3884767 : Nat := 118140960795 + 3884767 * 2 ^ 59
def prefixEnd_3884767 : Nat := 4983230072969 + 3 ^ 40 * 3884767 * 2
def baseEnd_3884767 : Nat := 443278378161090569988175

theorem tailTrace_3884767 : CollatzResearch.WordTrace tailWord_3884767 prefixEnd_3884767 443278378161090569988175 := by
  unfold tailWord_3884767
  simp only [CollatzResearch.WordTrace]
  refine ⟨141689092717160099227532555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94459395144773399485021703 141689092717160099227532555)
  ·
    refine ⟨212533639075740148841298833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141689092717160099227532555 212533639075740148841298833)
    ·
      refine ⟨159400229306805111630974125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212533639075740148841298833 159400229306805111630974125)
      ·
        refine ⟨59775085990051916861615297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159400229306805111630974125 59775085990051916861615297)
        ·
          refine ⟨44831314492538937646211473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59775085990051916861615297 44831314492538937646211473)
          ·
            refine ⟨33623485869404203234658605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44831314492538937646211473 33623485869404203234658605)
            ·
              refine ⟨12608807201026576212996977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33623485869404203234658605 12608807201026576212996977)
              ·
                refine ⟨9456605400769932159747733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12608807201026576212996977 9456605400769932159747733)
                ·
                  refine ⟨443278378161090569988175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9456605400769932159747733 443278378161090569988175)
                  ·
                    rfl

theorem cell22_3884767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 6].length) (baseStart_3884767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884767 prefixEnd_3884767 := by exact prefixLift 3884767
  have htrace : WordTrace (prefixWord ++ tailWord_3884767) baseStart_3884767 baseEnd_3884767 := by
    simpa [prefixWord, tailWord_3884767, baseEnd_3884767] using wordTrace_append hprefix tailTrace_3884767
  have hstable : (prefixWord ++ tailWord_3884767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884767).length < 2 ^ (prefixWord ++ tailWord_3884767).sum := by decide
  have hdescent : baseEnd_3884767 < baseStart_3884767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884846 : List Nat := [4, 1, 3, 2, 2, 2, 8]
def baseStart_3884846 : Nat := 118140960795 + 3884846 * 2 ^ 59
def prefixEnd_3884846 : Nat := 4983230072969 + 3 ^ 40 * 3884846 * 2
def baseEnd_3884846 : Nat := 49254154733249697675529

theorem tailTrace_3884846 : CollatzResearch.WordTrace tailWord_3884846 prefixEnd_3884846 49254154733249697675529 := by
  unfold tailWord_3884846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711496760484236964957299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94461316055915930479772261 17711496760484236964957299)
  ·
    refine ⟨26567245140726355447435949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711496760484236964957299 26567245140726355447435949)
    ·
      refine ⟨9962716927772383292788481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26567245140726355447435949 9962716927772383292788481)
      ·
        refine ⟨7472037695829287469591361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9962716927772383292788481 7472037695829287469591361)
        ·
          refine ⟨5604028271871965602193521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7472037695829287469591361 5604028271871965602193521)
          ·
            refine ⟨4203021203903974201645141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5604028271871965602193521 4203021203903974201645141)
            ·
              refine ⟨49254154733249697675529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4203021203903974201645141 49254154733249697675529)
              ·
                rfl

theorem cell22_3884846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 8].length) (baseStart_3884846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884846 prefixEnd_3884846 := by exact prefixLift 3884846
  have htrace : WordTrace (prefixWord ++ tailWord_3884846) baseStart_3884846 baseEnd_3884846 := by
    simpa [prefixWord, tailWord_3884846, baseEnd_3884846] using wordTrace_append hprefix tailTrace_3884846
  have hstable : (prefixWord ++ tailWord_3884846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884846).length < 2 ^ (prefixWord ++ tailWord_3884846).sum := by decide
  have hdescent : baseEnd_3884846 < baseStart_3884846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884874 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_3884874 : Nat := 118140960795 + 3884874 * 2 ^ 59
def prefixEnd_3884874 : Nat := 4983230072969 + 3 ^ 40 * 3884874 * 2
def baseEnd_3884874 : Nat := 443290587589986365846399

theorem tailTrace_3884874 : CollatzResearch.WordTrace tailWord_3884874 prefixEnd_3884874 443290587589986365846399 := by
  unfold tailWord_3884874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35423248831943114125419419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94461996885181637667785117 35423248831943114125419419)
  ·
    refine ⟨53134873247914671188129129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35423248831943114125419419 53134873247914671188129129)
    ·
      refine ⟨39851154935936003391096847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53134873247914671188129129 39851154935936003391096847)
      ·
        refine ⟨59776732403904005086645271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39851154935936003391096847 59776732403904005086645271)
        ·
          refine ⟨89665098605856007629967907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59776732403904005086645271 89665098605856007629967907)
          ·
            refine ⟨134497647908784011444951861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89665098605856007629967907 134497647908784011444951861)
            ·
              refine ⟨12609154491448501072964237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134497647908784011444951861 12609154491448501072964237)
              ·
                refine ⟨4728432934293187902361589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12609154491448501072964237 4728432934293187902361589)
                ·
                  refine ⟨443290587589986365846399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4728432934293187902361589 443290587589986365846399)
                  ·
                    rfl

theorem cell22_3884874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_3884874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884874 prefixEnd_3884874 := by exact prefixLift 3884874
  have htrace : WordTrace (prefixWord ++ tailWord_3884874) baseStart_3884874 baseEnd_3884874 := by
    simpa [prefixWord, tailWord_3884874, baseEnd_3884874] using wordTrace_append hprefix tailTrace_3884874
  have hstable : (prefixWord ++ tailWord_3884874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884874).length < 2 ^ (prefixWord ++ tailWord_3884874).sum := by decide
  have hdescent : baseEnd_3884874 < baseStart_3884874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884936 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_3884936 : Nat := 118140960795 + 3884936 * 2 ^ 59
def prefixEnd_3884936 : Nat := 4983230072969 + 3 ^ 40 * 3884936 * 2
def baseEnd_3884936 : Nat := 443297662212337200829669

theorem tailTrace_3884936 : CollatzResearch.WordTrace tailWord_3884936 prefixEnd_3884936 443297662212337200829669 := by
  unfold tailWord_3884936
  simp only [CollatzResearch.WordTrace]
  refine ⟨70847628326773920545217331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94463504435698560726956441 70847628326773920545217331)
  ·
    refine ⟨106271442490160880817825997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70847628326773920545217331 106271442490160880817825997)
    ·
      refine ⟨39851790933810330306684749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106271442490160880817825997 39851790933810330306684749)
      ·
        refine ⟨14944421600178873865006781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39851790933810330306684749 14944421600178873865006781)
        ·
          refine ⟨5604158100067077699377543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14944421600178873865006781 5604158100067077699377543)
          ·
            refine ⟨8406237150100616549066315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604158100067077699377543 8406237150100616549066315)
            ·
              refine ⟨12609355725150924823599473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8406237150100616549066315 12609355725150924823599473)
              ·
                refine ⟨9457016793863193617699605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12609355725150924823599473 9457016793863193617699605)
                ·
                  refine ⟨443297662212337200829669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9457016793863193617699605 443297662212337200829669)
                  ·
                    rfl

theorem cell22_3884936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_3884936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884936 prefixEnd_3884936 := by exact prefixLift 3884936
  have htrace : WordTrace (prefixWord ++ tailWord_3884936) baseStart_3884936 baseEnd_3884936 := by
    simpa [prefixWord, tailWord_3884936, baseEnd_3884936] using wordTrace_append hprefix tailTrace_3884936
  have hstable : (prefixWord ++ tailWord_3884936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884936).length < 2 ^ (prefixWord ++ tailWord_3884936).sum := by decide
  have hdescent : baseEnd_3884936 < baseStart_3884936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884949 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3884949 : Nat := 118140960795 + 3884949 * 2 ^ 59
def prefixEnd_3884949 : Nat := 4983230072969 + 3 ^ 40 * 3884949 * 2
def baseEnd_3884949 : Nat := 1329897436802683901913967

theorem tailTrace_3884949 : CollatzResearch.WordTrace tailWord_3884949 prefixEnd_3884949 1329897436802683901913967 := by
  unfold tailWord_3884949
  simp only [CollatzResearch.WordTrace]
  refine ⟨141695730802500744310657901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94463820535000496207105267 141695730802500744310657901)
  ·
    refine ⟨53135899050937779116496713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141695730802500744310657901 53135899050937779116496713)
    ·
      refine ⟨39851924288203334337372535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53135899050937779116496713 39851924288203334337372535)
      ·
        refine ⟨59777886432305001506058803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39851924288203334337372535 59777886432305001506058803)
        ·
          refine ⟨89666829648457502259088205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59777886432305001506058803 89666829648457502259088205)
          ·
            refine ⟨33625061118171563347158077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89666829648457502259088205 33625061118171563347158077)
            ·
              refine ⟨12609397919314336255184279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33625061118171563347158077 12609397919314336255184279)
              ·
                refine ⟨18914096878971504382776419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12609397919314336255184279 18914096878971504382776419)
                ·
                  refine ⟨28371145318457256574164629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18914096878971504382776419 28371145318457256574164629)
                  ·
                    refine ⟨1329897436802683901913967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28371145318457256574164629 1329897436802683901913967)
                    ·
                      rfl

theorem cell22_3884949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3884949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884949 prefixEnd_3884949 := by exact prefixLift 3884949
  have htrace : WordTrace (prefixWord ++ tailWord_3884949) baseStart_3884949 baseEnd_3884949 := by
    simpa [prefixWord, tailWord_3884949, baseEnd_3884949] using wordTrace_append hprefix tailTrace_3884949
  have hstable : (prefixWord ++ tailWord_3884949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884949).length < 2 ^ (prefixWord ++ tailWord_3884949).sum := by decide
  have hdescent : baseEnd_3884949 < baseStart_3884949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884964 : List Nat := [2, 3, 1, 2, 1, 4, 9]
def baseStart_3884964 : Nat := 118140960795 + 3884964 * 2 ^ 59
def prefixEnd_3884964 : Nat := 4983230072969 + 3 ^ 40 * 3884964 * 2
def baseEnd_3884964 : Nat := 49255650800341809732923

theorem tailTrace_3884964 : CollatzResearch.WordTrace tailWord_3884964 prefixEnd_3884964 49255650800341809732923 := by
  unfold tailWord_3884964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70848138948723200936226973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94464185264964267914969297 70848138948723200936226973)
  ·
    refine ⟨26568052105771200351085115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70848138948723200936226973 26568052105771200351085115)
    ·
      refine ⟨39852078158656800526627673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26568052105771200351085115 39852078158656800526627673)
      ·
        refine ⟨29889058618992600394970755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39852078158656800526627673 29889058618992600394970755)
        ·
          refine ⟨44833587928488900592456133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29889058618992600394970755 44833587928488900592456133)
          ·
            refine ⟨8406297736591668861085525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44833587928488900592456133 8406297736591668861085525)
            ·
              refine ⟨49255650800341809732923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8406297736591668861085525 49255650800341809732923)
              ·
                rfl

theorem cell22_3884964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 9].length) (baseStart_3884964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3884964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3884964 prefixEnd_3884964 := by exact prefixLift 3884964
  have htrace : WordTrace (prefixWord ++ tailWord_3884964) baseStart_3884964 baseEnd_3884964 := by
    simpa [prefixWord, tailWord_3884964, baseEnd_3884964] using wordTrace_append hprefix tailTrace_3884964
  have hstable : (prefixWord ++ tailWord_3884964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884964).length < 2 ^ (prefixWord ++ tailWord_3884964).sum := by decide
  have hdescent : baseEnd_3884964 < baseStart_3884964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885024 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_3885024 : Nat := 118140960795 + 3885024 * 2 ^ 59
def prefixEnd_3885024 : Nat := 4983230072969 + 3 ^ 40 * 3885024 * 2
def baseEnd_3885024 : Nat := 1329923110835408706288737

theorem tailTrace_3885024 : CollatzResearch.WordTrace tailWord_3885024 prefixEnd_3885024 1329923110835408706288737 := by
  unfold tailWord_3885024
  simp only [CollatzResearch.WordTrace]
  refine ⟨70849233138614516059819063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94465644184819354746425417 70849233138614516059819063)
  ·
    refine ⟨106273849707921774089728595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70849233138614516059819063 106273849707921774089728595)
    ·
      refine ⟨159410774561882661134592893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106273849707921774089728595 159410774561882661134592893)
      ·
        refine ⟨59779040460705997925472335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159410774561882661134592893 59779040460705997925472335)
        ·
          refine ⟨89668560691058996888208503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59779040460705997925472335 89668560691058996888208503)
          ·
            refine ⟨134502841036588495332312755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89668560691058996888208503 134502841036588495332312755)
            ·
              refine ⟨201754261554882742998469133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134502841036588495332312755 201754261554882742998469133)
              ·
                refine ⟨75657848083081028624425925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201754261554882742998469133 75657848083081028624425925)
                ·
                  refine ⟨14185846515577692867079861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75657848083081028624425925 14185846515577692867079861)
                  ·
                    refine ⟨1329923110835408706288737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14185846515577692867079861 1329923110835408706288737)
                    ·
                      rfl

theorem cell22_3885024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_3885024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885024 prefixEnd_3885024 := by exact prefixLift 3885024
  have htrace : WordTrace (prefixWord ++ tailWord_3885024) baseStart_3885024 baseEnd_3885024 := by
    simpa [prefixWord, tailWord_3885024, baseEnd_3885024] using wordTrace_append hprefix tailTrace_3885024
  have hstable : (prefixWord ++ tailWord_3885024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885024).length < 2 ^ (prefixWord ++ tailWord_3885024).sum := by decide
  have hdescent : baseEnd_3885024 < baseStart_3885024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885056 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_3885056 : Nat := 118140960795 + 3885056 * 2 ^ 59
def prefixEnd_3885056 : Nat := 4983230072969 + 3 ^ 40 * 3885056 * 2
def baseEnd_3885056 : Nat := 1329934065089371289488639

theorem tailTrace_3885056 : CollatzResearch.WordTrace tailWord_3885056 prefixEnd_3885056 1329934065089371289488639 := by
  unfold tailWord_3885056
  simp only [CollatzResearch.WordTrace]
  refine ⟨70849816706556550792401511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94466422275408734389868681 70849816706556550792401511)
  ·
    refine ⟨106274725059834826188602267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70849816706556550792401511 106274725059834826188602267)
    ·
      refine ⟨159412087589752239282903401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106274725059834826188602267 159412087589752239282903401)
      ·
        refine ⟨119559065692314179462177551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159412087589752239282903401 119559065692314179462177551)
        ·
          refine ⟨179338598538471269193266327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119559065692314179462177551 179338598538471269193266327)
          ·
            refine ⟨269007897807706903789899491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179338598538471269193266327 269007897807706903789899491)
            ·
              refine ⟨403511846711560355684849237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269007897807706903789899491 403511846711560355684849237)
              ·
                refine ⟨4728654453651097918181827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 403511846711560355684849237 4728654453651097918181827)
                ·
                  refine ⟨7092981680476646877272741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728654453651097918181827 7092981680476646877272741)
                  ·
                    refine ⟨1329934065089371289488639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092981680476646877272741 1329934065089371289488639)
                    ·
                      rfl

theorem cell22_3885056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_3885056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885056 prefixEnd_3885056 := by exact prefixLift 3885056
  have htrace : WordTrace (prefixWord ++ tailWord_3885056) baseStart_3885056 baseEnd_3885056 := by
    simpa [prefixWord, tailWord_3885056, baseEnd_3885056] using wordTrace_append hprefix tailTrace_3885056
  have hstable : (prefixWord ++ tailWord_3885056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885056).length < 2 ^ (prefixWord ++ tailWord_3885056).sum := by decide
  have hdescent : baseEnd_3885056 < baseStart_3885056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885099 : List Nat := [1, 1, 1, 1, 2, 1, 4, 11]
def baseStart_3885099 : Nat := 118140960795 + 3885099 * 2 ^ 59
def prefixEnd_3885099 : Nat := 4983230072969 + 3 ^ 40 * 3885099 * 2
def baseEnd_3885099 : Nat := 147772087207570390073723

theorem tailTrace_3885099 : CollatzResearch.WordTrace tailWord_3885099 prefixEnd_3885099 147772087207570390073723 := by
  unfold tailWord_3885099
  simp only [CollatzResearch.WordTrace]
  refine ⟨141701201751957319928618351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94467467834638213285745567 141701201751957319928618351)
  ·
    refine ⟨212551802627935979892927527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141701201751957319928618351 212551802627935979892927527)
    ·
      refine ⟨318827703941903969839391291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212551802627935979892927527 318827703941903969839391291)
      ·
        refine ⟨478241555912855954759086937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318827703941903969839391291 478241555912855954759086937)
        ·
          refine ⟨358681166934641966069315203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478241555912855954759086937 358681166934641966069315203)
          ·
            refine ⟨538021750401962949103972805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358681166934641966069315203 538021750401962949103972805)
            ·
              refine ⟨100879078200368052956994901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538021750401962949103972805 100879078200368052956994901)
              ·
                refine ⟨147772087207570390073723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 100879078200368052956994901 147772087207570390073723)
                ·
                  rfl

theorem cell22_3885099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 11].length) (baseStart_3885099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885099 prefixEnd_3885099 := by exact prefixLift 3885099
  have htrace : WordTrace (prefixWord ++ tailWord_3885099) baseStart_3885099 baseEnd_3885099 := by
    simpa [prefixWord, tailWord_3885099, baseEnd_3885099] using wordTrace_append hprefix tailTrace_3885099
  have hstable : (prefixWord ++ tailWord_3885099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885099).length < 2 ^ (prefixWord ++ tailWord_3885099).sum := by decide
  have hdescent : baseEnd_3885099 < baseStart_3885099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885154 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3885154 : Nat := 118140960795 + 3885154 * 2 ^ 59
def prefixEnd_3885154 : Nat := 4983230072969 + 3 ^ 40 * 3885154 * 2
def baseEnd_3885154 : Nat := 1329967612492131700538339

theorem tailTrace_3885154 : CollatzResearch.WordTrace tailWord_3885154 prefixEnd_3885154 1329967612492131700538339 := by
  unfold tailWord_3885154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35425801941689516080467629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94468805177838709547913677 35425801941689516080467629)
  ·
    refine ⟨13284675728133568530175361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35425801941689516080467629 13284675728133568530175361)
    ·
      refine ⟨9963506796100176397631521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13284675728133568530175361 9963506796100176397631521)
      ·
        refine ⟨7472630097075132298223641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9963506796100176397631521 7472630097075132298223641)
        ·
          refine ⟨5604472572806349223667731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7472630097075132298223641 5604472572806349223667731)
          ·
            refine ⟨8406708859209523835501597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604472572806349223667731 8406708859209523835501597)
            ·
              refine ⟨3152515822203571438313099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8406708859209523835501597 3152515822203571438313099)
              ·
                refine ⟨4728773733305357157469649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152515822203571438313099 4728773733305357157469649)
                ·
                  refine ⟨3546580299979017868102237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728773733305357157469649 3546580299979017868102237)
                  ·
                    refine ⟨1329967612492131700538339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3546580299979017868102237 1329967612492131700538339)
                    ·
                      rfl

theorem cell22_3885154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3885154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885154 prefixEnd_3885154 := by exact prefixLift 3885154
  have htrace : WordTrace (prefixWord ++ tailWord_3885154) baseStart_3885154 baseEnd_3885154 := by
    simpa [prefixWord, tailWord_3885154, baseEnd_3885154] using wordTrace_append hprefix tailTrace_3885154
  have hstable : (prefixWord ++ tailWord_3885154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885154).length < 2 ^ (prefixWord ++ tailWord_3885154).sum := by decide
  have hdescent : baseEnd_3885154 < baseStart_3885154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885253 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3885253 : Nat := 118140960795 + 3885253 * 2 ^ 59
def prefixEnd_3885253 : Nat := 4983230072969 + 3 ^ 40 * 3885253 * 2
def baseEnd_3885253 : Nat := 1330001502215328442313035

theorem tailTrace_3885253 : CollatzResearch.WordTrace tailWord_3885253 prefixEnd_3885253 1330001502215328442313035 := by
  unfold tailWord_3885253
  simp only [CollatzResearch.WordTrace]
  refine ⟨141706818593399404229724413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94471212395599602819816275 141706818593399404229724413)
  ·
    refine ⟨53140056972524776586146655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141706818593399404229724413 53140056972524776586146655)
    ·
      refine ⟨79710085458787164879219983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53140056972524776586146655 79710085458787164879219983)
      ·
        refine ⟨119565128188180747318829975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79710085458787164879219983 119565128188180747318829975)
        ·
          refine ⟨179347692282271120978244963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119565128188180747318829975 179347692282271120978244963)
          ·
            refine ⟨269021538423406681467367445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179347692282271120978244963 269021538423406681467367445)
            ·
              refine ⟨12610384613597188193782849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269021538423406681467367445 12610384613597188193782849)
              ·
                refine ⟨9457788460197891145337137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12610384613597188193782849 9457788460197891145337137)
                ·
                  refine ⟨7093341345148418359002853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9457788460197891145337137 7093341345148418359002853)
                  ·
                    refine ⟨1330001502215328442313035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093341345148418359002853 1330001502215328442313035)
                    ·
                      rfl

theorem cell22_3885253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3885253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885253 prefixEnd_3885253 := by exact prefixLift 3885253
  have htrace : WordTrace (prefixWord ++ tailWord_3885253) baseStart_3885253 baseEnd_3885253 := by
    simpa [prefixWord, tailWord_3885253, baseEnd_3885253] using wordTrace_append hprefix tailTrace_3885253
  have hstable : (prefixWord ++ tailWord_3885253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885253).length < 2 ^ (prefixWord ++ tailWord_3885253).sum := by decide
  have hdescent : baseEnd_3885253 < baseStart_3885253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885285 : List Nat := [1, 3, 1, 4, 2, 2, 3, 6]
def baseStart_3885285 : Nat := 118140960795 + 3885285 * 2 ^ 59
def prefixEnd_3885285 : Nat := 4983230072969 + 3 ^ 40 * 3885285 * 2
def baseEnd_3885285 : Nat := 147779161829921225056993

theorem tailTrace_3885285 : CollatzResearch.WordTrace tailWord_3885285 prefixEnd_3885285 147779161829921225056993 := by
  unfold tailWord_3885285
  simp only [CollatzResearch.WordTrace]
  refine ⟨141707985729283473694889309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94471990486188982463259539 141707985729283473694889309)
  ·
    refine ⟨53140494648481302635583491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141707985729283473694889309 53140494648481302635583491)
    ·
      refine ⟨79710741972721953953375237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53140494648481302635583491 79710741972721953953375237)
      ·
        refine ⟨14945764119885366366257857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79710741972721953953375237 14945764119885366366257857)
        ·
          refine ⟨11209323089914024774693393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14945764119885366366257857 11209323089914024774693393)
          ·
            refine ⟨8406992317435518581020045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11209323089914024774693393 8406992317435518581020045)
            ·
              refine ⟨3152622119038319467882517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8406992317435518581020045 3152622119038319467882517)
              ·
                refine ⟨147779161829921225056993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3152622119038319467882517 147779161829921225056993)
                ·
                  rfl

theorem cell22_3885285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 6].length) (baseStart_3885285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885285 prefixEnd_3885285 := by exact prefixLift 3885285
  have htrace : WordTrace (prefixWord ++ tailWord_3885285) baseStart_3885285 baseEnd_3885285 := by
    simpa [prefixWord, tailWord_3885285, baseEnd_3885285] using wordTrace_append hprefix tailTrace_3885285
  have hstable : (prefixWord ++ tailWord_3885285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885285).length < 2 ^ (prefixWord ++ tailWord_3885285).sum := by decide
  have hdescent : baseEnd_3885285 < baseStart_3885285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885287 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3885287 : Nat := 118140960795 + 3885287 * 2 ^ 59
def prefixEnd_3885287 : Nat := 4983230072969 + 3 ^ 40 * 3885287 * 2
def baseEnd_3885287 : Nat := 1330013141110163686962931

theorem tailTrace_3885287 : CollatzResearch.WordTrace tailWord_3885287 prefixEnd_3885287 1330013141110163686962931 := by
  unfold tailWord_3885287
  simp only [CollatzResearch.WordTrace]
  refine ⟨141708058675276228036462115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94472039116850818690974743 141708058675276228036462115)
  ·
    refine ⟨212562088012914342054693173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141708058675276228036462115 212562088012914342054693173)
    ·
      refine ⟨19927695751210719567627485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212562088012914342054693173 19927695751210719567627485)
      ·
        refine ⟨7472885906704019837860307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19927695751210719567627485 7472885906704019837860307)
        ·
          refine ⟨11209328860056029756790461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472885906704019837860307 11209328860056029756790461)
          ·
            refine ⟨4203498322521011158796423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11209328860056029756790461 4203498322521011158796423)
            ·
              refine ⟨6305247483781516738194635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203498322521011158796423 6305247483781516738194635)
              ·
                refine ⟨9457871225672275107291953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305247483781516738194635 9457871225672275107291953)
                ·
                  refine ⟨7093403419254206330468965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9457871225672275107291953 7093403419254206330468965)
                  ·
                    refine ⟨1330013141110163686962931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093403419254206330468965 1330013141110163686962931)
                    ·
                      rfl

theorem cell22_3885287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3885287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885287 prefixEnd_3885287 := by exact prefixLift 3885287
  have htrace : WordTrace (prefixWord ++ tailWord_3885287) baseStart_3885287 baseEnd_3885287 := by
    simpa [prefixWord, tailWord_3885287, baseEnd_3885287] using wordTrace_append hprefix tailTrace_3885287
  have hstable : (prefixWord ++ tailWord_3885287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885287).length < 2 ^ (prefixWord ++ tailWord_3885287).sum := by decide
  have hdescent : baseEnd_3885287 < baseStart_3885287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885313 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 7]
def baseStart_3885313 : Nat := 118140960795 + 3885313 * 2 ^ 59
def prefixEnd_3885313 : Nat := 4983230072969 + 3 ^ 40 * 3885313 * 2
def baseEnd_3885313 : Nat := 443340680480502761937617

theorem tailTrace_3885313 : CollatzResearch.WordTrace tailWord_3885313 prefixEnd_3885313 443340680480502761937617 := by
  unfold tailWord_3885313
  simp only [CollatzResearch.WordTrace]
  refine ⟨141709006973182034476908593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94472671315454689651272395 141709006973182034476908593)
  ·
    refine ⟨106281755229886525857681445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141709006973182034476908593 106281755229886525857681445)
    ·
      refine ⟨19927829105603723598315271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106281755229886525857681445 19927829105603723598315271)
      ·
        refine ⟨29891743658405585397472907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19927829105603723598315271 29891743658405585397472907)
        ·
          refine ⟨44837615487608378096209361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29891743658405585397472907 44837615487608378096209361)
          ·
            refine ⟨33628211615706283572157021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44837615487608378096209361 33628211615706283572157021)
            ·
              refine ⟨12610579355889856339558883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33628211615706283572157021 12610579355889856339558883)
              ·
                refine ⟨18915869033834784509338325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12610579355889856339558883 18915869033834784509338325)
                ·
                  refine ⟨443340680480502761937617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18915869033834784509338325 443340680480502761937617)
                  ·
                    rfl

theorem cell22_3885313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_3885313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885313 prefixEnd_3885313 := by exact prefixLift 3885313
  have htrace : WordTrace (prefixWord ++ tailWord_3885313) baseStart_3885313 baseEnd_3885313 := by
    simpa [prefixWord, tailWord_3885313, baseEnd_3885313] using wordTrace_append hprefix tailTrace_3885313
  have hstable : (prefixWord ++ tailWord_3885313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885313).length < 2 ^ (prefixWord ++ tailWord_3885313).sum := by decide
  have hdescent : baseEnd_3885313 < baseStart_3885313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885390 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_3885390 : Nat := 118140960795 + 3885390 * 2 ^ 59
def prefixEnd_3885390 : Nat := 4983230072969 + 3 ^ 40 * 3885390 * 2
def baseEnd_3885390 : Nat := 1330048400115105751637615

theorem tailTrace_3885390 : CollatzResearch.WordTrace tailWord_3885390 prefixEnd_3885390 1330048400115105751637615 := by
  unfold tailWord_3885390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17713976924237884578432703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94474543595935384418307749 17713976924237884578432703)
  ·
    refine ⟨26570965386356826867649055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17713976924237884578432703 26570965386356826867649055)
    ·
      refine ⟨39856448079535240301473583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26570965386356826867649055 39856448079535240301473583)
      ·
        refine ⟨59784672119302860452210375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39856448079535240301473583 59784672119302860452210375)
        ·
          refine ⟨89677008178954290678315563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59784672119302860452210375 89677008178954290678315563)
          ·
            refine ⟨134515512268431436017473345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89677008178954290678315563 134515512268431436017473345)
            ·
              refine ⟨100886634201323577013105009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134515512268431436017473345 100886634201323577013105009)
              ·
                refine ⟨75664975650992682759828757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100886634201323577013105009 75664975650992682759828757)
                ·
                  refine ⟨3546795733640282004366973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75664975650992682759828757 3546795733640282004366973)
                  ·
                    refine ⟨1330048400115105751637615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3546795733640282004366973 1330048400115105751637615)
                    ·
                      rfl

theorem cell22_3885390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_3885390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885390 prefixEnd_3885390 := by exact prefixLift 3885390
  have htrace : WordTrace (prefixWord ++ tailWord_3885390) baseStart_3885390 baseEnd_3885390 := by
    simpa [prefixWord, tailWord_3885390, baseEnd_3885390] using wordTrace_append hprefix tailTrace_3885390
  have hstable : (prefixWord ++ tailWord_3885390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885390).length < 2 ^ (prefixWord ++ tailWord_3885390).sum := by decide
  have hdescent : baseEnd_3885390 < baseStart_3885390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885420 : List Nat := [2, 2, 1, 1, 7, 9]
def baseStart_3885420 : Nat := 118140960795 + 3885420 * 2 ^ 59
def prefixEnd_3885420 : Nat := 4983230072969 + 3 ^ 40 * 3885420 * 2
def baseEnd_3885420 : Nat := 16420477404051798436883

theorem tailTrace_3885420 : CollatzResearch.WordTrace tailWord_3885420 prefixEnd_3885420 16420477404051798436883 := by
  unfold tailWord_3885420
  simp only [CollatzResearch.WordTrace]
  refine ⟨70856454791897195875526857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94475273055862927834035809 70856454791897195875526857)
  ·
    refine ⟨53142341093922896906645143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70856454791897195875526857 53142341093922896906645143)
    ·
      refine ⟨79713511640884345359967715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53142341093922896906645143 79713511640884345359967715)
      ·
        refine ⟨119570267461326518039951573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79713511640884345359967715 119570267461326518039951573)
        ·
          refine ⟨2802428143624840266561365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 119570267461326518039951573 2802428143624840266561365)
          ·
            refine ⟨16420477404051798436883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2802428143624840266561365 16420477404051798436883)
            ·
              rfl

theorem cell22_3885420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 9].length) (baseStart_3885420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885420 prefixEnd_3885420 := by exact prefixLift 3885420
  have htrace : WordTrace (prefixWord ++ tailWord_3885420) baseStart_3885420 baseEnd_3885420 := by
    simpa [prefixWord, tailWord_3885420, baseEnd_3885420] using wordTrace_append hprefix tailTrace_3885420
  have hstable : (prefixWord ++ tailWord_3885420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885420).length < 2 ^ (prefixWord ++ tailWord_3885420).sum := by decide
  have hdescent : baseEnd_3885420 < baseStart_3885420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885452 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_3885452 : Nat := 118140960795 + 3885452 * 2 ^ 59
def prefixEnd_3885452 : Nat := 4983230072969 + 3 ^ 40 * 3885452 * 2
def baseEnd_3885452 : Nat := 1330069623982158256587425

theorem tailTrace_3885452 : CollatzResearch.WordTrace tailWord_3885452 prefixEnd_3885452 1330069623982158256587425 := by
  unfold tailWord_3885452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70857038359839230608109305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94476051146452307477479073 70857038359839230608109305)
  ·
    refine ⟨53142778769879422956081979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70857038359839230608109305 53142778769879422956081979)
    ·
      refine ⟨79714168154819134434122969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53142778769879422956081979 79714168154819134434122969)
      ·
        refine ⟨59785626116114350825592227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79714168154819134434122969 59785626116114350825592227)
        ·
          refine ⟨89678439174171526238388341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59785626116114350825592227 89678439174171526238388341)
          ·
            refine ⟨8407353672578580584848907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89678439174171526238388341 8407353672578580584848907)
            ·
              refine ⟨12611030508867870877273361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8407353672578580584848907 12611030508867870877273361)
              ·
                refine ⟨9458272881650903157955021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12611030508867870877273361 9458272881650903157955021)
                ·
                  refine ⟨3546852330619088684233133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9458272881650903157955021 3546852330619088684233133)
                  ·
                    refine ⟨1330069623982158256587425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3546852330619088684233133 1330069623982158256587425)
                    ·
                      rfl

theorem cell22_3885452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_3885452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885452 prefixEnd_3885452 := by exact prefixLift 3885452
  have htrace : WordTrace (prefixWord ++ tailWord_3885452) baseStart_3885452 baseEnd_3885452 := by
    simpa [prefixWord, tailWord_3885452, baseEnd_3885452] using wordTrace_append hprefix tailTrace_3885452
  have hstable : (prefixWord ++ tailWord_3885452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885452).length < 2 ^ (prefixWord ++ tailWord_3885452).sum := by decide
  have hdescent : baseEnd_3885452 < baseStart_3885452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885462 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3885462 : Nat := 118140960795 + 3885462 * 2 ^ 59
def prefixEnd_3885462 : Nat := 4983230072969 + 3 ^ 40 * 3885462 * 2
def baseEnd_3885462 : Nat := 1330073047186521563837395

theorem tailTrace_3885462 : CollatzResearch.WordTrace tailWord_3885462 prefixEnd_3885462 1330073047186521563837395 := by
  unfold tailWord_3885462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8857152590602639557755165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94476294299761488616055093 8857152590602639557755165)
  ·
    refine ⟨3321432221475989834158187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8857152590602639557755165 3321432221475989834158187)
    ·
      refine ⟨4982148332213984751237281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321432221475989834158187 4982148332213984751237281)
      ·
        refine ⟨3736611249160488563427961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4982148332213984751237281 3736611249160488563427961)
        ·
          refine ⟨2802458436870366422570971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3736611249160488563427961 2802458436870366422570971)
          ·
            refine ⟨4203687655305549633856457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802458436870366422570971 4203687655305549633856457)
            ·
              refine ⟨3152765741479162225392343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4203687655305549633856457 3152765741479162225392343)
              ·
                refine ⟨4729148612218743338088515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152765741479162225392343 4729148612218743338088515)
                ·
                  refine ⟨7093722918328115007132773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729148612218743338088515 7093722918328115007132773)
                  ·
                    refine ⟨1330073047186521563837395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093722918328115007132773 1330073047186521563837395)
                    ·
                      rfl

theorem cell22_3885462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3885462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885462 prefixEnd_3885462 := by exact prefixLift 3885462
  have htrace : WordTrace (prefixWord ++ tailWord_3885462) baseStart_3885462 baseEnd_3885462 := by
    simpa [prefixWord, tailWord_3885462, baseEnd_3885462] using wordTrace_append hprefix tailTrace_3885462
  have hstable : (prefixWord ++ tailWord_3885462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885462).length < 2 ^ (prefixWord ++ tailWord_3885462).sum := by decide
  have hdescent : baseEnd_3885462 < baseStart_3885462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885512 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_3885512 : Nat := 118140960795 + 3885512 * 2 ^ 59
def prefixEnd_3885512 : Nat := 4983230072969 + 3 ^ 40 * 3885512 * 2
def baseEnd_3885512 : Nat := 1330090163208338100087241

theorem tailTrace_3885512 : CollatzResearch.WordTrace tailWord_3885512 prefixEnd_3885512 1330090163208338100087241 := by
  unfold tailWord_3885512
  simp only [CollatzResearch.WordTrace]
  refine ⟨70858132549730545731701395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94477510066307394308935193 70858132549730545731701395)
  ·
    refine ⟨106287198824595818597552093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70858132549730545731701395 106287198824595818597552093)
    ·
      refine ⟨39857699559223431974082035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106287198824595818597552093 39857699559223431974082035)
      ·
        refine ⟨59786549338835147961123053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39857699559223431974082035 59786549338835147961123053)
        ·
          refine ⟨22419956002063180485421145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59786549338835147961123053 22419956002063180485421145)
          ·
            refine ⟨16814967001547385364065859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22419956002063180485421145 16814967001547385364065859)
            ·
              refine ⟨25222450502321078046098789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16814967001547385364065859 25222450502321078046098789)
              ·
                refine ⟨4729209469185202133643523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25222450502321078046098789 4729209469185202133643523)
                ·
                  refine ⟨7093814203777803200465285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729209469185202133643523 7093814203777803200465285)
                  ·
                    refine ⟨1330090163208338100087241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093814203777803200465285 1330090163208338100087241)
                    ·
                      rfl

theorem cell22_3885512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_3885512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885512 prefixEnd_3885512 := by exact prefixLift 3885512
  have htrace : WordTrace (prefixWord ++ tailWord_3885512) baseStart_3885512 baseEnd_3885512 := by
    simpa [prefixWord, tailWord_3885512, baseEnd_3885512] using wordTrace_append hprefix tailTrace_3885512
  have hstable : (prefixWord ++ tailWord_3885512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885512).length < 2 ^ (prefixWord ++ tailWord_3885512).sum := by decide
  have hdescent : baseEnd_3885512 < baseStart_3885512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885555 : List Nat := [1, 1, 1, 2, 2, 2, 6, 7]
def baseStart_3885555 : Nat := 118140960795 + 3885555 * 2 ^ 59
def prefixEnd_3885555 : Nat := 4983230072969 + 3 ^ 40 * 3885555 * 2
def baseEnd_3885555 : Nat := 147789431443011146806901

theorem tailTrace_3885555 : CollatzResearch.WordTrace tailWord_3885555 prefixEnd_3885555 147789431443011146806901 := by
  unfold tailWord_3885555
  simp only [CollatzResearch.WordTrace]
  refine ⟨141717833438305309807218119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94478555625536873204812079 141717833438305309807218119)
  ·
    refine ⟨212576750157457964710827179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141717833438305309807218119 212576750157457964710827179)
    ·
      refine ⟨318865125236186947066240769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212576750157457964710827179 318865125236186947066240769)
      ·
        refine ⟨239148843927140210299680577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318865125236186947066240769 239148843927140210299680577)
        ·
          refine ⟨179361632945355157724760433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239148843927140210299680577 179361632945355157724760433)
          ·
            refine ⟨134521224709016368293570325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179361632945355157724760433 134521224709016368293570325)
            ·
              refine ⟨6305682408235142263761109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134521224709016368293570325 6305682408235142263761109)
              ·
                refine ⟨147789431443011146806901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6305682408235142263761109 147789431443011146806901)
                ·
                  rfl

theorem cell22_3885555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 7].length) (baseStart_3885555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885555 prefixEnd_3885555 := by exact prefixLift 3885555
  have htrace : WordTrace (prefixWord ++ tailWord_3885555) baseStart_3885555 baseEnd_3885555 := by
    simpa [prefixWord, tailWord_3885555, baseEnd_3885555] using wordTrace_append hprefix tailTrace_3885555
  have hstable : (prefixWord ++ tailWord_3885555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885555).length < 2 ^ (prefixWord ++ tailWord_3885555).sum := by decide
  have hdescent : baseEnd_3885555 < baseStart_3885555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885572 : List Nat := [2, 3, 2, 3, 1, 1, 2, 8]
def baseStart_3885572 : Nat := 118140960795 + 3885572 * 2 ^ 59
def prefixEnd_3885572 : Nat := 4983230072969 + 3 ^ 40 * 3885572 * 2
def baseEnd_3885572 : Nat := 147790078048279771509673

theorem tailTrace_3885572 : CollatzResearch.WordTrace tailWord_3885572 prefixEnd_3885572 147790078048279771509673 := by
  unfold tailWord_3885572
  simp only [CollatzResearch.WordTrace]
  refine ⟨70859226739621860855293485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94478968986162481140391313 70859226739621860855293485)
  ·
    refine ⟨26572210027358197820735057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70859226739621860855293485 26572210027358197820735057)
    ·
      refine ⟨19929157520518648365551293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26572210027358197820735057 19929157520518648365551293)
      ·
        refine ⟨7473434070194493137081735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19929157520518648365551293 7473434070194493137081735)
        ·
          refine ⟨11210151105291739705622603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473434070194493137081735 11210151105291739705622603)
          ·
            refine ⟨16815226657937609558433905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11210151105291739705622603 16815226657937609558433905)
            ·
              refine ⟨12611419993453207168825429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16815226657937609558433905 12611419993453207168825429)
              ·
                refine ⟨147790078048279771509673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12611419993453207168825429 147790078048279771509673)
                ·
                  rfl

theorem cell22_3885572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_3885572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885572 prefixEnd_3885572 := by exact prefixLift 3885572
  have htrace : WordTrace (prefixWord ++ tailWord_3885572) baseStart_3885572 baseEnd_3885572 := by
    simpa [prefixWord, tailWord_3885572, baseEnd_3885572] using wordTrace_append hprefix tailTrace_3885572
  have hstable : (prefixWord ++ tailWord_3885572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885572).length < 2 ^ (prefixWord ++ tailWord_3885572).sum := by decide
  have hdescent : baseEnd_3885572 < baseStart_3885572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885617 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 5]
def baseStart_3885617 : Nat := 118140960795 + 3885617 * 2 ^ 59
def prefixEnd_3885617 : Nat := 4983230072969 + 3 ^ 40 * 3885617 * 2
def baseEnd_3885617 : Nat := 443375368951384275403973

theorem tailTrace_3885617 : CollatzResearch.WordTrace tailWord_3885617 prefixEnd_3885617 443375368951384275403973 := by
  unfold tailWord_3885617
  simp only [CollatzResearch.WordTrace]
  refine ⟨141720094764080694395975105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94480063176053796263983403 141720094764080694395975105)
  ·
    refine ⟨106290071073060520796981329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141720094764080694395975105 106290071073060520796981329)
    ·
      refine ⟨79717553304795390597735997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106290071073060520796981329 79717553304795390597735997)
      ·
        refine ⟨29894082489298271474150999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79717553304795390597735997 29894082489298271474150999)
        ·
          refine ⟨44841123733947407211226499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29894082489298271474150999 44841123733947407211226499)
          ·
            refine ⟨67261685600921110816839749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44841123733947407211226499 67261685600921110816839749)
            ·
              refine ⟨12611566050172708278157453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67261685600921110816839749 12611566050172708278157453)
              ·
                refine ⟨4729337268814765604309045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12611566050172708278157453 4729337268814765604309045)
                ·
                  refine ⟨443375368951384275403973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4729337268814765604309045 443375368951384275403973)
                  ·
                    rfl

theorem cell22_3885617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_3885617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885617 prefixEnd_3885617 := by exact prefixLift 3885617
  have htrace : WordTrace (prefixWord ++ tailWord_3885617) baseStart_3885617 baseEnd_3885617 := by
    simpa [prefixWord, tailWord_3885617, baseEnd_3885617] using wordTrace_append hprefix tailTrace_3885617
  have hstable : (prefixWord ++ tailWord_3885617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885617).length < 2 ^ (prefixWord ++ tailWord_3885617).sum := by decide
  have hdescent : baseEnd_3885617 < baseStart_3885617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885692 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_3885692 : Nat := 118140960795 + 3885692 * 2 ^ 59
def prefixEnd_3885692 : Nat := 4983230072969 + 3 ^ 40 * 3885692 * 2
def baseEnd_3885692 : Nat := 1330151780886877630586689

theorem tailTrace_3885692 : CollatzResearch.WordTrace tailWord_3885692 prefixEnd_3885692 1330151780886877630586689 := by
  unfold tailWord_3885692
  simp only [CollatzResearch.WordTrace]
  refine ⟨70861415119404491102477665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94481886825872654803303553 70861415119404491102477665)
  ·
    refine ⟨53146061339553368326858249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70861415119404491102477665 53146061339553368326858249)
    ·
      refine ⟨39859546004665026245143687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53146061339553368326858249 39859546004665026245143687)
      ·
        refine ⟨59789319006997539367715531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39859546004665026245143687 59789319006997539367715531)
        ·
          refine ⟨89683978510496309051573297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59789319006997539367715531 89683978510496309051573297)
          ·
            refine ⟨67262983882872231788679973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89683978510496309051573297 67262983882872231788679973)
            ·
              refine ⟨12611809478038543460377495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67262983882872231788679973 12611809478038543460377495)
              ·
                refine ⟨18917714217057815190566243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12611809478038543460377495 18917714217057815190566243)
                ·
                  refine ⟨28376571325586722785849365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18917714217057815190566243 28376571325586722785849365)
                  ·
                    refine ⟨1330151780886877630586689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28376571325586722785849365 1330151780886877630586689)
                    ·
                      rfl

theorem cell22_3885692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_3885692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885692 prefixEnd_3885692 := by exact prefixLift 3885692
  have htrace : WordTrace (prefixWord ++ tailWord_3885692) baseStart_3885692 baseEnd_3885692 := by
    simpa [prefixWord, tailWord_3885692, baseEnd_3885692] using wordTrace_append hprefix tailTrace_3885692
  have hstable : (prefixWord ++ tailWord_3885692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885692).length < 2 ^ (prefixWord ++ tailWord_3885692).sum := by decide
  have hdescent : baseEnd_3885692 < baseStart_3885692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885696 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 4]
def baseStart_3885696 : Nat := 118140960795 + 3885696 * 2 ^ 59
def prefixEnd_3885696 : Nat := 4983230072969 + 3 ^ 40 * 3885696 * 2
def baseEnd_3885696 : Nat := 443384383389540984495559

theorem tailTrace_3885696 : CollatzResearch.WordTrace tailWord_3885696 prefixEnd_3885696 443384383389540984495559 := by
  unfold tailWord_3885696
  simp only [CollatzResearch.WordTrace]
  refine ⟨70861488065397245444050471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94481984087196327258733961 70861488065397245444050471)
  ·
    refine ⟨106292232098095868166075707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70861488065397245444050471 106292232098095868166075707)
    ·
      refine ⟨159438348147143802249113561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106292232098095868166075707 159438348147143802249113561)
      ·
        refine ⟨119578761110357851686835171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159438348147143802249113561 119578761110357851686835171)
        ·
          refine ⟨179368141665536777530252757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119578761110357851686835171 179368141665536777530252757)
          ·
            refine ⟨4203940820286018223365299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 179368141665536777530252757 4203940820286018223365299)
            ·
              refine ⟨6305911230429027335047949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203940820286018223365299 6305911230429027335047949)
              ·
                refine ⟨2364716711410885250642981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6305911230429027335047949 2364716711410885250642981)
                ·
                  refine ⟨443384383389540984495559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2364716711410885250642981 443384383389540984495559)
                  ·
                    rfl

theorem cell22_3885696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_3885696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885696 prefixEnd_3885696 := by exact prefixLift 3885696
  have htrace : WordTrace (prefixWord ++ tailWord_3885696) baseStart_3885696 baseEnd_3885696 := by
    simpa [prefixWord, tailWord_3885696, baseEnd_3885696] using wordTrace_append hprefix tailTrace_3885696
  have hstable : (prefixWord ++ tailWord_3885696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885696).length < 2 ^ (prefixWord ++ tailWord_3885696).sum := by decide
  have hdescent : baseEnd_3885696 < baseStart_3885696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885724 : List Nat := [2, 2, 3, 2, 2, 2, 2, 7]
def baseStart_3885724 : Nat := 118140960795 + 3885724 * 2 ^ 59
def prefixEnd_3885724 : Nat := 4983230072969 + 3 ^ 40 * 3885724 * 2
def baseEnd_3885724 : Nat := 147795859460093357087399

theorem tailTrace_3885724 : CollatzResearch.WordTrace tailWord_3885724 prefixEnd_3885724 147795859460093357087399 := by
  unfold tailWord_3885724
  simp only [CollatzResearch.WordTrace]
  refine ⟨70861998687346525835060113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94482664916462034446746817 70861998687346525835060113)
  ·
    refine ⟨53146499015509894376295085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70861998687346525835060113 53146499015509894376295085)
    ·
      refine ⟨19929937130816210391110657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53146499015509894376295085 19929937130816210391110657)
      ·
        refine ⟨14947452848112157793332993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19929937130816210391110657 14947452848112157793332993)
        ·
          refine ⟨11210589636084118344999745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14947452848112157793332993 11210589636084118344999745)
          ·
            refine ⟨8407942227063088758749809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11210589636084118344999745 8407942227063088758749809)
            ·
              refine ⟨6305956670297316569062357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407942227063088758749809 6305956670297316569062357)
              ·
                refine ⟨147795859460093357087399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6305956670297316569062357 147795859460093357087399)
                ·
                  rfl

theorem cell22_3885724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_3885724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885724 prefixEnd_3885724 := by exact prefixLift 3885724
  have htrace : WordTrace (prefixWord ++ tailWord_3885724) baseStart_3885724 baseEnd_3885724 := by
    simpa [prefixWord, tailWord_3885724, baseEnd_3885724] using wordTrace_append hprefix tailTrace_3885724
  have hstable : (prefixWord ++ tailWord_3885724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885724).length < 2 ^ (prefixWord ++ tailWord_3885724).sum := by decide
  have hdescent : baseEnd_3885724 < baseStart_3885724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885784 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_3885784 : Nat := 118140960795 + 3885784 * 2 ^ 59
def prefixEnd_3885784 : Nat := 4983230072969 + 3 ^ 40 * 3885784 * 2
def baseEnd_3885784 : Nat := 1330183274367020057286407

theorem tailTrace_3885784 : CollatzResearch.WordTrace tailWord_3885784 prefixEnd_3885784 1330183274367020057286407 := by
  unfold tailWord_3885784
  simp only [CollatzResearch.WordTrace]
  refine ⟨70863092877237840958652203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94484123836317121278202937 70863092877237840958652203)
  ·
    refine ⟨106294639315856761437978305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70863092877237840958652203 106294639315856761437978305)
    ·
      refine ⟨79720979486892571078483729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106294639315856761437978305 79720979486892571078483729)
      ·
        refine ⟨59790734615169428308862797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79720979486892571078483729 59790734615169428308862797)
        ·
          refine ⟨22421525480688535615823549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59790734615169428308862797 22421525480688535615823549)
          ·
            refine ⟨8408072055258200855933831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22421525480688535615823549 8408072055258200855933831)
            ·
              refine ⟨12612108082887301283900747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8408072055258200855933831 12612108082887301283900747)
              ·
                refine ⟨18918162124330951925851121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12612108082887301283900747 18918162124330951925851121)
                ·
                  refine ⟨14188621593248213944388341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18918162124330951925851121 14188621593248213944388341)
                  ·
                    refine ⟨1330183274367020057286407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14188621593248213944388341 1330183274367020057286407)
                    ·
                      rfl

theorem cell22_3885784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_3885784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885784 prefixEnd_3885784 := by exact prefixLift 3885784
  have htrace : WordTrace (prefixWord ++ tailWord_3885784) baseStart_3885784 baseEnd_3885784 := by
    simpa [prefixWord, tailWord_3885784, baseEnd_3885784] using wordTrace_append hprefix tailTrace_3885784
  have hstable : (prefixWord ++ tailWord_3885784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885784).length < 2 ^ (prefixWord ++ tailWord_3885784).sum := by decide
  have hdescent : baseEnd_3885784 < baseStart_3885784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885814 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3885814 : Nat := 118140960795 + 3885814 * 2 ^ 59
def prefixEnd_3885814 : Nat := 4983230072969 + 3 ^ 40 * 3885814 * 2
def baseEnd_3885814 : Nat := 443397847993369993012105

theorem tailTrace_3885814 : CollatzResearch.WordTrace tailWord_3885814 prefixEnd_3885814 443397847993369993012105 := by
  unfold tailWord_3885814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8857954996522937315056031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94484853296244664693930997 8857954996522937315056031)
  ·
    refine ⟨13286932494784405972584047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8857954996522937315056031 13286932494784405972584047)
    ·
      refine ⟨19930398742176608958876071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13286932494784405972584047 19930398742176608958876071)
      ·
        refine ⟨29895598113264913438314107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19930398742176608958876071 29895598113264913438314107)
        ·
          refine ⟨44843397169897370157471161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29895598113264913438314107 44843397169897370157471161)
          ·
            refine ⟨33632547877423027618103371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44843397169897370157471161 33632547877423027618103371)
            ·
              refine ⟨50448821816134541427155057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33632547877423027618103371 50448821816134541427155057)
              ·
                refine ⟨37836616362100906070366293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50448821816134541427155057 37836616362100906070366293)
                ·
                  refine ⟨443397847993369993012105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37836616362100906070366293 443397847993369993012105)
                  ·
                    rfl

theorem cell22_3885814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3885814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885814 prefixEnd_3885814 := by exact prefixLift 3885814
  have htrace : WordTrace (prefixWord ++ tailWord_3885814) baseStart_3885814 baseEnd_3885814 := by
    simpa [prefixWord, tailWord_3885814, baseEnd_3885814] using wordTrace_append hprefix tailTrace_3885814
  have hstable : (prefixWord ++ tailWord_3885814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885814).length < 2 ^ (prefixWord ++ tailWord_3885814).sum := by decide
  have hdescent : baseEnd_3885814 < baseStart_3885814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885831 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 6]
def baseStart_3885831 : Nat := 118140960795 + 3885831 * 2 ^ 59
def prefixEnd_3885831 : Nat := 4983230072969 + 3 ^ 40 * 3885831 * 2
def baseEnd_3885831 : Nat := 443399787809175867120421

theorem tailTrace_3885831 : CollatzResearch.WordTrace tailWord_3885831 prefixEnd_3885831 443399787809175867120421 := by
  unfold tailWord_3885831
  simp only [CollatzResearch.WordTrace]
  refine ⟨141727899985305408944265347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94485266656870272629510231 141727899985305408944265347)
  ·
    refine ⟨212591849977958113416398021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141727899985305408944265347 212591849977958113416398021)
    ·
      refine ⟨39860971870867146265574629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212591849977958113416398021 39860971870867146265574629)
      ·
        refine ⟨7473932225787589924795243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39860971870867146265574629 7473932225787589924795243)
        ·
          refine ⟨11210898338681384887192865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473932225787589924795243 11210898338681384887192865)
          ·
            refine ⟨8408173754011038665394649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11210898338681384887192865 8408173754011038665394649)
            ·
              refine ⟨6306130315508278999045987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8408173754011038665394649 6306130315508278999045987)
              ·
                refine ⟨9459195473262418498568981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6306130315508278999045987 9459195473262418498568981)
                ·
                  refine ⟨443399787809175867120421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9459195473262418498568981 443399787809175867120421)
                  ·
                    rfl

theorem cell22_3885831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 6].length) (baseStart_3885831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885831 prefixEnd_3885831 := by exact prefixLift 3885831
  have htrace : WordTrace (prefixWord ++ tailWord_3885831) baseStart_3885831 baseEnd_3885831 := by
    simpa [prefixWord, tailWord_3885831, baseEnd_3885831] using wordTrace_append hprefix tailTrace_3885831
  have hstable : (prefixWord ++ tailWord_3885831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885831).length < 2 ^ (prefixWord ++ tailWord_3885831).sum := by decide
  have hdescent : baseEnd_3885831 < baseStart_3885831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885942 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_3885942 : Nat := 118140960795 + 3885942 * 2 ^ 59
def prefixEnd_3885942 : Nat := 4983230072969 + 3 ^ 40 * 3885942 * 2
def baseEnd_3885942 : Nat := 1330237360995960311835923

theorem tailTrace_3885942 : CollatzResearch.WordTrace tailWord_3885942 prefixEnd_3885942 1330237360995960311835923 := by
  unfold tailWord_3885942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858246780493954681347255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94487965658602183267704053 8858246780493954681347255)
  ·
    refine ⟨13287370170740932022020883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8858246780493954681347255 13287370170740932022020883)
    ·
      refine ⟨19931055256111398033031325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13287370170740932022020883 19931055256111398033031325)
      ·
        refine ⟨7474145721041774262386747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19931055256111398033031325 7474145721041774262386747)
        ·
          refine ⟨11211218581562661393580121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7474145721041774262386747 11211218581562661393580121)
          ·
            refine ⟨8408413936171996045185091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11211218581562661393580121 8408413936171996045185091)
            ·
              refine ⟨12612620904257994067777637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8408413936171996045185091 12612620904257994067777637)
              ·
                refine ⟨2364866419548373887708307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12612620904257994067777637 2364866419548373887708307)
                ·
                  refine ⟨3547299629322560831562461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364866419548373887708307 3547299629322560831562461)
                  ·
                    refine ⟨1330237360995960311835923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547299629322560831562461 1330237360995960311835923)
                    ·
                      rfl

theorem cell22_3885942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_3885942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885942 prefixEnd_3885942 := by exact prefixLift 3885942
  have htrace : WordTrace (prefixWord ++ tailWord_3885942) baseStart_3885942 baseEnd_3885942 := by
    simpa [prefixWord, tailWord_3885942, baseEnd_3885942] using wordTrace_append hprefix tailTrace_3885942
  have hstable : (prefixWord ++ tailWord_3885942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885942).length < 2 ^ (prefixWord ++ tailWord_3885942).sum := by decide
  have hdescent : baseEnd_3885942 < baseStart_3885942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885981 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3885981 : Nat := 118140960795 + 3885981 * 2 ^ 59
def prefixEnd_3885981 : Nat := 4983230072969 + 3 ^ 40 * 3885981 * 2
def baseEnd_3885981 : Nat := 1330250711492977210110803

theorem tailTrace_3885981 : CollatzResearch.WordTrace tailWord_3885981 prefixEnd_3885981 1330250711492977210110803 := by
  unfold tailWord_3885981
  simp only [CollatzResearch.WordTrace]
  refine ⟨141733370934761984562225797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94488913956507989708150531 141733370934761984562225797)
  ·
    refine ⟨26575007050267872105417337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141733370934761984562225797 26575007050267872105417337)
    ·
      refine ⟨19931255287700904079063003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26575007050267872105417337 19931255287700904079063003)
      ·
        refine ⟨29896882931551356118594505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19931255287700904079063003 29896882931551356118594505)
        ·
          refine ⟨22422662198663517088945879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29896882931551356118594505 22422662198663517088945879)
          ·
            refine ⟨33633993297995275633418819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22422662198663517088945879 33633993297995275633418819)
            ·
              refine ⟨50450989946992913450128229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33633993297995275633418819 50450989946992913450128229)
              ·
                refine ⟨9459560615061171271899043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50450989946992913450128229 9459560615061171271899043)
                ·
                  refine ⟨14189340922591756907848565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459560615061171271899043 14189340922591756907848565)
                  ·
                    refine ⟨1330250711492977210110803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14189340922591756907848565 1330250711492977210110803)
                    ·
                      rfl

theorem cell22_3885981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3885981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885981 prefixEnd_3885981 := by exact prefixLift 3885981
  have htrace : WordTrace (prefixWord ++ tailWord_3885981) baseStart_3885981 baseEnd_3885981 := by
    simpa [prefixWord, tailWord_3885981, baseEnd_3885981] using wordTrace_append hprefix tailTrace_3885981
  have hstable : (prefixWord ++ tailWord_3885981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885981).length < 2 ^ (prefixWord ++ tailWord_3885981).sum := by decide
  have hdescent : baseEnd_3885981 < baseStart_3885981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885983 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 4]
def baseStart_3885983 : Nat := 118140960795 + 3885983 * 2 ^ 59
def prefixEnd_3885983 : Nat := 4983230072969 + 3 ^ 40 * 3885983 * 2
def baseEnd_3885983 : Nat := 443417132044616623853599

theorem tailTrace_3885983 : CollatzResearch.WordTrace tailWord_3885983 prefixEnd_3885983 443417132044616623853599 := by
  unfold tailWord_3885983
  simp only [CollatzResearch.WordTrace]
  refine ⟨141733443880754738903798603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94488962587169825935865735 141733443880754738903798603)
  ·
    refine ⟨212600165821132108355697905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141733443880754738903798603 212600165821132108355697905)
    ·
      refine ⟨159450124365849081266773429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212600165821132108355697905 159450124365849081266773429)
      ·
        refine ⟨14948449159298351368760009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159450124365849081266773429 14948449159298351368760009)
        ·
          refine ⟨11211336869473763526570007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14948449159298351368760009 11211336869473763526570007)
          ·
            refine ⟨16817005304210645289855011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11211336869473763526570007 16817005304210645289855011)
            ·
              refine ⟨25225507956315967934782517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16817005304210645289855011 25225507956315967934782517)
              ·
                refine ⟨2364891370904621993885861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25225507956315967934782517 2364891370904621993885861)
                ·
                  refine ⟨443417132044616623853599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2364891370904621993885861 443417132044616623853599)
                  ·
                    rfl

theorem cell22_3885983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 4].length) (baseStart_3885983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885983 prefixEnd_3885983 := by exact prefixLift 3885983
  have htrace : WordTrace (prefixWord ++ tailWord_3885983) baseStart_3885983 baseEnd_3885983 := by
    simpa [prefixWord, tailWord_3885983, baseEnd_3885983] using wordTrace_append hprefix tailTrace_3885983
  have hstable : (prefixWord ++ tailWord_3885983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885983).length < 2 ^ (prefixWord ++ tailWord_3885983).sum := by decide
  have hdescent : baseEnd_3885983 < baseStart_3885983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885985 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 1, 4]
def baseStart_3885985 : Nat := 118140960795 + 3885985 * 2 ^ 59
def prefixEnd_3885985 : Nat := 4983230072969 + 3 ^ 40 * 3885985 * 2
def baseEnd_3885985 : Nat := 1330252080774722533010791

theorem tailTrace_3885985 : CollatzResearch.WordTrace tailWord_3885985 prefixEnd_3885985 1330252080774722533010791 := by
  unfold tailWord_3885985
  simp only [CollatzResearch.WordTrace]
  refine ⟨141733516826747493245371409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94489011217831662163580939 141733516826747493245371409)
  ·
    refine ⟨106300137620060619934028557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141733516826747493245371409 106300137620060619934028557)
    ·
      refine ⟨39862551607522732475260709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106300137620060619934028557 39862551607522732475260709)
      ·
        refine ⟨7474228426410512339111383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39862551607522732475260709 7474228426410512339111383)
        ·
          refine ⟨11211342639615768508667075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7474228426410512339111383 11211342639615768508667075)
          ·
            refine ⟨16817013959423652763000613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11211342639615768508667075 16817013959423652763000613)
            ·
              refine ⟨3153190117391934893062615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16817013959423652763000613 3153190117391934893062615)
              ·
                refine ⟨4729785176087902339593923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153190117391934893062615 4729785176087902339593923)
                ·
                  refine ⟨7094677764131853509390885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729785176087902339593923 7094677764131853509390885)
                  ·
                    refine ⟨1330252080774722533010791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7094677764131853509390885 1330252080774722533010791)
                    ·
                      rfl

theorem cell22_3885985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_3885985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3885985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3885985 prefixEnd_3885985 := by exact prefixLift 3885985
  have htrace : WordTrace (prefixWord ++ tailWord_3885985) baseStart_3885985 baseEnd_3885985 := by
    simpa [prefixWord, tailWord_3885985, baseEnd_3885985] using wordTrace_append hprefix tailTrace_3885985
  have hstable : (prefixWord ++ tailWord_3885985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885985).length < 2 ^ (prefixWord ++ tailWord_3885985).sum := by decide
  have hdescent : baseEnd_3885985 < baseStart_3885985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886056 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_3886056 : Nat := 118140960795 + 3886056 * 2 ^ 59
def prefixEnd_3886056 : Nat := 4983230072969 + 3 ^ 40 * 3886056 * 2
def baseEnd_3886056 : Nat := 443425461841900671495191

theorem tailTrace_3886056 : CollatzResearch.WordTrace tailWord_3886056 prefixEnd_3886056 443425461841900671495191 := by
  unfold tailWord_3886056
  simp only [CollatzResearch.WordTrace]
  refine ⟨70868053204745136185603011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94490737606326848247470681 70868053204745136185603011)
  ·
    refine ⟨106302079807117704278404517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70868053204745136185603011 106302079807117704278404517)
    ·
      refine ⟨19931639963834569552200847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106302079807117704278404517 19931639963834569552200847)
      ·
        refine ⟨29897459945751854328301271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19931639963834569552200847 29897459945751854328301271)
        ·
          refine ⟨44846189918627781492451907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29897459945751854328301271 44846189918627781492451907)
          ·
            refine ⟨67269284877941672238677861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44846189918627781492451907 67269284877941672238677861)
            ·
              refine ⟨12612990914614063544752099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67269284877941672238677861 12612990914614063544752099)
              ·
                refine ⟨18919486371921095317128149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12612990914614063544752099 18919486371921095317128149)
                ·
                  refine ⟨443425461841900671495191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18919486371921095317128149 443425461841900671495191)
                  ·
                    rfl

theorem cell22_3886056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_3886056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886056 prefixEnd_3886056 := by exact prefixLift 3886056
  have htrace : WordTrace (prefixWord ++ tailWord_3886056) baseStart_3886056 baseEnd_3886056 := by
    simpa [prefixWord, tailWord_3886056, baseEnd_3886056] using wordTrace_append hprefix tailTrace_3886056
  have hstable : (prefixWord ++ tailWord_3886056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886056).length < 2 ^ (prefixWord ++ tailWord_3886056).sum := by decide
  have hdescent : baseEnd_3886056 < baseStart_3886056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886066 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_3886066 : Nat := 118140960795 + 3886066 * 2 ^ 59
def prefixEnd_3886066 : Nat := 4983230072969 + 3 ^ 40 * 3886066 * 2
def baseEnd_3886066 : Nat := 1330279808730065321735543

theorem tailTrace_3886066 : CollatzResearch.WordTrace tailWord_3886066 prefixEnd_3886066 1330279808730065321735543 := by
  unfold tailWord_3886066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35434117784863511019767513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94490980759636029386046701 35434117784863511019767513)
  ·
    refine ⟨26575588338647633264825635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35434117784863511019767513 26575588338647633264825635)
    ·
      refine ⟨39863382507971449897238453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26575588338647633264825635 39863382507971449897238453)
      ·
        refine ⟨3737192110122323427866105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39863382507971449897238453 3737192110122323427866105)
        ·
          refine ⟨2802894082591742570899579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3737192110122323427866105 2802894082591742570899579)
          ·
            refine ⟨4204341123887613856349369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802894082591742570899579 4204341123887613856349369)
            ·
              refine ⟨3153255842915710392262027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204341123887613856349369 3153255842915710392262027)
              ·
                refine ⟨4729883764373565588393041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153255842915710392262027 4729883764373565588393041)
                ·
                  refine ⟨3547412823280174191294781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729883764373565588393041 3547412823280174191294781)
                  ·
                    refine ⟨1330279808730065321735543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547412823280174191294781 1330279808730065321735543)
                    ·
                      rfl

theorem cell22_3886066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_3886066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886066 prefixEnd_3886066 := by exact prefixLift 3886066
  have htrace : WordTrace (prefixWord ++ tailWord_3886066) baseStart_3886066 baseEnd_3886066 := by
    simpa [prefixWord, tailWord_3886066, baseEnd_3886066] using wordTrace_append hprefix tailTrace_3886066
  have hstable : (prefixWord ++ tailWord_3886066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886066).length < 2 ^ (prefixWord ++ tailWord_3886066).sum := by decide
  have hdescent : baseEnd_3886066 < baseStart_3886066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886131 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_3886131 : Nat := 118140960795 + 3886131 * 2 ^ 59
def prefixEnd_3886131 : Nat := 4983230072969 + 3 ^ 40 * 3886131 * 2
def baseEnd_3886131 : Nat := 1330302059558426818860343

theorem tailTrace_3886131 : CollatzResearch.WordTrace tailWord_3886131 prefixEnd_3886131 1330302059558426818860343 := by
  unfold tailWord_3886131
  simp only [CollatzResearch.WordTrace]
  refine ⟨141738841884218560180186247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94492561256145706786790831 141738841884218560180186247)
  ·
    refine ⟨212608262826327840270279371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141738841884218560180186247 212608262826327840270279371)
    ·
      refine ⟨318912394239491760405419057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212608262826327840270279371 318912394239491760405419057)
      ·
        refine ⟨239184295679618820304064293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318912394239491760405419057 239184295679618820304064293)
        ·
          refine ⟨44847055439928528807012055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239184295679618820304064293 44847055439928528807012055)
          ·
            refine ⟨67270583159892793210518083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44847055439928528807012055 67270583159892793210518083)
            ·
              refine ⟨100905874739839189815777125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67270583159892793210518083 100905874739839189815777125)
              ·
                refine ⟨18919851513719848090458211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100905874739839189815777125 18919851513719848090458211)
                ·
                  refine ⟨28379777270579772135687317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18919851513719848090458211 28379777270579772135687317)
                  ·
                    refine ⟨1330302059558426818860343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28379777270579772135687317 1330302059558426818860343)
                    ·
                      rfl

theorem cell22_3886131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_3886131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886131 prefixEnd_3886131 := by exact prefixLift 3886131
  have htrace : WordTrace (prefixWord ++ tailWord_3886131) baseStart_3886131 baseEnd_3886131 := by
    simpa [prefixWord, tailWord_3886131, baseEnd_3886131] using wordTrace_append hprefix tailTrace_3886131
  have hstable : (prefixWord ++ tailWord_3886131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886131).length < 2 ^ (prefixWord ++ tailWord_3886131).sum := by decide
  have hdescent : baseEnd_3886131 < baseStart_3886131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886133 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3886133 : Nat := 118140960795 + 3886133 * 2 ^ 59
def prefixEnd_3886133 : Nat := 4983230072969 + 3 ^ 40 * 3886133 * 2
def baseEnd_3886133 : Nat := 1330302744199299480310337

theorem tailTrace_3886133 : CollatzResearch.WordTrace tailWord_3886133 prefixEnd_3886133 1330302744199299480310337 := by
  unfold tailWord_3886133
  simp only [CollatzResearch.WordTrace]
  refine ⟨141738914830211314521759053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94492609886807543014506035 141738914830211314521759053)
  ·
    refine ⟨53152093061329242945659645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141738914830211314521759053 53152093061329242945659645)
    ·
      refine ⟨19932034897998466104622367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53152093061329242945659645 19932034897998466104622367)
      ·
        refine ⟨29898052346997699156933551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19932034897998466104622367 29898052346997699156933551)
        ·
          refine ⟨44847078520496548735400327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29898052346997699156933551 44847078520496548735400327)
          ·
            refine ⟨67270617780744823103100491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44847078520496548735400327 67270617780744823103100491)
            ·
              refine ⟨100905926671117234654650737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67270617780744823103100491 100905926671117234654650737)
              ·
                refine ⟨75679445003337925990988053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100905926671117234654650737 75679445003337925990988053)
                ·
                  refine ⟨3547473984531465280827565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75679445003337925990988053 3547473984531465280827565)
                  ·
                    refine ⟨1330302744199299480310337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547473984531465280827565 1330302744199299480310337)
                    ·
                      rfl

theorem cell22_3886133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3886133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886133 prefixEnd_3886133 := by exact prefixLift 3886133
  have htrace : WordTrace (prefixWord ++ tailWord_3886133) baseStart_3886133 baseEnd_3886133 := by
    simpa [prefixWord, tailWord_3886133, baseEnd_3886133] using wordTrace_append hprefix tailTrace_3886133
  have hstable : (prefixWord ++ tailWord_3886133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886133).length < 2 ^ (prefixWord ++ tailWord_3886133).sum := by decide
  have hdescent : baseEnd_3886133 < baseStart_3886133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886184 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 1, 5]
def baseStart_3886184 : Nat := 118140960795 + 3886184 * 2 ^ 59
def prefixEnd_3886184 : Nat := 4983230072969 + 3 ^ 40 * 3886184 * 2
def baseEnd_3886184 : Nat := 1330320202541552347285181

theorem tailTrace_3886184 : CollatzResearch.WordTrace tailWord_3886184 prefixEnd_3886184 1330320202541552347285181 := by
  unfold tailWord_3886184
  simp only [CollatzResearch.WordTrace]
  refine ⟨70870387476513275115932803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94493849968684366821243737 70870387476513275115932803)
  ·
    refine ⟨106305581214769912673899205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70870387476513275115932803 106305581214769912673899205)
    ·
      refine ⟨19932296477769358626356101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106305581214769912673899205 19932296477769358626356101)
      ·
        refine ⟨3737305589581754742441769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19932296477769358626356101 3737305589581754742441769)
        ·
          refine ⟨2802979192186316056831327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3737305589581754742441769 2802979192186316056831327)
          ·
            refine ⟨4204468788279474085246991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802979192186316056831327 4204468788279474085246991)
            ·
              refine ⟨6306703182419211127870487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204468788279474085246991 6306703182419211127870487)
              ·
                refine ⟨9460054773628816691805731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6306703182419211127870487 9460054773628816691805731)
                ·
                  refine ⟨14190082160443225037708597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9460054773628816691805731 14190082160443225037708597)
                  ·
                    refine ⟨1330320202541552347285181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14190082160443225037708597 1330320202541552347285181)
                    ·
                      rfl

theorem cell22_3886184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_3886184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886184 prefixEnd_3886184 := by exact prefixLift 3886184
  have htrace : WordTrace (prefixWord ++ tailWord_3886184) baseStart_3886184 baseEnd_3886184 := by
    simpa [prefixWord, tailWord_3886184, baseEnd_3886184] using wordTrace_append hprefix tailTrace_3886184
  have hstable : (prefixWord ++ tailWord_3886184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886184).length < 2 ^ (prefixWord ++ tailWord_3886184).sum := by decide
  have hdescent : baseEnd_3886184 < baseStart_3886184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886242 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3886242 : Nat := 118140960795 + 3886242 * 2 ^ 59
def prefixEnd_3886242 : Nat := 4983230072969 + 3 ^ 40 * 3886242 * 2
def baseEnd_3886242 : Nat := 443446685708953176445001

theorem tailTrace_3886242 : CollatzResearch.WordTrace tailWord_3886242 prefixEnd_3886242 443446685708953176445001 := by
  unfold tailWord_3886242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35435722596704106534369245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94495260257877617424984653 35435722596704106534369245)
  ·
    refine ⟨13288395973764039950388467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35435722596704106534369245 13288395973764039950388467)
    ·
      refine ⟨19932593960646059925582701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13288395973764039950388467 19932593960646059925582701)
      ·
        refine ⟨7474722735242272472093513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19932593960646059925582701 7474722735242272472093513)
        ·
          refine ⟨5606042051431704354070135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7474722735242272472093513 5606042051431704354070135)
          ·
            refine ⟨8409063077147556531105203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606042051431704354070135 8409063077147556531105203)
            ·
              refine ⟨12613594615721334796657805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8409063077147556531105203 12613594615721334796657805)
              ·
                refine ⟨4730097980895500548746677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12613594615721334796657805 4730097980895500548746677)
                ·
                  refine ⟨443446685708953176445001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4730097980895500548746677 443446685708953176445001)
                  ·
                    rfl

theorem cell22_3886242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3886242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886242 prefixEnd_3886242 := by exact prefixLift 3886242
  have htrace : WordTrace (prefixWord ++ tailWord_3886242) baseStart_3886242 baseEnd_3886242 := by
    simpa [prefixWord, tailWord_3886242, baseEnd_3886242] using wordTrace_append hprefix tailTrace_3886242
  have hstable : (prefixWord ++ tailWord_3886242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886242).length < 2 ^ (prefixWord ++ tailWord_3886242).sum := by decide
  have hdescent : baseEnd_3886242 < baseStart_3886242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886255 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 1, 4]
def baseStart_3886255 : Nat := 118140960795 + 3886255 * 2 ^ 59
def prefixEnd_3886255 : Nat := 4983230072969 + 3 ^ 40 * 3886255 * 2
def baseEnd_3886255 : Nat := 1330344507292531828759963

theorem tailTrace_3886255 : CollatzResearch.WordTrace tailWord_3886255 prefixEnd_3886255 1330344507292531828759963 := by
  unfold tailWord_3886255
  simp only [CollatzResearch.WordTrace]
  refine ⟨141743364535769329357700219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94495576357179552905133479 141743364535769329357700219)
  ·
    refine ⟨212615046803653994036550329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141743364535769329357700219 212615046803653994036550329)
    ·
      refine ⟨159461285102740495527412747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212615046803653994036550329 159461285102740495527412747)
      ·
        refine ⟨239191927654110743291119121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159461285102740495527412747 239191927654110743291119121)
        ·
          refine ⟨179393945740583057468339341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239191927654110743291119121 179393945740583057468339341)
          ·
            refine ⟨67272729652718646550627253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179393945740583057468339341 67272729652718646550627253)
            ·
              refine ⟨6306818404942373114121305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67272729652718646550627253 6306818404942373114121305)
              ·
                refine ⟨4730113803706779835590979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6306818404942373114121305 4730113803706779835590979)
                ·
                  refine ⟨7095170705560169753386469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730113803706779835590979 7095170705560169753386469)
                  ·
                    refine ⟨1330344507292531828759963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095170705560169753386469 1330344507292531828759963)
                    ·
                      rfl

theorem cell22_3886255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_3886255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886255 prefixEnd_3886255 := by exact prefixLift 3886255
  have htrace : WordTrace (prefixWord ++ tailWord_3886255) baseStart_3886255 baseEnd_3886255 := by
    simpa [prefixWord, tailWord_3886255, baseEnd_3886255] using wordTrace_append hprefix tailTrace_3886255
  have hstable : (prefixWord ++ tailWord_3886255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886255).length < 2 ^ (prefixWord ++ tailWord_3886255).sum := by decide
  have hdescent : baseEnd_3886255 < baseStart_3886255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886283 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 4, 4]
def baseStart_3886283 : Nat := 118140960795 + 3886283 * 2 ^ 59
def prefixEnd_3886283 : Nat := 4983230072969 + 3 ^ 40 * 3886283 * 2
def baseEnd_3886283 : Nat := 1330354092264749089059877

theorem tailTrace_3886283 : CollatzResearch.WordTrace tailWord_3886283 prefixEnd_3886283 1330354092264749089059877 := by
  unfold tailWord_3886283
  simp only [CollatzResearch.WordTrace]
  refine ⟨141744385779667890139719503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94496257186445260093146335 141744385779667890139719503)
  ·
    refine ⟨212616578669501835209579255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141744385779667890139719503 212616578669501835209579255)
    ·
      refine ⟨318924868004252752814368883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212616578669501835209579255 318924868004252752814368883)
      ·
        refine ⟨478387302006379129221553325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318924868004252752814368883 478387302006379129221553325)
        ·
          refine ⟨179395238252392173458082497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478387302006379129221553325 179395238252392173458082497)
          ·
            refine ⟨134546428689294130093561873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179395238252392173458082497 134546428689294130093561873)
            ·
              refine ⟨100909821516970597570171405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134546428689294130093561873 100909821516970597570171405)
              ·
                refine ⟨37841183068863974088814277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100909821516970597570171405 37841183068863974088814277)
                ·
                  refine ⟨7095221825411995141652677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37841183068863974088814277 7095221825411995141652677)
                  ·
                    refine ⟨1330354092264749089059877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095221825411995141652677 1330354092264749089059877)
                    ·
                      rfl

theorem cell22_3886283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_3886283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886283 prefixEnd_3886283 := by exact prefixLift 3886283
  have htrace : WordTrace (prefixWord ++ tailWord_3886283) baseStart_3886283 baseEnd_3886283 := by
    simpa [prefixWord, tailWord_3886283, baseEnd_3886283] using wordTrace_append hprefix tailTrace_3886283
  have hstable : (prefixWord ++ tailWord_3886283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886283).length < 2 ^ (prefixWord ++ tailWord_3886283).sum := by decide
  have hdescent : baseEnd_3886283 < baseStart_3886283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886315 : List Nat := [1, 1, 1, 1, 2, 7, 3, 6]
def baseStart_3886315 : Nat := 118140960795 + 3886315 * 2 ^ 59
def prefixEnd_3886315 : Nat := 4983230072969 + 3 ^ 40 * 3886315 * 2
def baseEnd_3886315 : Nat := 147818338502079074695531

theorem tailTrace_3886315 : CollatzResearch.WordTrace tailWord_3886315 prefixEnd_3886315 147818338502079074695531 := by
  unfold tailWord_3886315
  simp only [CollatzResearch.WordTrace]
  refine ⟨141745552915551959604884399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94497035277034639736589599 141745552915551959604884399)
  ·
    refine ⟨212618329373327939407326599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141745552915551959604884399 212618329373327939407326599)
    ·
      refine ⟨318927494059991909110989899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212618329373327939407326599 318927494059991909110989899)
      ·
        refine ⟨478391241089987863666484849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318927494059991909110989899 478391241089987863666484849)
        ·
          refine ⟨358793430817490897749863637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478391241089987863666484849 358793430817490897749863637)
          ·
            refine ⟨8409221034784942916012429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 358793430817490897749863637 8409221034784942916012429)
            ·
              refine ⟨3153457888044353593504661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8409221034784942916012429 3153457888044353593504661)
              ·
                refine ⟨147818338502079074695531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3153457888044353593504661 147818338502079074695531)
                ·
                  rfl

theorem cell22_3886315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 6].length) (baseStart_3886315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886315 prefixEnd_3886315 := by exact prefixLift 3886315
  have htrace : WordTrace (prefixWord ++ tailWord_3886315) baseStart_3886315 baseEnd_3886315 := by
    simpa [prefixWord, tailWord_3886315, baseEnd_3886315] using wordTrace_append hprefix tailTrace_3886315
  have hstable : (prefixWord ++ tailWord_3886315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886315).length < 2 ^ (prefixWord ++ tailWord_3886315).sum := by decide
  have hdescent : baseEnd_3886315 < baseStart_3886315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886317 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3886317 : Nat := 118140960795 + 3886317 * 2 ^ 59
def prefixEnd_3886317 : Nat := 4983230072969 + 3 ^ 40 * 3886317 * 2
def baseEnd_3886317 : Nat := 1330365731159584333709773

theorem tailTrace_3886317 : CollatzResearch.WordTrace tailWord_3886317 prefixEnd_3886317 1330365731159584333709773 := by
  unfold tailWord_3886317
  simp only [CollatzResearch.WordTrace]
  refine ⟨141745625861544713946457205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94497083907696475964304803 141745625861544713946457205)
  ·
    refine ⟨13288652424519816932480363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141745625861544713946457205 13288652424519816932480363)
    ·
      refine ⟨19932978636779725398720545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13288652424519816932480363 19932978636779725398720545)
      ·
        refine ⟨14949733977584794049040409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19932978636779725398720545 14949733977584794049040409)
        ·
          refine ⟨11212300483188595536780307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14949733977584794049040409 11212300483188595536780307)
          ·
            refine ⟨16818450724782893305170461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212300483188595536780307 16818450724782893305170461)
            ·
              refine ⟨6306919021793584989438923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16818450724782893305170461 6306919021793584989438923)
              ·
                refine ⟨9460378532690377484158385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6306919021793584989438923 9460378532690377484158385)
                ·
                  refine ⟨7095283899517783113118789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9460378532690377484158385 7095283899517783113118789)
                  ·
                    refine ⟨1330365731159584333709773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095283899517783113118789 1330365731159584333709773)
                    ·
                      rfl

theorem cell22_3886317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3886317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886317 prefixEnd_3886317 := by exact prefixLift 3886317
  have htrace : WordTrace (prefixWord ++ tailWord_3886317) baseStart_3886317 baseEnd_3886317 := by
    simpa [prefixWord, tailWord_3886317, baseEnd_3886317] using wordTrace_append hprefix tailTrace_3886317
  have hstable : (prefixWord ++ tailWord_3886317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886317).length < 2 ^ (prefixWord ++ tailWord_3886317).sum := by decide
  have hdescent : baseEnd_3886317 < baseStart_3886317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886330 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_3886330 : Nat := 118140960795 + 3886330 * 2 ^ 59
def prefixEnd_3886330 : Nat := 4983230072969 + 3 ^ 40 * 3886330 * 2
def baseEnd_3886330 : Nat := 1330370181325256633134733

theorem tailTrace_3886330 : CollatzResearch.WordTrace tailWord_3886330 prefixEnd_3886330 1330370181325256633134733 := by
  unfold tailWord_3886330
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436525002624404291670111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94497400006998411444453629 35436525002624404291670111)
  ·
    refine ⟨53154787503936606437505167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35436525002624404291670111 53154787503936606437505167)
    ·
      refine ⟨79732181255904909656257751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53154787503936606437505167 79732181255904909656257751)
      ·
        refine ⟨119598271883857364484386627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79732181255904909656257751 119598271883857364484386627)
        ·
          refine ⟨179397407825786046726579941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119598271883857364484386627 179397407825786046726579941)
          ·
            refine ⟨33637013967334883761233739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179397407825786046726579941 33637013967334883761233739)
            ·
              refine ⟨50455520951002325641850609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33637013967334883761233739 50455520951002325641850609)
              ·
                refine ⟨37841640713251744231387957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50455520951002325641850609 37841640713251744231387957)
                ·
                  refine ⟨3547653816867351021692621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37841640713251744231387957 3547653816867351021692621)
                  ·
                    refine ⟨1330370181325256633134733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547653816867351021692621 1330370181325256633134733)
                    ·
                      rfl

theorem cell22_3886330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_3886330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886330 prefixEnd_3886330 := by exact prefixLift 3886330
  have htrace : WordTrace (prefixWord ++ tailWord_3886330) baseStart_3886330 baseEnd_3886330 := by
    simpa [prefixWord, tailWord_3886330, baseEnd_3886330] using wordTrace_append hprefix tailTrace_3886330
  have hstable : (prefixWord ++ tailWord_3886330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886330).length < 2 ^ (prefixWord ++ tailWord_3886330).sum := by decide
  have hdescent : baseEnd_3886330 < baseStart_3886330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886347 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 3, 3]
def baseStart_3886347 : Nat := 118140960795 + 3886347 * 2 ^ 59
def prefixEnd_3886347 : Nat := 4983230072969 + 3 ^ 40 * 3886347 * 2
def baseEnd_3886347 : Nat := 1330376000772674255459681

theorem tailTrace_3886347 : CollatzResearch.WordTrace tailWord_3886347 prefixEnd_3886347 1330376000772674255459681 := by
  unfold tailWord_3886347
  simp only [CollatzResearch.WordTrace]
  refine ⟨141746720051436029070049295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94497813367624019380032863 141746720051436029070049295)
  ·
    refine ⟨212620080077154043605073943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141746720051436029070049295 212620080077154043605073943)
    ·
      refine ⟨318930120115731065407610915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212620080077154043605073943 318930120115731065407610915)
      ·
        refine ⟨478395180173596598111416373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318930120115731065407610915 478395180173596598111416373)
        ·
          refine ⟨44849548141274681072945285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 478395180173596598111416373 44849548141274681072945285)
          ·
            refine ⟨8409290276489002701177241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44849548141274681072945285 8409290276489002701177241)
            ·
              refine ⟨6306967707366752025882931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8409290276489002701177241 6306967707366752025882931)
              ·
                refine ⟨9460451561050128038824397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6306967707366752025882931 9460451561050128038824397)
                ·
                  refine ⟨3547669335393798014559149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9460451561050128038824397 3547669335393798014559149)
                  ·
                    refine ⟨1330376000772674255459681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547669335393798014559149 1330376000772674255459681)
                    ·
                      rfl

theorem cell22_3886347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 3].length) (baseStart_3886347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886347 prefixEnd_3886347 := by exact prefixLift 3886347
  have htrace : WordTrace (prefixWord ++ tailWord_3886347) baseStart_3886347 baseEnd_3886347 := by
    simpa [prefixWord, tailWord_3886347, baseEnd_3886347] using wordTrace_append hprefix tailTrace_3886347
  have hstable : (prefixWord ++ tailWord_3886347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886347).length < 2 ^ (prefixWord ++ tailWord_3886347).sum := by decide
  have hdescent : baseEnd_3886347 < baseStart_3886347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886366 : List Nat := [4, 3, 2, 1, 2, 2, 2, 6]
def baseStart_3886366 : Nat := 118140960795 + 3886366 * 2 ^ 59
def prefixEnd_3886366 : Nat := 4983230072969 + 3 ^ 40 * 3886366 * 2
def baseEnd_3886366 : Nat := 147820278317884948803847

theorem tailTrace_3886366 : CollatzResearch.WordTrace tailWord_3886366 prefixEnd_3886366 147820278317884948803847 := by
  unfold tailWord_3886366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718426629795899414373869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94498275358911463543327301 17718426629795899414373869)
  ·
    refine ⟨6644409986173462280390201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17718426629795899414373869 6644409986173462280390201)
    ·
      refine ⟨4983307489630096710292651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6644409986173462280390201 4983307489630096710292651)
      ·
        refine ⟨7474961234445145065438977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983307489630096710292651 7474961234445145065438977)
        ·
          refine ⟨5606220925833858799079233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7474961234445145065438977 5606220925833858799079233)
          ·
            refine ⟨4204665694375394099309425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5606220925833858799079233 4204665694375394099309425)
            ·
              refine ⟨3153499270781545574482069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204665694375394099309425 3153499270781545574482069)
              ·
                refine ⟨147820278317884948803847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3153499270781545574482069 147820278317884948803847)
                ·
                  rfl

theorem cell22_3886366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_3886366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886366 prefixEnd_3886366 := by exact prefixLift 3886366
  have htrace : WordTrace (prefixWord ++ tailWord_3886366) baseStart_3886366 baseEnd_3886366 := by
    simpa [prefixWord, tailWord_3886366, baseEnd_3886366] using wordTrace_append hprefix tailTrace_3886366
  have hstable : (prefixWord ++ tailWord_3886366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886366).length < 2 ^ (prefixWord ++ tailWord_3886366).sum := by decide
  have hdescent : baseEnd_3886366 < baseStart_3886366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886467 : List Nat := [1, 1, 1, 3, 5, 3, 1, 7]
def baseStart_3886467 : Nat := 118140960795 + 3886467 * 2 ^ 59
def prefixEnd_3886467 : Nat := 4983230072969 + 3 ^ 40 * 3886467 * 2
def baseEnd_3886467 : Nat := 147824119913892660273257

theorem tailTrace_3886467 : CollatzResearch.WordTrace tailWord_3886467 prefixEnd_3886467 147824119913892660273257 := by
  unfold tailWord_3886467
  simp only [CollatzResearch.WordTrace]
  refine ⟨141751096811001289564417655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94500731207334193042945103 141751096811001289564417655)
  ·
    refine ⟨212626645216501934346626483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141751096811001289564417655 212626645216501934346626483)
    ·
      refine ⟨318939967824752901519939725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212626645216501934346626483 318939967824752901519939725)
      ·
        refine ⟨119602487934282338069977397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318939967824752901519939725 119602487934282338069977397)
        ·
          refine ⟨11212733243838969194060381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119602487934282338069977397 11212733243838969194060381)
          ·
            refine ⟨4204774966439613447772643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11212733243838969194060381 4204774966439613447772643)
            ·
              refine ⟨6307162449659420171658965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204774966439613447772643 6307162449659420171658965)
              ·
                refine ⟨147824119913892660273257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6307162449659420171658965 147824119913892660273257)
                ·
                  rfl

theorem cell22_3886467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 7].length) (baseStart_3886467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886467 prefixEnd_3886467 := by exact prefixLift 3886467
  have htrace : WordTrace (prefixWord ++ tailWord_3886467) baseStart_3886467 baseEnd_3886467 := by
    simpa [prefixWord, tailWord_3886467, baseEnd_3886467] using wordTrace_append hprefix tailTrace_3886467
  have hstable : (prefixWord ++ tailWord_3886467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886467).length < 2 ^ (prefixWord ++ tailWord_3886467).sum := by decide
  have hdescent : baseEnd_3886467 < baseStart_3886467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886484 : List Nat := [2, 4, 2, 1, 2, 2, 3, 6]
def baseStart_3886484 : Nat := 118140960795 + 3886484 * 2 ^ 59
def prefixEnd_3886484 : Nat := 4983230072969 + 3 ^ 40 * 3886484 * 2
def baseEnd_3886484 : Nat := 147824766519161284976029

theorem tailTrace_3886484 : CollatzResearch.WordTrace tailWord_3886484 prefixEnd_3886484 147824766519161284976029 := by
  unfold tailWord_3886484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70875858425969850733893253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94501144567959800978524337 70875858425969850733893253)
  ·
    refine ⟨13289223454869347012604985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70875858425969850733893253 13289223454869347012604985)
    ·
      refine ⟨9966917591152010259453739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13289223454869347012604985 9966917591152010259453739)
      ·
        refine ⟨14950376386728015389180609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9966917591152010259453739 14950376386728015389180609)
        ·
          refine ⟨11212782290046011541885457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14950376386728015389180609 11212782290046011541885457)
          ·
            refine ⟨8409586717534508656414093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11212782290046011541885457 8409586717534508656414093)
            ·
              refine ⟨3153595019075440746155285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8409586717534508656414093 3153595019075440746155285)
              ·
                refine ⟨147824766519161284976029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3153595019075440746155285 147824766519161284976029)
                ·
                  rfl

theorem cell22_3886484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 6].length) (baseStart_3886484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886484 prefixEnd_3886484 := by exact prefixLift 3886484
  have htrace : WordTrace (prefixWord ++ tailWord_3886484) baseStart_3886484 baseEnd_3886484 := by
    simpa [prefixWord, tailWord_3886484, baseEnd_3886484] using wordTrace_append hprefix tailTrace_3886484
  have hstable : (prefixWord ++ tailWord_3886484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886484).length < 2 ^ (prefixWord ++ tailWord_3886484).sum := by decide
  have hdescent : baseEnd_3886484 < baseStart_3886484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886542 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_3886542 : Nat := 118140960795 + 3886542 * 2 ^ 59
def prefixEnd_3886542 : Nat := 4983230072969 + 3 ^ 40 * 3886542 * 2
def baseEnd_3886542 : Nat := 1330442753257758746834083

theorem tailTrace_3886542 : CollatzResearch.WordTrace tailWord_3886542 prefixEnd_3886542 1330442753257758746834083 := by
  unfold tailWord_3886542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17719229035716197171674735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94502554857153051582265253 17719229035716197171674735)
  ·
    refine ⟨26578843553574295757512103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17719229035716197171674735 26578843553574295757512103)
    ·
      refine ⟨39868265330361443636268155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26578843553574295757512103 39868265330361443636268155)
      ·
        refine ⟨59802397995542165454402233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39868265330361443636268155 59802397995542165454402233)
        ·
          refine ⟨44851798496656624090801675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59802397995542165454402233 44851798496656624090801675)
          ·
            refine ⟨67277697744984936136202513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44851798496656624090801675 67277697744984936136202513)
            ·
              refine ⟨50458273308738702102151885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67277697744984936136202513 50458273308738702102151885)
              ·
                refine ⟨18921852490777013288306957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50458273308738702102151885 18921852490777013288306957)
                ·
                  refine ⟨7095694684041379983115109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18921852490777013288306957 7095694684041379983115109)
                  ·
                    refine ⟨1330442753257758746834083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095694684041379983115109 1330442753257758746834083)
                    ·
                      rfl

theorem cell22_3886542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_3886542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886542 prefixEnd_3886542 := by exact prefixLift 3886542
  have htrace : WordTrace (prefixWord ++ tailWord_3886542) baseStart_3886542 baseEnd_3886542 := by
    simpa [prefixWord, tailWord_3886542, baseEnd_3886542] using wordTrace_append hprefix tailTrace_3886542
  have hstable : (prefixWord ++ tailWord_3886542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886542).length < 2 ^ (prefixWord ++ tailWord_3886542).sum := by decide
  have hdescent : baseEnd_3886542 < baseStart_3886542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886550 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3886550 : Nat := 118140960795 + 3886550 * 2 ^ 59
def prefixEnd_3886550 : Nat := 4983230072969 + 3 ^ 40 * 3886550 * 2
def baseEnd_3886550 : Nat := 1330445491821249392634059

theorem tailTrace_3886550 : CollatzResearch.WordTrace tailWord_3886550 prefixEnd_3886550 1330445491821249392634059 := by
  unfold tailWord_3886550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8859632754356287171230569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94502749379800396493126069 8859632754356287171230569)
  ·
    refine ⟨6644724565767215378422927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8859632754356287171230569 6644724565767215378422927)
    ·
      refine ⟨9967086848650823067634391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6644724565767215378422927 9967086848650823067634391)
      ·
        refine ⟨14950630272976234601451587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967086848650823067634391 14950630272976234601451587)
        ·
          refine ⟨22425945409464351902177381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14950630272976234601451587 22425945409464351902177381)
          ·
            refine ⟨4204864764274565981658259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22425945409464351902177381 4204864764274565981658259)
            ·
              refine ⟨6307297146411848972487389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204864764274565981658259 6307297146411848972487389)
              ·
                refine ⟨2365236429904443364682771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6307297146411848972487389 2365236429904443364682771)
                ·
                  refine ⟨3547854644856665047024157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365236429904443364682771 3547854644856665047024157)
                  ·
                    refine ⟨1330445491821249392634059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547854644856665047024157 1330445491821249392634059)
                    ·
                      rfl

theorem cell22_3886550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3886550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886550 prefixEnd_3886550 := by exact prefixLift 3886550
  have htrace : WordTrace (prefixWord ++ tailWord_3886550) baseStart_3886550 baseEnd_3886550 := by
    simpa [prefixWord, tailWord_3886550, baseEnd_3886550] using wordTrace_append hprefix tailTrace_3886550
  have hstable : (prefixWord ++ tailWord_3886550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886550).length < 2 ^ (prefixWord ++ tailWord_3886550).sum := by decide
  have hdescent : baseEnd_3886550 < baseStart_3886550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886593 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3886593 : Nat := 118140960795 + 3886593 * 2 ^ 59
def prefixEnd_3886593 : Nat := 4983230072969 + 3 ^ 40 * 3886593 * 2
def baseEnd_3886593 : Nat := 1330460211600011613808927

theorem tailTrace_3886593 : CollatzResearch.WordTrace tailWord_3886593 prefixEnd_3886593 1330460211600011613808927 := by
  unfold tailWord_3886593
  simp only [CollatzResearch.WordTrace]
  refine ⟨141755692408544813083504433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94503794939029875389002955 141755692408544813083504433)
  ·
    refine ⟨106316769306408609812628325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141755692408544813083504433 106316769306408609812628325)
    ·
      refine ⟨19934394244951614339867811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106316769306408609812628325 19934394244951614339867811)
      ·
        refine ⟨29901591367427421509801717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19934394244951614339867811 29901591367427421509801717)
        ·
          refine ⟨2803274190696320766543911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29901591367427421509801717 2803274190696320766543911)
          ·
            refine ⟨4204911286044481149815867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803274190696320766543911 4204911286044481149815867)
            ·
              refine ⟨6307366929066721724723801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204911286044481149815867 6307366929066721724723801)
              ·
                refine ⟨4730525196800041293542851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307366929066721724723801 4730525196800041293542851)
                ·
                  refine ⟨7095787795200061940314277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730525196800041293542851 7095787795200061940314277)
                  ·
                    refine ⟨1330460211600011613808927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095787795200061940314277 1330460211600011613808927)
                    ·
                      rfl

theorem cell22_3886593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3886593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886593 prefixEnd_3886593 := by exact prefixLift 3886593
  have htrace : WordTrace (prefixWord ++ tailWord_3886593) baseStart_3886593 baseEnd_3886593 := by
    simpa [prefixWord, tailWord_3886593, baseEnd_3886593] using wordTrace_append hprefix tailTrace_3886593
  have hstable : (prefixWord ++ tailWord_3886593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886593).length < 2 ^ (prefixWord ++ tailWord_3886593).sum := by decide
  have hdescent : baseEnd_3886593 < baseStart_3886593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886602 : List Nat := [3, 1, 2, 2, 2, 2, 2, 8]
def baseStart_3886602 : Nat := 118140960795 + 3886602 * 2 ^ 59
def prefixEnd_3886602 : Nat := 4983230072969 + 3 ^ 40 * 3886602 * 2
def baseEnd_3886602 : Nat := 147829254720437621148211

theorem tailTrace_3886602 : CollatzResearch.WordTrace tailWord_3886602 prefixEnd_3886602 147829254720437621148211 := by
  unfold tailWord_3886602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35439005166378051905145515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94504013777008138413721373 35439005166378051905145515)
  ·
    refine ⟨53158507749567077857718273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35439005166378051905145515 53158507749567077857718273)
    ·
      refine ⟨39868880812175308393288705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53158507749567077857718273 39868880812175308393288705)
      ·
        refine ⟨29901660609131481294966529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39868880812175308393288705 29901660609131481294966529)
        ·
          refine ⟨22426245456848610971224897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29901660609131481294966529 22426245456848610971224897)
          ·
            refine ⟨16819684092636458228418673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22426245456848610971224897 16819684092636458228418673)
            ·
              refine ⟨12614763069477343671314005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16819684092636458228418673 12614763069477343671314005)
              ·
                refine ⟨147829254720437621148211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12614763069477343671314005 147829254720437621148211)
                ·
                  rfl

theorem cell22_3886602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_3886602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886602 prefixEnd_3886602 := by exact prefixLift 3886602
  have htrace : WordTrace (prefixWord ++ tailWord_3886602) baseStart_3886602 baseEnd_3886602 := by
    simpa [prefixWord, tailWord_3886602, baseEnd_3886602] using wordTrace_append hprefix tailTrace_3886602
  have hstable : (prefixWord ++ tailWord_3886602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886602).length < 2 ^ (prefixWord ++ tailWord_3886602).sum := by decide
  have hdescent : baseEnd_3886602 < baseStart_3886602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886668 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_3886668 : Nat := 118140960795 + 3886668 * 2 ^ 59
def prefixEnd_3886668 : Nat := 4983230072969 + 3 ^ 40 * 3886668 * 2
def baseEnd_3886668 : Nat := 1330485885632736418183697

theorem tailTrace_3886668 : CollatzResearch.WordTrace tailWord_3886668 prefixEnd_3886668 1330485885632736418183697 := by
  unfold tailWord_3886668
  simp only [CollatzResearch.WordTrace]
  refine ⟨70879213941636550446242329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94505618588848733928323105 70879213941636550446242329)
  ·
    refine ⟨53159410456227412834681747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70879213941636550446242329 53159410456227412834681747)
    ·
      refine ⟨79739115684341119252022621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53159410456227412834681747 79739115684341119252022621)
      ·
        refine ⟨29902168381627919719508483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79739115684341119252022621 29902168381627919719508483)
        ·
          refine ⟨44853252572441879579262725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29902168381627919719508483 44853252572441879579262725)
          ·
            refine ⟨8409984857332852421111761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44853252572441879579262725 8409984857332852421111761)
            ·
              refine ⟨6307488642999639315833821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8409984857332852421111761 6307488642999639315833821)
              ·
                refine ⟨2365308241124864743437683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6307488642999639315833821 2365308241124864743437683)
                ·
                  refine ⟨3547962361687297115156525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365308241124864743437683 3547962361687297115156525)
                  ·
                    refine ⟨1330485885632736418183697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547962361687297115156525 1330485885632736418183697)
                    ·
                      rfl

theorem cell22_3886668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_3886668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886668 prefixEnd_3886668 := by exact prefixLift 3886668
  have htrace : WordTrace (prefixWord ++ tailWord_3886668) baseStart_3886668 baseEnd_3886668 := by
    simpa [prefixWord, tailWord_3886668, baseEnd_3886668] using wordTrace_append hprefix tailTrace_3886668
  have hstable : (prefixWord ++ tailWord_3886668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886668).length < 2 ^ (prefixWord ++ tailWord_3886668).sum := by decide
  have hdescent : baseEnd_3886668 < baseStart_3886668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886685 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3886685 : Nat := 118140960795 + 3886685 * 2 ^ 59
def prefixEnd_3886685 : Nat := 4983230072969 + 3 ^ 40 * 3886685 * 2
def baseEnd_3886685 : Nat := 1330491705080154040508645

theorem tailTrace_3886685 : CollatzResearch.WordTrace tailWord_3886685 prefixEnd_3886685 1330491705080154040508645 := by
  unfold tailWord_3886685
  simp only [CollatzResearch.WordTrace]
  refine ⟨141759047924211512795853509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94506031949474341863902339 141759047924211512795853509)
  ·
    refine ⟨26579821485789658649222533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141759047924211512795853509 26579821485789658649222533)
    ·
      refine ⟨4983716528585560996729225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26579821485789658649222533 4983716528585560996729225)
      ·
        refine ⟨3737787396439170747546919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4983716528585560996729225 3737787396439170747546919)
        ·
          refine ⟨5606681094658756121320379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3737787396439170747546919 5606681094658756121320379)
          ·
            refine ⟨8410021641988134181980569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606681094658756121320379 8410021641988134181980569)
            ·
              refine ⟨6307516231491100636485427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8410021641988134181980569 6307516231491100636485427)
              ·
                refine ⟨9461274347236650954728141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307516231491100636485427 9461274347236650954728141)
                ·
                  refine ⟨3547977880213744108023053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9461274347236650954728141 3547977880213744108023053)
                  ·
                    refine ⟨1330491705080154040508645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547977880213744108023053 1330491705080154040508645)
                    ·
                      rfl

theorem cell22_3886685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3886685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886685 prefixEnd_3886685 := by exact prefixLift 3886685
  have htrace : WordTrace (prefixWord ++ tailWord_3886685) baseStart_3886685 baseEnd_3886685 := by
    simpa [prefixWord, tailWord_3886685, baseEnd_3886685] using wordTrace_append hprefix tailTrace_3886685
  have hstable : (prefixWord ++ tailWord_3886685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886685).length < 2 ^ (prefixWord ++ tailWord_3886685).sum := by decide
  have hdescent : baseEnd_3886685 < baseStart_3886685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886743 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 4]
def baseStart_3886743 : Nat := 118140960795 + 3886743 * 2 ^ 59
def prefixEnd_3886743 : Nat := 4983230072969 + 3 ^ 40 * 3886743 * 2
def baseEnd_3886743 : Nat := 443503853221820407519489

theorem tailTrace_3886743 : CollatzResearch.WordTrace tailWord_3886743 prefixEnd_3886743 443503853221820407519489 := by
  unfold tailWord_3886743
  simp only [CollatzResearch.WordTrace]
  refine ⟨141761163358001388701464883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94507442238667592467643255 141761163358001388701464883)
  ·
    refine ⟨212641745037002083052197325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141761163358001388701464883 212641745037002083052197325)
    ·
      refine ⟨79740654388875781144573997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212641745037002083052197325 79740654388875781144573997)
      ·
        refine ⟨29902745395828417929215249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79740654388875781144573997 29902745395828417929215249)
        ·
          refine ⟨22427059046871313446911437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29902745395828417929215249 22427059046871313446911437)
          ·
            refine ⟨8410147142576742542591789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22427059046871313446911437 8410147142576742542591789)
            ·
              refine ⟨3153805178466278453471921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8410147142576742542591789 3153805178466278453471921)
              ·
                refine ⟨2365353883849708840103941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153805178466278453471921 2365353883849708840103941)
                ·
                  refine ⟨443503853221820407519489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365353883849708840103941 443503853221820407519489)
                  ·
                    rfl

theorem cell22_3886743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 4].length) (baseStart_3886743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886743 prefixEnd_3886743 := by exact prefixLift 3886743
  have htrace : WordTrace (prefixWord ++ tailWord_3886743) baseStart_3886743 baseEnd_3886743 := by
    simpa [prefixWord, tailWord_3886743, baseEnd_3886743] using wordTrace_append hprefix tailTrace_3886743
  have hstable : (prefixWord ++ tailWord_3886743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886743).length < 2 ^ (prefixWord ++ tailWord_3886743).sum := by decide
  have hdescent : baseEnd_3886743 < baseStart_3886743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886773 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3886773 : Nat := 118140960795 + 3886773 * 2 ^ 59
def prefixEnd_3886773 : Nat := 4983230072969 + 3 ^ 40 * 3886773 * 2
def baseEnd_3886773 : Nat := 1330521829278551144308375

theorem tailTrace_3886773 : CollatzResearch.WordTrace tailWord_3886773 prefixEnd_3886773 1330521829278551144308375 := by
  unfold tailWord_3886773
  simp only [CollatzResearch.WordTrace]
  refine ⟨141762257547892703825056973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94508171698595135883371315 141762257547892703825056973)
  ·
    refine ⟨53160846580459763934396365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141762257547892703825056973 53160846580459763934396365)
    ·
      refine ⟨19935317467672411475398637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53160846580459763934396365 19935317467672411475398637)
      ·
        refine ⟨7475744050377154303274489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19935317467672411475398637 7475744050377154303274489)
        ·
          refine ⟨5606808037782865727455867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7475744050377154303274489 5606808037782865727455867)
          ·
            refine ⟨8410212056674298591183801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606808037782865727455867 8410212056674298591183801)
            ·
              refine ⟨6307659042505723943387851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8410212056674298591183801 6307659042505723943387851)
              ·
                refine ⟨9461488563758585915081777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307659042505723943387851 9461488563758585915081777)
                ·
                  refine ⟨7096116422818939436311333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9461488563758585915081777 7096116422818939436311333)
                  ·
                    refine ⟨1330521829278551144308375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096116422818939436311333 1330521829278551144308375)
                    ·
                      rfl

theorem cell22_3886773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3886773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886773 prefixEnd_3886773 := by exact prefixLift 3886773
  have htrace : WordTrace (prefixWord ++ tailWord_3886773) baseStart_3886773 baseEnd_3886773 := by
    simpa [prefixWord, tailWord_3886773, baseEnd_3886773] using wordTrace_append hprefix tailTrace_3886773
  have hstable : (prefixWord ++ tailWord_3886773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886773).length < 2 ^ (prefixWord ++ tailWord_3886773).sum := by decide
  have hdescent : baseEnd_3886773 < baseStart_3886773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886790 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3886790 : Nat := 118140960795 + 3886790 * 2 ^ 59
def prefixEnd_3886790 : Nat := 4983230072969 + 3 ^ 40 * 3886790 * 2
def baseEnd_3886790 : Nat := 1330527648725968766633323

theorem tailTrace_3886790 : CollatzResearch.WordTrace tailWord_3886790 prefixEnd_3886790 1330527648725968766633323 := by
  unfold tailWord_3886790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430089924650972366513307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94508585059220743818950549 4430089924650972366513307)
  ·
    refine ⟨6645134886976458549769961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430089924650972366513307 6645134886976458549769961)
    ·
      refine ⟨4983851165232343912327471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6645134886976458549769961 4983851165232343912327471)
      ·
        refine ⟨7475776747848515868491207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983851165232343912327471 7475776747848515868491207)
        ·
          refine ⟨11213665121772773802736811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475776747848515868491207 11213665121772773802736811)
          ·
            refine ⟨16820497682659160704105217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11213665121772773802736811 16820497682659160704105217)
            ·
              refine ⟨12615373261994370528078913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16820497682659160704105217 12615373261994370528078913)
              ·
                refine ⟨9461529946495777896059185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12615373261994370528078913 9461529946495777896059185)
                ·
                  refine ⟨7096147459871833422044389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9461529946495777896059185 7096147459871833422044389)
                  ·
                    refine ⟨1330527648725968766633323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096147459871833422044389 1330527648725968766633323)
                    ·
                      rfl

theorem cell22_3886790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3886790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886790 prefixEnd_3886790 := by exact prefixLift 3886790
  have htrace : WordTrace (prefixWord ++ tailWord_3886790) baseStart_3886790 baseEnd_3886790 := by
    simpa [prefixWord, tailWord_3886790, baseEnd_3886790] using wordTrace_append hprefix tailTrace_3886790
  have hstable : (prefixWord ++ tailWord_3886790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886790).length < 2 ^ (prefixWord ++ tailWord_3886790).sum := by decide
  have hdescent : baseEnd_3886790 < baseStart_3886790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886844 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_3886844 : Nat := 118140960795 + 3886844 * 2 ^ 59
def prefixEnd_3886844 : Nat := 4983230072969 + 3 ^ 40 * 3886844 * 2
def baseEnd_3886844 : Nat := 443515378009843541927719

theorem tailTrace_3886844 : CollatzResearch.WordTrace tailWord_3886844 prefixEnd_3886844 443515378009843541927719 := by
  unfold tailWord_3886844
  simp only [CollatzResearch.WordTrace]
  refine ⟨70882423565317741475445793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94509898087090321967261057 70882423565317741475445793)
  ·
    refine ⟨53161817673988306106584345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70882423565317741475445793 53161817673988306106584345)
    ·
      refine ⟨39871363255491229579938259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53161817673988306106584345 39871363255491229579938259)
      ·
        refine ⟨59807044883236844369907389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39871363255491229579938259 59807044883236844369907389)
        ·
          refine ⟨22427641831213816638715271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59807044883236844369907389 22427641831213816638715271)
          ·
            refine ⟨33641462746820724958072907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22427641831213816638715271 33641462746820724958072907)
            ·
              refine ⟨50462194120231087437109361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33641462746820724958072907 50462194120231087437109361)
              ·
                refine ⟨37846645590173315577832021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50462194120231087437109361 37846645590173315577832021)
                ·
                  refine ⟨443515378009843541927719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37846645590173315577832021 443515378009843541927719)
                  ·
                    rfl

theorem cell22_3886844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_3886844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886844 prefixEnd_3886844 := by exact prefixLift 3886844
  have htrace : WordTrace (prefixWord ++ tailWord_3886844) baseStart_3886844 baseEnd_3886844 := by
    simpa [prefixWord, tailWord_3886844, baseEnd_3886844] using wordTrace_append hprefix tailTrace_3886844
  have hstable : (prefixWord ++ tailWord_3886844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886844).length < 2 ^ (prefixWord ++ tailWord_3886844).sum := by decide
  have hdescent : baseEnd_3886844 < baseStart_3886844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886859 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_3886859 : Nat := 118140960795 + 3886859 * 2 ^ 59
def prefixEnd_3886859 : Nat := 4983230072969 + 3 ^ 40 * 3886859 * 2
def baseEnd_3886859 : Nat := 1330551268836075586658111

theorem tailTrace_3886859 : CollatzResearch.WordTrace tailWord_3886859 prefixEnd_3886859 1330551268836075586658111 := by
  unfold tailWord_3886859
  simp only [CollatzResearch.WordTrace]
  refine ⟨141765394225581140512687631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94510262817054093675125087 141765394225581140512687631)
  ·
    refine ⟨212648091338371710769031447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141765394225581140512687631 212648091338371710769031447)
    ·
      refine ⟨318972137007557566153547171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212648091338371710769031447 318972137007557566153547171)
      ·
        refine ⟨478458205511336349230320757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318972137007557566153547171 478458205511336349230320757)
        ·
          refine ⟨44855456766687782740342571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 478458205511336349230320757 44855456766687782740342571)
          ·
            refine ⟨67283185150031674110513857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44855456766687782740342571 67283185150031674110513857)
            ·
              refine ⟨50462388862523755582885393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67283185150031674110513857 50462388862523755582885393)
              ·
                refine ⟨37846791646892816687164045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50462388862523755582885393 37846791646892816687164045)
                ·
                  refine ⟨14192546867584806257686517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37846791646892816687164045 14192546867584806257686517)
                  ·
                    refine ⟨1330551268836075586658111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14192546867584806257686517 1330551268836075586658111)
                    ·
                      rfl

theorem cell22_3886859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_3886859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886859 prefixEnd_3886859 := by exact prefixLift 3886859
  have htrace : WordTrace (prefixWord ++ tailWord_3886859) baseStart_3886859 baseEnd_3886859 := by
    simpa [prefixWord, tailWord_3886859, baseEnd_3886859] using wordTrace_append hprefix tailTrace_3886859
  have hstable : (prefixWord ++ tailWord_3886859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886859).length < 2 ^ (prefixWord ++ tailWord_3886859).sum := by decide
  have hdescent : baseEnd_3886859 < baseStart_3886859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886906 : List Nat := [3, 1, 1, 1, 5, 3, 8]
def baseStart_3886906 : Nat := 118140960795 + 3886906 * 2 ^ 59
def prefixEnd_3886906 : Nat := 4983230072969 + 3 ^ 40 * 3886906 * 2
def baseEnd_3886906 : Nat := 49280272514688264101221

theorem tailTrace_3886906 : CollatzResearch.WordTrace tailWord_3886906 prefixEnd_3886906 49280272514688264101221 := by
  unfold tailWord_3886906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35441777114102716884912143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94511405637607245026432381 35441777114102716884912143)
  ·
    refine ⟨53162665671154075327368215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35441777114102716884912143 53162665671154075327368215)
    ·
      refine ⟨79743998506731112991052323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53162665671154075327368215 79743998506731112991052323)
      ·
        refine ⟨119615997760096669486578485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79743998506731112991052323 119615997760096669486578485)
        ·
          refine ⟨11213999790009062764366733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119615997760096669486578485 11213999790009062764366733)
          ·
            refine ⟨4205249921253398536637525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11213999790009062764366733 4205249921253398536637525)
            ·
              refine ⟨49280272514688264101221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4205249921253398536637525 49280272514688264101221)
              ·
                rfl

theorem cell22_3886906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 8].length) (baseStart_3886906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886906 prefixEnd_3886906 := by exact prefixLift 3886906
  have htrace : WordTrace (prefixWord ++ tailWord_3886906) baseStart_3886906 baseEnd_3886906 := by
    simpa [prefixWord, tailWord_3886906, baseEnd_3886906] using wordTrace_append hprefix tailTrace_3886906
  have hstable : (prefixWord ++ tailWord_3886906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886906).length < 2 ^ (prefixWord ++ tailWord_3886906).sum := by decide
  have hdescent : baseEnd_3886906 < baseStart_3886906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
