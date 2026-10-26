import V185TrunkScan23Chunk0913

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5409355 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 3]
def baseStart_5409355 : Nat := 118140960795 + 5409355 * 2 ^ 59
def prefixEnd_5409355 : Nat := 4983230072969 + 3 ^ 40 * 5409355 * 2
def baseEnd_5409355 : Nat := 2777599145801788607385335

theorem tailTrace_5409355 : CollatzResearch.WordTrace tailWord_5409355 prefixEnd_5409355 2777599145801788607385335 := by
  unfold tailWord_5409355
  simp only [CollatzResearch.WordTrace]
  refine ⟨197295385317838154128109519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131530256878558769418739679 197295385317838154128109519)
  ·
    refine ⟨295943077976757231192164279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197295385317838154128109519 295943077976757231192164279)
    ·
      refine ⟨443914616965135846788246419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295943077976757231192164279 443914616965135846788246419)
      ·
        refine ⟨665871925447703770182369629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443914616965135846788246419 665871925447703770182369629)
        ·
          refine ⟨249701972042888913818388611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 665871925447703770182369629 249701972042888913818388611)
          ·
            refine ⟨374552958064333370727582917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249701972042888913818388611 374552958064333370727582917)
            ·
              refine ⟨70228679637062507011421797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374552958064333370727582917 70228679637062507011421797)
              ·
                refine ⟨13167877431949220064641587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70228679637062507011421797 13167877431949220064641587)
                ·
                  refine ⟨19751816147923830096962381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13167877431949220064641587 19751816147923830096962381)
                  ·
                    refine ⟨7406931055471436286360893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19751816147923830096962381 7406931055471436286360893)
                    ·
                      refine ⟨2777599145801788607385335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406931055471436286360893 2777599145801788607385335)
                      ·
                        rfl

theorem cell23_5409355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 3].length) (baseStart_5409355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409355 prefixEnd_5409355 := by exact prefixLift 5409355
  have htrace : WordTrace (prefixWord ++ tailWord_5409355) baseStart_5409355 baseEnd_5409355 := by
    simpa [prefixWord, tailWord_5409355, baseEnd_5409355] using wordTrace_append hprefix tailTrace_5409355
  have hstable : (prefixWord ++ tailWord_5409355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409355).length < 2 ^ (prefixWord ++ tailWord_5409355).sum := by decide
  have hdescent : baseEnd_5409355 < baseStart_5409355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409399 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 1, 3, 2]
def baseStart_5409399 : Nat := 118140960795 + 5409399 * 2 ^ 59
def prefixEnd_5409399 : Nat := 4983230072969 + 3 ^ 40 * 5409399 * 2
def baseEnd_5409399 : Nat := 2777621738950586435235133

theorem tailTrace_5409399 : CollatzResearch.WordTrace tailWord_5409399 prefixEnd_5409399 2777621738950586435235133 := by
  unfold tailWord_5409399
  simp only [CollatzResearch.WordTrace]
  refine ⟨197296990129678749642711251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131531326753119166428474167 197296990129678749642711251)
  ·
    refine ⟨295945485194518124464066877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197296990129678749642711251 295945485194518124464066877)
    ·
      refine ⟨110979556947944296674025079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295945485194518124464066877 110979556947944296674025079)
      ·
        refine ⟨166469335421916445011037619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110979556947944296674025079 166469335421916445011037619)
        ·
          refine ⟨249704003132874667516556429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166469335421916445011037619 249704003132874667516556429)
          ·
            refine ⟨93639001174828000318708661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249704003132874667516556429 93639001174828000318708661)
            ·
              refine ⟨8778656360140125029878937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93639001174828000318708661 8778656360140125029878937)
              ·
                refine ⟨6583992270105093772409203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8778656360140125029878937 6583992270105093772409203)
                ·
                  refine ⟨9875988405157640658613805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583992270105093772409203 9875988405157640658613805)
                  ·
                    refine ⟨3703495651934115246980177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9875988405157640658613805 3703495651934115246980177)
                    ·
                      refine ⟨2777621738950586435235133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703495651934115246980177 2777621738950586435235133)
                      ·
                        rfl

theorem cell23_5409399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_5409399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409399 prefixEnd_5409399 := by exact prefixLift 5409399
  have htrace : WordTrace (prefixWord ++ tailWord_5409399) baseStart_5409399 baseEnd_5409399 := by
    simpa [prefixWord, tailWord_5409399, baseEnd_5409399] using wordTrace_append hprefix tailTrace_5409399
  have hstable : (prefixWord ++ tailWord_5409399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409399).length < 2 ^ (prefixWord ++ tailWord_5409399).sum := by decide
  have hdescent : baseEnd_5409399 < baseStart_5409399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409410 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5409410 : Nat := 118140960795 + 5409410 * 2 ^ 59
def prefixEnd_5409410 : Nat := 4983230072969 + 3 ^ 40 * 5409410 * 2
def baseEnd_5409410 : Nat := 2777627387237785892197583

theorem tailTrace_5409410 : CollatzResearch.WordTrace tailWord_5409410 prefixEnd_5409410 2777627387237785892197583 := by
  unfold tailWord_5409410
  simp only [CollatzResearch.WordTrace]
  refine ⟨49324347833159724630340421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131531594221759265680907789 49324347833159724630340421)
  ·
    refine ⟨9248315218717448368188829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49324347833159724630340421 9248315218717448368188829)
    ·
      refine ⟨3468118207019043138070811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9248315218717448368188829 3468118207019043138070811)
      ·
        refine ⟨5202177310528564707106217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468118207019043138070811 5202177310528564707106217)
        ·
          refine ⟨3901632982896423530329663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5202177310528564707106217 3901632982896423530329663)
          ·
            refine ⟨5852449474344635295494495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901632982896423530329663 5852449474344635295494495)
            ·
              refine ⟨8778674211516952943241743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852449474344635295494495 8778674211516952943241743)
              ·
                refine ⟨13168011317275429414862615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8778674211516952943241743 13168011317275429414862615)
                ·
                  refine ⟨19752016975913144122293923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13168011317275429414862615 19752016975913144122293923)
                  ·
                    refine ⟨29628025463869716183440885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19752016975913144122293923 29628025463869716183440885)
                    ·
                      refine ⟨2777627387237785892197583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29628025463869716183440885 2777627387237785892197583)
                      ·
                        rfl

theorem cell23_5409410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5409410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409410 prefixEnd_5409410 := by exact prefixLift 5409410
  have htrace : WordTrace (prefixWord ++ tailWord_5409410) baseStart_5409410 baseEnd_5409410 := by
    simpa [prefixWord, tailWord_5409410, baseEnd_5409410] using wordTrace_append hprefix tailTrace_5409410
  have hstable : (prefixWord ++ tailWord_5409410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409410).length < 2 ^ (prefixWord ++ tailWord_5409410).sum := by decide
  have hdescent : baseEnd_5409410 < baseStart_5409410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409415 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_5409415 : Nat := 118140960795 + 5409415 * 2 ^ 59
def prefixEnd_5409415 : Nat := 4983230072969 + 3 ^ 40 * 5409415 * 2
def baseEnd_5409415 : Nat := 2777629954641058372635059

theorem tailTrace_5409415 : CollatzResearch.WordTrace tailWord_5409415 prefixEnd_5409415 2777629954641058372635059 := by
  unfold tailWord_5409415
  simp only [CollatzResearch.WordTrace]
  refine ⟨197297573697620784375293699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131531715798413856250195799 197297573697620784375293699)
  ·
    refine ⟨295946360546431176562940549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197297573697620784375293699 295946360546431176562940549)
    ·
      refine ⟨55489942602455845605551353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295946360546431176562940549 55489942602455845605551353)
      ·
        refine ⟨41617456951841884204163515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55489942602455845605551353 41617456951841884204163515)
        ·
          refine ⟨62426185427762826306245273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41617456951841884204163515 62426185427762826306245273)
          ·
            refine ⟨46819639070822119729683955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62426185427762826306245273 46819639070822119729683955)
            ·
              refine ⟨70229458606233179594525933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46819639070822119729683955 70229458606233179594525933)
              ·
                refine ⟨26336046977337442347947225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70229458606233179594525933 26336046977337442347947225)
                ·
                  refine ⟨19752035233003081760960419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26336046977337442347947225 19752035233003081760960419)
                  ·
                    refine ⟨29628052849504622641440629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19752035233003081760960419 29628052849504622641440629)
                    ·
                      refine ⟨2777629954641058372635059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29628052849504622641440629 2777629954641058372635059)
                      ·
                        rfl

theorem cell23_5409415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_5409415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409415 prefixEnd_5409415 := by exact prefixLift 5409415
  have htrace : WordTrace (prefixWord ++ tailWord_5409415) baseStart_5409415 baseEnd_5409415 := by
    simpa [prefixWord, tailWord_5409415, baseEnd_5409415] using wordTrace_append hprefix tailTrace_5409415
  have hstable : (prefixWord ++ tailWord_5409415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409415).length < 2 ^ (prefixWord ++ tailWord_5409415).sum := by decide
  have hdescent : baseEnd_5409415 < baseStart_5409415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409469 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 5]
def baseStart_5409469 : Nat := 118140960795 + 5409469 * 2 ^ 59
def prefixEnd_5409469 : Nat := 4983230072969 + 3 ^ 40 * 5409469 * 2
def baseEnd_5409469 : Nat := 308628631399600129039979

theorem tailTrace_5409469 : CollatzResearch.WordTrace tailWord_5409469 prefixEnd_5409469 308628631399600129039979 := by
  unfold tailWord_5409469
  simp only [CollatzResearch.WordTrace]
  refine ⟨197299543239425151597759461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131533028826283434398506307 197299543239425151597759461)
  ·
    refine ⟨36993664357392215924579899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197299543239425151597759461 36993664357392215924579899)
    ·
      refine ⟨55490496536088323886869849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36993664357392215924579899 55490496536088323886869849)
      ·
        refine ⟨41617872402066242915152387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55490496536088323886869849 41617872402066242915152387)
        ·
          refine ⟨62426808603099364372728581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41617872402066242915152387 62426808603099364372728581)
          ·
            refine ⟨11705026613081130819886609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62426808603099364372728581 11705026613081130819886609)
            ·
              refine ⟨8778769959810848114914957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11705026613081130819886609 8778769959810848114914957)
              ·
                refine ⟨3292038734929068043093109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8778769959810848114914957 3292038734929068043093109)
                ·
                  refine ⟨308628631399600129039979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3292038734929068043093109 308628631399600129039979)
                  ·
                    rfl

theorem cell23_5409469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_5409469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409469 prefixEnd_5409469 := by exact prefixLift 5409469
  have htrace : WordTrace (prefixWord ++ tailWord_5409469) baseStart_5409469 baseEnd_5409469 := by
    simpa [prefixWord, tailWord_5409469, baseEnd_5409469] using wordTrace_append hprefix tailTrace_5409469
  have hstable : (prefixWord ++ tailWord_5409469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409469).length < 2 ^ (prefixWord ++ tailWord_5409469).sum := by decide
  have hdescent : baseEnd_5409469 < baseStart_5409469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409515 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4]
def baseStart_5409515 : Nat := 118140960795 + 5409515 * 2 ^ 59
def prefixEnd_5409515 : Nat := 4983230072969 + 3 ^ 40 * 5409515 * 2
def baseEnd_5409515 : Nat := 2777681302706507981384599

theorem tailTrace_5409515 : CollatzResearch.WordTrace tailWord_5409515 prefixEnd_5409515 2777681302706507981384599 := by
  unfold tailWord_5409515
  simp only [CollatzResearch.WordTrace]
  refine ⟨197301220997258501453933999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131534147331505667635955999 197301220997258501453933999)
  ·
    refine ⟨295951831495887752180900999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197301220997258501453933999 295951831495887752180900999)
    ·
      refine ⟨443927747243831628271351499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295951831495887752180900999 443927747243831628271351499)
      ·
        refine ⟨665891620865747442407027249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443927747243831628271351499 665891620865747442407027249)
        ·
          refine ⟨499418715649310581805270437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665891620865747442407027249 499418715649310581805270437)
          ·
            refine ⟨93641009184245734088488207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 499418715649310581805270437 93641009184245734088488207)
            ·
              refine ⟨140461513776368601132732311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93641009184245734088488207 140461513776368601132732311)
              ·
                refine ⟨210692270664552901699098467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140461513776368601132732311 210692270664552901699098467)
                ·
                  refine ⟨316038405996829352548647701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210692270664552901699098467 316038405996829352548647701)
                  ·
                    refine ⟨14814300281101375900717861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 316038405996829352548647701 14814300281101375900717861)
                    ·
                      refine ⟨2777681302706507981384599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14814300281101375900717861 2777681302706507981384599)
                      ·
                        rfl

theorem cell23_5409515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_5409515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409515 prefixEnd_5409515 := by exact prefixLift 5409515
  have htrace : WordTrace (prefixWord ++ tailWord_5409515) baseStart_5409515 baseEnd_5409515 := by
    simpa [prefixWord, tailWord_5409515, baseEnd_5409515] using wordTrace_append hprefix tailTrace_5409515
  have hstable : (prefixWord ++ tailWord_5409515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409515).length < 2 ^ (prefixWord ++ tailWord_5409515).sum := by decide
  have hdescent : baseEnd_5409515 < baseStart_5409515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409545 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_5409545 : Nat := 118140960795 + 5409545 * 2 ^ 59
def prefixEnd_5409545 : Nat := 4983230072969 + 3 ^ 40 * 5409545 * 2
def baseEnd_5409545 : Nat := 2777696707126142864009461

theorem tailTrace_5409545 : CollatzResearch.WordTrace tailWord_5409545 prefixEnd_5409545 2777696707126142864009461 := by
  unfold tailWord_5409545
  simp only [CollatzResearch.WordTrace]
  refine ⟨197302315187149816577526089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131534876791433211051684059 197302315187149816577526089)
  ·
    refine ⟨147976736390362362433144567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197302315187149816577526089 147976736390362362433144567)
    ·
      refine ⟨221965104585543543649716851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147976736390362362433144567 221965104585543543649716851)
      ·
        refine ⟨332947656878315315474575277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221965104585543543649716851 332947656878315315474575277)
        ·
          refine ⟨124855371329368243302965729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332947656878315315474575277 124855371329368243302965729)
          ·
            refine ⟨93641528497026182477224297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124855371329368243302965729 93641528497026182477224297)
            ·
              refine ⟨70231146372769636857918223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93641528497026182477224297 70231146372769636857918223)
              ·
                refine ⟨105346719559154455286877335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70231146372769636857918223 105346719559154455286877335)
                ·
                  refine ⟨158020079338731682930316003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105346719559154455286877335 158020079338731682930316003)
                  ·
                    refine ⟨237030119008097524395474005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158020079338731682930316003 237030119008097524395474005)
                    ·
                      refine ⟨2777696707126142864009461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 237030119008097524395474005 2777696707126142864009461)
                      ·
                        rfl

theorem cell23_5409545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_5409545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409545 prefixEnd_5409545 := by exact prefixLift 5409545
  have htrace : WordTrace (prefixWord ++ tailWord_5409545) baseStart_5409545 baseEnd_5409545 := by
    simpa [prefixWord, tailWord_5409545, baseEnd_5409545] using wordTrace_append hprefix tailTrace_5409545
  have hstable : (prefixWord ++ tailWord_5409545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409545).length < 2 ^ (prefixWord ++ tailWord_5409545).sum := by decide
  have hdescent : baseEnd_5409545 < baseStart_5409545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409559 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 6]
def baseStart_5409559 : Nat := 118140960795 + 5409559 * 2 ^ 59
def prefixEnd_5409559 : Nat := 4983230072969 + 3 ^ 40 * 5409559 * 2
def baseEnd_5409559 : Nat := 308633766206145089914933

theorem tailTrace_5409559 : CollatzResearch.WordTrace tailWord_5409559 prefixEnd_5409559 308633766206145089914933 := by
  unfold tailWord_5409559
  simp only [CollatzResearch.WordTrace]
  refine ⟨197302825809099096968535731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131535217206066064645690487 197302825809099096968535731)
  ·
    refine ⟨295954238713648645452803597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197302825809099096968535731 295954238713648645452803597)
    ·
      refine ⟨110982839517618242044801349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295954238713648645452803597 110982839517618242044801349)
      ·
        refine ⟨20809282409553420383400253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110982839517618242044801349 20809282409553420383400253)
        ·
          refine ⟨7803480903582532643775095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20809282409553420383400253 7803480903582532643775095)
          ·
            refine ⟨11705221355373798965662643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7803480903582532643775095 11705221355373798965662643)
            ·
              refine ⟨17557832033060698448493965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705221355373798965662643 17557832033060698448493965)
              ·
                refine ⟨6584187012397761918185237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17557832033060698448493965 6584187012397761918185237)
                ·
                  refine ⟨308633766206145089914933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6584187012397761918185237 308633766206145089914933)
                  ·
                    rfl

theorem cell23_5409559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 6].length) (baseStart_5409559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409559 prefixEnd_5409559 := by exact prefixLift 5409559
  have htrace : WordTrace (prefixWord ++ tailWord_5409559) baseStart_5409559 baseEnd_5409559 := by
    simpa [prefixWord, tailWord_5409559, baseEnd_5409559] using wordTrace_append hprefix tailTrace_5409559
  have hstable : (prefixWord ++ tailWord_5409559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409559).length < 2 ^ (prefixWord ++ tailWord_5409559).sum := by decide
  have hdescent : baseEnd_5409559 < baseStart_5409559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409569 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_5409569 : Nat := 118140960795 + 5409569 * 2 ^ 59
def prefixEnd_5409569 : Nat := 4983230072969 + 3 ^ 40 * 5409569 * 2
def baseEnd_5409569 : Nat := 2777709030661850770109351

theorem tailTrace_5409569 : CollatzResearch.WordTrace tailWord_5409569 prefixEnd_5409569 2777709030661850770109351 := by
  unfold tailWord_5409569
  simp only [CollatzResearch.WordTrace]
  refine ⟨197303190539062868676399761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131535460359375245784266507 197303190539062868676399761)
  ·
    refine ⟨147977392904297151507299821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197303190539062868676399761 147977392904297151507299821)
    ·
      refine ⟨55491522339111431815237433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147977392904297151507299821 55491522339111431815237433)
      ·
        refine ⟨41618641754333573861428075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55491522339111431815237433 41618641754333573861428075)
        ·
          refine ⟨62427962631500360792142113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41618641754333573861428075 62427962631500360792142113)
          ·
            refine ⟨46820971973625270594106585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62427962631500360792142113 46820971973625270594106585)
            ·
              refine ⟨35115728980218952945579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46820971973625270594106585 35115728980218952945579939)
              ·
                refine ⟨52673593470328429418369909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35115728980218952945579939 52673593470328429418369909)
                ·
                  refine ⟨4938149387843290257972179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52673593470328429418369909 4938149387843290257972179)
                  ·
                    refine ⟨7407224081764935386958269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4938149387843290257972179 7407224081764935386958269)
                    ·
                      refine ⟨2777709030661850770109351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7407224081764935386958269 2777709030661850770109351)
                      ·
                        rfl

theorem cell23_5409569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_5409569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409569 prefixEnd_5409569 := by exact prefixLift 5409569
  have htrace : WordTrace (prefixWord ++ tailWord_5409569) baseStart_5409569 baseEnd_5409569 := by
    simpa [prefixWord, tailWord_5409569, baseEnd_5409569] using wordTrace_append hprefix tailTrace_5409569
  have hstable : (prefixWord ++ tailWord_5409569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409569).length < 2 ^ (prefixWord ++ tailWord_5409569).sum := by decide
  have hdescent : baseEnd_5409569 < baseStart_5409569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409579 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 2, 3, 2]
def baseStart_5409579 : Nat := 118140960795 + 5409579 * 2 ^ 59
def prefixEnd_5409579 : Nat := 4983230072969 + 3 ^ 40 * 5409579 * 2
def baseEnd_5409579 : Nat := 2777714165468395730984305

theorem tailTrace_5409579 : CollatzResearch.WordTrace tailWord_5409579 prefixEnd_5409579 2777714165468395730984305 := by
  unfold tailWord_5409579
  simp only [CollatzResearch.WordTrace]
  refine ⟨197303555269026640384263791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131535703512684426922842527 197303555269026640384263791)
  ·
    refine ⟨295955332903539960576395687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197303555269026640384263791 295955332903539960576395687)
    ·
      refine ⟨443932999355309940864593531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295955332903539960576395687 443932999355309940864593531)
      ·
        refine ⟨665899499032964911296890297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443932999355309940864593531 665899499032964911296890297)
        ·
          refine ⟨499424624274723683472667723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665899499032964911296890297 499424624274723683472667723)
          ·
            refine ⟨749136936412085525209001585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499424624274723683472667723 749136936412085525209001585)
            ·
              refine ⟨561852702309064143906751189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749136936412085525209001585 561852702309064143906751189)
              ·
                refine ⟨13168422710368690872814481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 561852702309064143906751189 13168422710368690872814481)
                ·
                  refine ⟨9876317032776518154610861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13168422710368690872814481 9876317032776518154610861)
                  ·
                    refine ⟨3703618887291194307979073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9876317032776518154610861 3703618887291194307979073)
                    ·
                      refine ⟨2777714165468395730984305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703618887291194307979073 2777714165468395730984305)
                      ·
                        rfl

theorem cell23_5409579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3, 2].length) (baseStart_5409579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409579 prefixEnd_5409579 := by exact prefixLift 5409579
  have htrace : WordTrace (prefixWord ++ tailWord_5409579) baseStart_5409579 baseEnd_5409579 := by
    simpa [prefixWord, tailWord_5409579, baseEnd_5409579] using wordTrace_append hprefix tailTrace_5409579
  have hstable : (prefixWord ++ tailWord_5409579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409579).length < 2 ^ (prefixWord ++ tailWord_5409579).sum := by decide
  have hdescent : baseEnd_5409579 < baseStart_5409579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409597 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_5409597 : Nat := 118140960795 + 5409597 * 2 ^ 59
def prefixEnd_5409597 : Nat := 4983230072969 + 3 ^ 40 * 5409597 * 2
def baseEnd_5409597 : Nat := 925907802706725553519741

theorem tailTrace_5409597 : CollatzResearch.WordTrace tailWord_5409597 prefixEnd_5409597 925907802706725553519741 := by
  unfold tailWord_5409597
  simp only [CollatzResearch.WordTrace]
  refine ⟨197304211782961429458419045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131536141188640952972279363 197304211782961429458419045)
  ·
    refine ⟨36994539709305268023453571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197304211782961429458419045 36994539709305268023453571)
    ·
      refine ⟨55491809563957902035180357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36994539709305268023453571 55491809563957902035180357)
      ·
        refine ⟨10404714293242106631596317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55491809563957902035180357 10404714293242106631596317)
        ·
          refine ⟨3901767859965789986848619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10404714293242106631596317 3901767859965789986848619)
          ·
            refine ⟨5852651789948684980272929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901767859965789986848619 5852651789948684980272929)
            ·
              refine ⟨4389488842461513735204697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5852651789948684980272929 4389488842461513735204697)
              ·
                refine ⟨3292116631846135301403523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4389488842461513735204697 3292116631846135301403523)
                ·
                  refine ⟨4938174947769202952105285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292116631846135301403523 4938174947769202952105285)
                  ·
                    refine ⟨925907802706725553519741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4938174947769202952105285 925907802706725553519741)
                    ·
                      rfl

theorem cell23_5409597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_5409597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409597 prefixEnd_5409597 := by exact prefixLift 5409597
  have htrace : WordTrace (prefixWord ++ tailWord_5409597) baseStart_5409597 baseEnd_5409597 := by
    simpa [prefixWord, tailWord_5409597, baseEnd_5409597] using wordTrace_append hprefix tailTrace_5409597
  have hstable : (prefixWord ++ tailWord_5409597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409597).length < 2 ^ (prefixWord ++ tailWord_5409597).sum := by decide
  have hdescent : baseEnd_5409597 < baseStart_5409597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409626 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2]
def baseStart_5409626 : Nat := 118140960795 + 5409626 * 2 ^ 59
def prefixEnd_5409626 : Nat := 4983230072969 + 3 ^ 40 * 5409626 * 2
def baseEnd_5409626 : Nat := 2777738299059157047096589

theorem tailTrace_5409626 : CollatzResearch.WordTrace tailWord_5409626 prefixEnd_5409626 2777738299059157047096589 := by
  unfold tailWord_5409626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49326317374964091852806183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131536846333237578274149821 49326317374964091852806183)
  ·
    refine ⟨73989476062446137779209275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49326317374964091852806183 73989476062446137779209275)
    ·
      refine ⟨110984214093669206668813913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73989476062446137779209275 110984214093669206668813913)
      ·
        refine ⟨83238160570251905001610435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110984214093669206668813913 83238160570251905001610435)
        ·
          refine ⟨124857240855377857502415653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83238160570251905001610435 124857240855377857502415653)
          ·
            refine ⟨23410732660383348281702935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124857240855377857502415653 23410732660383348281702935)
            ·
              refine ⟨35116098990575022422554403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23410732660383348281702935 35116098990575022422554403)
              ·
                refine ⟨52674148485862533633831605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35116098990575022422554403 52674148485862533633831605)
                ·
                  refine ⟨4938201420549612528171713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52674148485862533633831605 4938201420549612528171713)
                  ·
                    refine ⟨3703651065412209396128785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4938201420549612528171713 3703651065412209396128785)
                    ·
                      refine ⟨2777738299059157047096589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703651065412209396128785 2777738299059157047096589)
                      ·
                        rfl

theorem cell23_5409626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_5409626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409626 prefixEnd_5409626 := by exact prefixLift 5409626
  have htrace : WordTrace (prefixWord ++ tailWord_5409626) baseStart_5409626 baseEnd_5409626 := by
    simpa [prefixWord, tailWord_5409626, baseEnd_5409626] using wordTrace_append hprefix tailTrace_5409626
  have hstable : (prefixWord ++ tailWord_5409626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409626).length < 2 ^ (prefixWord ++ tailWord_5409626).sum := by decide
  have hdescent : baseEnd_5409626 < baseStart_5409626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409639 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5409639 : Nat := 118140960795 + 5409639 * 2 ^ 59
def prefixEnd_5409639 : Nat := 4983230072969 + 3 ^ 40 * 5409639 * 2
def baseEnd_5409639 : Nat := 2777744974307665496234029

theorem tailTrace_5409639 : CollatzResearch.WordTrace tailWord_5409639 prefixEnd_5409639 2777744974307665496234029 := by
  unfold tailWord_5409639
  simp only [CollatzResearch.WordTrace]
  refine ⟨197305743648809270631447971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131537162432539513754298647 197305743648809270631447971)
  ·
    refine ⟨295958615473213905947171957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197305743648809270631447971 295958615473213905947171957)
    ·
      refine ⟨27746120200613803682547371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295958615473213905947171957 27746120200613803682547371)
      ·
        refine ⟨41619180300920705523821057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27746120200613803682547371 41619180300920705523821057)
        ·
          refine ⟨31214385225690529142865793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41619180300920705523821057 31214385225690529142865793)
          ·
            refine ⟨23410788919267896857149345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31214385225690529142865793 23410788919267896857149345)
            ·
              refine ⟨17558091689450922642862009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23410788919267896857149345 17558091689450922642862009)
              ·
                refine ⟨13168568767088191982146507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17558091689450922642862009 13168568767088191982146507)
                ·
                  refine ⟨19752853150632287973219761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13168568767088191982146507 19752853150632287973219761)
                  ·
                    refine ⟨14814639862974215979914821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19752853150632287973219761 14814639862974215979914821)
                    ·
                      refine ⟨2777744974307665496234029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14814639862974215979914821 2777744974307665496234029)
                      ·
                        rfl

theorem cell23_5409639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5409639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409639 prefixEnd_5409639 := by exact prefixLift 5409639
  have htrace : WordTrace (prefixWord ++ tailWord_5409639) baseStart_5409639 baseEnd_5409639 := by
    simpa [prefixWord, tailWord_5409639, baseEnd_5409639] using wordTrace_append hprefix tailTrace_5409639
  have hstable : (prefixWord ++ tailWord_5409639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409639).length < 2 ^ (prefixWord ++ tailWord_5409639).sum := by decide
  have hdescent : baseEnd_5409639 < baseStart_5409639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409643 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 1, 2, 2]
def baseStart_5409643 : Nat := 118140960795 + 5409643 * 2 ^ 59
def prefixEnd_5409643 : Nat := 4983230072969 + 3 ^ 40 * 5409643 * 2
def baseEnd_5409643 : Nat := 2777747028230283480584011

theorem tailTrace_5409643 : CollatzResearch.WordTrace tailWord_5409643 prefixEnd_5409643 2777747028230283480584011 := by
  unfold tailWord_5409643
  simp only [CollatzResearch.WordTrace]
  refine ⟨197305889540794779314593583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131537259693863186209729055 197305889540794779314593583)
  ·
    refine ⟨295958834311192168971890375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197305889540794779314593583 295958834311192168971890375)
    ·
      refine ⟨443938251466788253457835563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295958834311192168971890375 443938251466788253457835563)
      ·
        refine ⟨665907377200182380186753345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443938251466788253457835563 665907377200182380186753345)
        ·
          refine ⟨499430532900136785140065009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665907377200182380186753345 499430532900136785140065009)
          ·
            refine ⟨374572899675102588855048757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499430532900136785140065009 374572899675102588855048757)
            ·
              refine ⟨35116209344540867705160821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 374572899675102588855048757 35116209344540867705160821)
              ·
                refine ⟨3292144626050706347358827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35116209344540867705160821 3292144626050706347358827)
                ·
                  refine ⟨4938216939076059521038241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292144626050706347358827 4938216939076059521038241)
                  ·
                    refine ⟨3703662704307044640778681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4938216939076059521038241 3703662704307044640778681)
                    ·
                      refine ⟨2777747028230283480584011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703662704307044640778681 2777747028230283480584011)
                      ·
                        rfl

theorem cell23_5409643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 2, 2].length) (baseStart_5409643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409643 prefixEnd_5409643 := by exact prefixLift 5409643
  have htrace : WordTrace (prefixWord ++ tailWord_5409643) baseStart_5409643 baseEnd_5409643 := by
    simpa [prefixWord, tailWord_5409643, baseEnd_5409643] using wordTrace_append hprefix tailTrace_5409643
  have hstable : (prefixWord ++ tailWord_5409643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409643).length < 2 ^ (prefixWord ++ tailWord_5409643).sum := by decide
  have hdescent : baseEnd_5409643 < baseStart_5409643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409653 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5409653 : Nat := 118140960795 + 5409653 * 2 ^ 59
def prefixEnd_5409653 : Nat := 4983230072969 + 3 ^ 40 * 5409653 * 2
def baseEnd_5409653 : Nat := 925917387678942813819655

theorem tailTrace_5409653 : CollatzResearch.WordTrace tailWord_5409653 prefixEnd_5409653 925917387678942813819655 := by
  unfold tailWord_5409653
  simp only [CollatzResearch.WordTrace]
  refine ⟨197306254270758551022457613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131537502847172367348305075 197306254270758551022457613)
  ·
    refine ⟨73989845351534456633421605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197306254270758551022457613 73989845351534456633421605)
    ·
      refine ⟨13873096003412710618766551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73989845351534456633421605 13873096003412710618766551)
      ·
        refine ⟨20809644005119065928149827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13873096003412710618766551 20809644005119065928149827)
        ·
          refine ⟨31214466007678598892224741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20809644005119065928149827 31214466007678598892224741)
          ·
            refine ⟨5852712376439737292292139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31214466007678598892224741 5852712376439737292292139)
            ·
              refine ⟨8779068564659605938438209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852712376439737292292139 8779068564659605938438209)
              ·
                refine ⟨6584301423494704453828657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8779068564659605938438209 6584301423494704453828657)
                ·
                  refine ⟨4938226067621028340371493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6584301423494704453828657 4938226067621028340371493)
                  ·
                    refine ⟨925917387678942813819655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4938226067621028340371493 925917387678942813819655)
                    ·
                      rfl

theorem cell23_5409653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5409653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409653 prefixEnd_5409653 := by exact prefixLift 5409653
  have htrace : WordTrace (prefixWord ++ tailWord_5409653) baseStart_5409653 baseEnd_5409653 := by
    simpa [prefixWord, tailWord_5409653, baseEnd_5409653] using wordTrace_append hprefix tailTrace_5409653
  have hstable : (prefixWord ++ tailWord_5409653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409653).length < 2 ^ (prefixWord ++ tailWord_5409653).sum := by decide
  have hdescent : baseEnd_5409653 < baseStart_5409653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409676 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_5409676 : Nat := 118140960795 + 5409676 * 2 ^ 59
def prefixEnd_5409676 : Nat := 4983230072969 + 3 ^ 40 * 5409676 * 2
def baseEnd_5409676 : Nat := 2777763973091881851471359

theorem tailTrace_5409676 : CollatzResearch.WordTrace tailWord_5409676 prefixEnd_5409676 2777763973091881851471359 := by
  unfold tailWord_5409676
  simp only [CollatzResearch.WordTrace]
  refine ⟨98653546574837612975272441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131538062099783483967029921 98653546574837612975272441)
  ·
    refine ⟨73990159931128209731454331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98653546574837612975272441 73990159931128209731454331)
    ·
      refine ⟨110985239896692314597181497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73990159931128209731454331 110985239896692314597181497)
      ·
        refine ⟨83238929922519235947886123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110985239896692314597181497 83238929922519235947886123)
        ·
          refine ⟨124858394883778853921829185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83238929922519235947886123 124858394883778853921829185)
          ·
            refine ⟨93643796162834140441371889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124858394883778853921829185 93643796162834140441371889)
            ·
              refine ⟨70232847122125605331028917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93643796162834140441371889 70232847122125605331028917)
              ·
                refine ⟨6584329417699275499783961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70232847122125605331028917 6584329417699275499783961)
                ·
                  refine ⟨4938247063274456624837971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6584329417699275499783961 4938247063274456624837971)
                  ·
                    refine ⟨7407370594911684937256957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4938247063274456624837971 7407370594911684937256957)
                    ·
                      refine ⟨2777763973091881851471359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7407370594911684937256957 2777763973091881851471359)
                      ·
                        rfl

theorem cell23_5409676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_5409676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409676 prefixEnd_5409676 := by exact prefixLift 5409676
  have htrace : WordTrace (prefixWord ++ tailWord_5409676) baseStart_5409676 baseEnd_5409676 := by
    simpa [prefixWord, tailWord_5409676, baseEnd_5409676] using wordTrace_append hprefix tailTrace_5409676
  have hstable : (prefixWord ++ tailWord_5409676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409676).length < 2 ^ (prefixWord ++ tailWord_5409676).sum := by decide
  have hdescent : baseEnd_5409676 < baseStart_5409676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409750 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5409750 : Nat := 118140960795 + 5409750 * 2 ^ 59
def prefixEnd_5409750 : Nat := 4983230072969 + 3 ^ 40 * 5409750 * 2
def baseEnd_5409750 : Nat := 2777801970660314561946019

theorem tailTrace_5409750 : CollatzResearch.WordTrace tailWord_5409750 prefixEnd_5409750 2777801970660314561946019 := by
  unfold tailWord_5409750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12331862009462946036796169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131539861434271424392492469 12331862009462946036796169)
  ·
    refine ⟨9248896507097209527597127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12331862009462946036796169 9248896507097209527597127)
    ·
      refine ⟨13873344760645814291395691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9248896507097209527597127 13873344760645814291395691)
      ·
        refine ⟨20810017140968721437093537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13873344760645814291395691 20810017140968721437093537)
        ·
          refine ⟨15607512855726541077820153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20810017140968721437093537 15607512855726541077820153)
          ·
            refine ⟨11705634641794905808365115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15607512855726541077820153 11705634641794905808365115)
            ·
              refine ⟨17558451962692358712547673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705634641794905808365115 17558451962692358712547673)
              ·
                refine ⟨13168838972019269034410755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17558451962692358712547673 13168838972019269034410755)
                ·
                  refine ⟨19753258458028903551616133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13168838972019269034410755 19753258458028903551616133)
                  ·
                    refine ⟨3703735960880419415928025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19753258458028903551616133 3703735960880419415928025)
                    ·
                      refine ⟨2777801970660314561946019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703735960880419415928025 2777801970660314561946019)
                      ·
                        rfl

theorem cell23_5409750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5409750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409750 prefixEnd_5409750 := by exact prefixLift 5409750
  have htrace : WordTrace (prefixWord ++ tailWord_5409750) baseStart_5409750 baseEnd_5409750 := by
    simpa [prefixWord, tailWord_5409750, baseEnd_5409750] using wordTrace_append hprefix tailTrace_5409750
  have hstable : (prefixWord ++ tailWord_5409750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409750).length < 2 ^ (prefixWord ++ tailWord_5409750).sum := by decide
  have hdescent : baseEnd_5409750 < baseStart_5409750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409789 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_5409789 : Nat := 118140960795 + 5409789 * 2 ^ 59
def prefixEnd_5409789 : Nat := 4983230072969 + 3 ^ 40 * 5409789 * 2
def baseEnd_5409789 : Nat := 2777821996405839909358339

theorem tailTrace_5409789 : CollatzResearch.WordTrace tailWord_5409789 prefixEnd_5409789 2777821996405839909358339 := by
  unfold tailWord_5409789
  simp only [CollatzResearch.WordTrace]
  refine ⟨197311214598265846249408421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131540809732177230832938947 197311214598265846249408421)
  ·
    refine ⟨36995852737174846171764079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197311214598265846249408421 36995852737174846171764079)
    ·
      refine ⟨55493779105762269257646119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36995852737174846171764079 55493779105762269257646119)
      ·
        refine ⟨83240668658643403886469179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55493779105762269257646119 83240668658643403886469179)
        ·
          refine ⟨124861002987965105829703769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83240668658643403886469179 124861002987965105829703769)
          ·
            refine ⟨93645752240973829372277827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124861002987965105829703769 93645752240973829372277827)
            ·
              refine ⟨140468628361460744058416741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93645752240973829372277827 140468628361460744058416741)
              ·
                refine ⟨26337867817773889510953139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140468628361460744058416741 26337867817773889510953139)
                ·
                  refine ⟨39506801726660834266429709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26337867817773889510953139 39506801726660834266429709)
                  ·
                    refine ⟨14815050647497812849911141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39506801726660834266429709 14815050647497812849911141)
                    ·
                      refine ⟨2777821996405839909358339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14815050647497812849911141 2777821996405839909358339)
                      ·
                        rfl

theorem cell23_5409789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_5409789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409789 prefixEnd_5409789 := by exact prefixLift 5409789
  have htrace : WordTrace (prefixWord ++ tailWord_5409789) baseStart_5409789 baseEnd_5409789 := by
    simpa [prefixWord, tailWord_5409789, baseEnd_5409789] using wordTrace_append hprefix tailTrace_5409789
  have hstable : (prefixWord ++ tailWord_5409789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409789).length < 2 ^ (prefixWord ++ tailWord_5409789).sum := by decide
  have hdescent : baseEnd_5409789 < baseStart_5409789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409806 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5409806 : Nat := 118140960795 + 5409806 * 2 ^ 59
def prefixEnd_5409806 : Nat := 4983230072969 + 3 ^ 40 * 5409806 * 2
def baseEnd_5409806 : Nat := 2777830725576966342845761

theorem tailTrace_5409806 : CollatzResearch.WordTrace tailWord_5409806 prefixEnd_5409806 2777830725576966342845761 := by
  unfold tailWord_5409806
  simp only [CollatzResearch.WordTrace]
  refine ⟨24663979329900532269097159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131541223092802838768518181 24663979329900532269097159)
  ·
    refine ⟨36995968994850798403645739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24663979329900532269097159 36995968994850798403645739)
    ·
      refine ⟨55493953492276197605468609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36995968994850798403645739 55493953492276197605468609)
      ·
        refine ⟨41620465119207148204101457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55493953492276197605468609 41620465119207148204101457)
        ·
          refine ⟨31215348839405361153076093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41620465119207148204101457 31215348839405361153076093)
          ·
            refine ⟨11705755814777010432403535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31215348839405361153076093 11705755814777010432403535)
            ·
              refine ⟨17558633722165515648605303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705755814777010432403535 17558633722165515648605303)
              ·
                refine ⟨26337950583248273472907955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17558633722165515648605303 26337950583248273472907955)
                ·
                  refine ⟨39506925874872410209361933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26337950583248273472907955 39506925874872410209361933)
                  ·
                    refine ⟨14815097203077153828510725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39506925874872410209361933 14815097203077153828510725)
                    ·
                      refine ⟨2777830725576966342845761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14815097203077153828510725 2777830725576966342845761)
                      ·
                        rfl

theorem cell23_5409806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5409806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409806 prefixEnd_5409806 := by exact prefixLift 5409806
  have htrace : WordTrace (prefixWord ++ tailWord_5409806) baseStart_5409806 baseEnd_5409806 := by
    simpa [prefixWord, tailWord_5409806, baseEnd_5409806] using wordTrace_append hprefix tailTrace_5409806
  have hstable : (prefixWord ++ tailWord_5409806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409806).length < 2 ^ (prefixWord ++ tailWord_5409806).sum := by decide
  have hdescent : baseEnd_5409806 < baseStart_5409806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409829 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 8]
def baseStart_5409829 : Nat := 118140960795 + 5409829 * 2 ^ 59
def prefixEnd_5409829 : Nat := 4983230072969 + 3 ^ 40 * 5409829 * 2
def baseEnd_5409829 : Nat := 308649170625779972539795

theorem tailTrace_5409829 : CollatzResearch.WordTrace tailWord_5409829 prefixEnd_5409829 308649170625779972539795 := by
  unfold tailWord_5409829
  simp only [CollatzResearch.WordTrace]
  refine ⟨197312673518120933080864541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131541782345413955387243027 197312673518120933080864541)
  ·
    refine ⟨73992252569295349905324203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197312673518120933080864541 73992252569295349905324203)
    ·
      refine ⟨110988378853943024857986305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73992252569295349905324203 110988378853943024857986305)
      ·
        refine ⟨83241284140457268643489729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110988378853943024857986305 83241284140457268643489729)
        ·
          refine ⟨62430963105342951482617297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83241284140457268643489729 62430963105342951482617297)
          ·
            refine ⟨46823222329007213611962973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62430963105342951482617297 46823222329007213611962973)
            ·
              refine ⟨17558708373377705104486115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46823222329007213611962973 17558708373377705104486115)
              ·
                refine ⟨26338062560066557656729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17558708373377705104486115 26338062560066557656729173)
                ·
                  refine ⟨308649170625779972539795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26338062560066557656729173 308649170625779972539795)
                  ·
                    rfl

theorem cell23_5409829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_5409829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409829 prefixEnd_5409829 := by exact prefixLift 5409829
  have htrace : WordTrace (prefixWord ++ tailWord_5409829) baseStart_5409829 baseEnd_5409829 := by
    simpa [prefixWord, tailWord_5409829, baseEnd_5409829] using wordTrace_append hprefix tailTrace_5409829
  have hstable : (prefixWord ++ tailWord_5409829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409829).length < 2 ^ (prefixWord ++ tailWord_5409829).sum := by decide
  have hdescent : baseEnd_5409829 < baseStart_5409829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409906 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_5409906 : Nat := 118140960795 + 5409906 * 2 ^ 59
def prefixEnd_5409906 : Nat := 4983230072969 + 3 ^ 40 * 5409906 * 2
def baseEnd_5409906 : Nat := 925960691214138650531767

theorem tailTrace_5409906 : CollatzResearch.WordTrace tailWord_5409906 prefixEnd_5409906 925960691214138650531767 := by
  unfold tailWord_5409906
  simp only [CollatzResearch.WordTrace]
  refine ⟨49328870484710493807854393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131543654625894650154278381 49328870484710493807854393)
  ·
    refine ⟨36996652863532870355890795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49328870484710493807854393 36996652863532870355890795)
    ·
      refine ⟨55494979295299305533836193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36996652863532870355890795 55494979295299305533836193)
      ·
        refine ⟨41621234471474479150377145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55494979295299305533836193 41621234471474479150377145)
        ·
          refine ⟨31215925853605859362782859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41621234471474479150377145 31215925853605859362782859)
          ·
            refine ⟨46823888780408789044174289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31215925853605859362782859 46823888780408789044174289)
            ·
              refine ⟨35117916585306591783130717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46823888780408789044174289 35117916585306591783130717)
              ·
                refine ⟨13169218719489971918674019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35117916585306591783130717 13169218719489971918674019)
                ·
                  refine ⟨19753828079234957878011029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13169218719489971918674019 19753828079234957878011029)
                  ·
                    refine ⟨925960691214138650531767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19753828079234957878011029 925960691214138650531767)
                    ·
                      rfl

theorem cell23_5409906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_5409906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409906 prefixEnd_5409906 := by exact prefixLift 5409906
  have htrace : WordTrace (prefixWord ++ tailWord_5409906) baseStart_5409906 baseEnd_5409906 := by
    simpa [prefixWord, tailWord_5409906, baseEnd_5409906] using wordTrace_append hprefix tailTrace_5409906
  have hstable : (prefixWord ++ tailWord_5409906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409906).length < 2 ^ (prefixWord ++ tailWord_5409906).sum := by decide
  have hdescent : baseEnd_5409906 < baseStart_5409906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409913 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_5409913 : Nat := 118140960795 + 5409913 * 2 ^ 59
def prefixEnd_5409913 : Nat := 4983230072969 + 3 ^ 40 * 5409913 * 2
def baseEnd_5409913 : Nat := 2777885668006997424207769

theorem tailTrace_5409913 : CollatzResearch.WordTrace tailWord_5409913 prefixEnd_5409913 2777885668006997424207769 := by
  unfold tailWord_5409913
  simp only [CollatzResearch.WordTrace]
  refine ⟨197315737249816615426922393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131543824833211076951281595 197315737249816615426922393)
  ·
    refine ⟨147986802937362461570191795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197315737249816615426922393 147986802937362461570191795)
    ·
      refine ⟨221980204406043692355287693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147986802937362461570191795 221980204406043692355287693)
      ·
        refine ⟨83242576652266384633232885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221980204406043692355287693 83242576652266384633232885)
        ·
          refine ⟨7803991561149973559365583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83242576652266384633232885 7803991561149973559365583)
          ·
            refine ⟨11705987341724960339048375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7803991561149973559365583 11705987341724960339048375)
            ·
              refine ⟨17558981012587440508572563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705987341724960339048375 17558981012587440508572563)
              ·
                refine ⟨26338471518881160762858845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17558981012587440508572563 26338471518881160762858845)
                ·
                  refine ⟨9876926819580435286072067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26338471518881160762858845 9876926819580435286072067)
                  ·
                    refine ⟨14815390229370652929108101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9876926819580435286072067 14815390229370652929108101)
                    ·
                      refine ⟨2777885668006997424207769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14815390229370652929108101 2777885668006997424207769)
                      ·
                        rfl

theorem cell23_5409913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_5409913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409913 prefixEnd_5409913 := by exact prefixLift 5409913
  have htrace : WordTrace (prefixWord ++ tailWord_5409913) baseStart_5409913 baseEnd_5409913 := by
    simpa [prefixWord, tailWord_5409913, baseEnd_5409913] using wordTrace_append hprefix tailTrace_5409913
  have hstable : (prefixWord ++ tailWord_5409913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409913).length < 2 ^ (prefixWord ++ tailWord_5409913).sum := by decide
  have hdescent : baseEnd_5409913 < baseStart_5409913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409930 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_5409930 : Nat := 118140960795 + 5409930 * 2 ^ 59
def prefixEnd_5409930 : Nat := 4983230072969 + 3 ^ 40 * 5409930 * 2
def baseEnd_5409930 : Nat := 2777894397178123857695191

theorem tailTrace_5409930 : CollatzResearch.WordTrace tailWord_5409930 prefixEnd_5409930 2777894397178123857695191 := by
  unfold tailWord_5409930
  simp only [CollatzResearch.WordTrace]
  refine ⟨49329089322688756832572811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131544238193836684886860829 49329089322688756832572811)
  ·
    refine ⟨73993633984033135248859217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49329089322688756832572811 73993633984033135248859217)
    ·
      refine ⟨55495225488024851436644413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73993633984033135248859217 55495225488024851436644413)
      ·
        refine ⟨20810709558009319288741655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55495225488024851436644413 20810709558009319288741655)
        ·
          refine ⟨31216064337013978933112483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20810709558009319288741655 31216064337013978933112483)
          ·
            refine ⟨46824096505520968399668725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31216064337013978933112483 46824096505520968399668725)
            ·
              refine ⟨4389759047392590787468943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46824096505520968399668725 4389759047392590787468943)
              ·
                refine ⟨6584638571088886181203415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389759047392590787468943 6584638571088886181203415)
                ·
                  refine ⟨9876957856633329271805123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6584638571088886181203415 9876957856633329271805123)
                  ·
                    refine ⟨14815436784949993907707685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9876957856633329271805123 14815436784949993907707685)
                    ·
                      refine ⟨2777894397178123857695191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14815436784949993907707685 2777894397178123857695191)
                      ·
                        rfl

theorem cell23_5409930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_5409930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409930 prefixEnd_5409930 := by exact prefixLift 5409930
  have htrace : WordTrace (prefixWord ++ tailWord_5409930) baseStart_5409930 baseEnd_5409930 := by
    simpa [prefixWord, tailWord_5409930, baseEnd_5409930] using wordTrace_append hprefix tailTrace_5409930
  have hstable : (prefixWord ++ tailWord_5409930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409930).length < 2 ^ (prefixWord ++ tailWord_5409930).sum := by decide
  have hdescent : baseEnd_5409930 < baseStart_5409930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409950 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_5409950 : Nat := 118140960795 + 5409950 * 2 ^ 59
def prefixEnd_5409950 : Nat := 4983230072969 + 3 ^ 40 * 5409950 * 2
def baseEnd_5409950 : Nat := 2777904666791213779445099

theorem tailTrace_5409950 : CollatzResearch.WordTrace tailWord_5409950 prefixEnd_5409950 2777904666791213779445099 := by
  unfold tailWord_5409950
  simp only [CollatzResearch.WordTrace]
  refine ⟨24664635843835321343252413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131544724500455047164012869 24664635843835321343252413)
  ·
    refine ⟨9249238441438245503719655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24664635843835321343252413 9249238441438245503719655)
    ·
      refine ⟨13873857662157368255579483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9249238441438245503719655 13873857662157368255579483)
      ·
        refine ⟨20810786493236052383369225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13873857662157368255579483 20810786493236052383369225)
        ·
          refine ⟨15608089869927039287526919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20810786493236052383369225 15608089869927039287526919)
          ·
            refine ⟨23412134804890558931290379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15608089869927039287526919 23412134804890558931290379)
            ·
              refine ⟨35118202207335838396935569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23412134804890558931290379 35118202207335838396935569)
              ·
                refine ⟨26338651655501878797701677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35118202207335838396935569 26338651655501878797701677)
                ·
                  refine ⟨9876994370813204549138129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26338651655501878797701677 9876994370813204549138129)
                  ·
                    refine ⟨7407745778109903411853597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9876994370813204549138129 7407745778109903411853597)
                    ·
                      refine ⟨2777904666791213779445099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7407745778109903411853597 2777904666791213779445099)
                      ·
                        rfl

theorem cell23_5409950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_5409950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409950 prefixEnd_5409950 := by exact prefixLift 5409950
  have htrace : WordTrace (prefixWord ++ tailWord_5409950) baseStart_5409950 baseEnd_5409950 := by
    simpa [prefixWord, tailWord_5409950, baseEnd_5409950] using wordTrace_append hprefix tailTrace_5409950
  have hstable : (prefixWord ++ tailWord_5409950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409950).length < 2 ^ (prefixWord ++ tailWord_5409950).sum := by decide
  have hdescent : baseEnd_5409950 < baseStart_5409950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409984 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 1, 2, 3]
def baseStart_5409984 : Nat := 118140960795 + 5409984 * 2 ^ 59
def prefixEnd_5409984 : Nat := 4983230072969 + 3 ^ 40 * 5409984 * 2
def baseEnd_5409984 : Nat := 2777922125133466646419943

theorem tailTrace_5409984 : CollatzResearch.WordTrace tailWord_5409984 prefixEnd_5409984 2777922125133466646419943 := by
  unfold tailWord_5409984
  simp only [CollatzResearch.WordTrace]
  refine ⟨98659163416279697276378503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131545551221706263035171337 98659163416279697276378503)
  ·
    refine ⟨147988745124419545914567755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98659163416279697276378503 147988745124419545914567755)
    ·
      refine ⟨221983117686629318871851633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147988745124419545914567755 221983117686629318871851633)
      ·
        refine ⟨166487338264971989153888725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221983117686629318871851633 166487338264971989153888725)
        ·
          refine ⟨3902046990585280995794267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 166487338264971989153888725 3902046990585280995794267)
          ·
            refine ⟨5853070485877921493691401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902046990585280995794267 5853070485877921493691401)
            ·
              refine ⟨4389802864408441120268551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853070485877921493691401 4389802864408441120268551)
              ·
                refine ⟨6584704296612661680402827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389802864408441120268551 6584704296612661680402827)
                ·
                  refine ⟨9877056444918992520604241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6584704296612661680402827 9877056444918992520604241)
                  ·
                    refine ⟨7407792333689244390453181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9877056444918992520604241 7407792333689244390453181)
                    ·
                      refine ⟨2777922125133466646419943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7407792333689244390453181 2777922125133466646419943)
                      ·
                        rfl

theorem cell23_5409984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_5409984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409984 prefixEnd_5409984 := by exact prefixLift 5409984
  have htrace : WordTrace (prefixWord ++ tailWord_5409984) baseStart_5409984 baseEnd_5409984 := by
    simpa [prefixWord, tailWord_5409984, baseEnd_5409984] using wordTrace_append hprefix tailTrace_5409984
  have hstable : (prefixWord ++ tailWord_5409984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409984).length < 2 ^ (prefixWord ++ tailWord_5409984).sum := by decide
  have hdescent : baseEnd_5409984 < baseStart_5409984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410020 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_5410020 : Nat := 118140960795 + 5410020 * 2 ^ 59
def prefixEnd_5410020 : Nat := 4983230072969 + 3 ^ 40 * 5410020 * 2
def baseEnd_5410020 : Nat := 2777940610437028505569777

theorem tailTrace_5410020 : CollatzResearch.WordTrace tailWord_5410020 prefixEnd_5410020 2777940610437028505569777 := by
  unfold tailWord_5410020
  simp only [CollatzResearch.WordTrace]
  refine ⟨98659819930214486350533757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131546426573619315134045009 98659819930214486350533757)
  ·
    refine ⟨36997432473830432381450159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98659819930214486350533757 36997432473830432381450159)
    ·
      refine ⟨55496148710745648572175239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36997432473830432381450159 55496148710745648572175239)
      ·
        refine ⟨83244223066118472858262859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55496148710745648572175239 83244223066118472858262859)
        ·
          refine ⟨124866334599177709287394289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83244223066118472858262859 124866334599177709287394289)
          ·
            refine ⟨93649750949383281965545717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124866334599177709287394289 93649750949383281965545717)
            ·
              refine ⟨8779664151504682684269911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93649750949383281965545717 8779664151504682684269911)
              ·
                refine ⟨13169496227257024026404867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779664151504682684269911 13169496227257024026404867)
                ·
                  refine ⟨19754244340885536039607301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13169496227257024026404867 19754244340885536039607301)
                  ·
                    refine ⟨3703920813916038007426369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19754244340885536039607301 3703920813916038007426369)
                    ·
                      refine ⟨2777940610437028505569777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703920813916038007426369 2777940610437028505569777)
                      ·
                        rfl

theorem cell23_5410020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_5410020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410020 prefixEnd_5410020 := by exact prefixLift 5410020
  have htrace : WordTrace (prefixWord ++ tailWord_5410020) baseStart_5410020 baseEnd_5410020 := by
    simpa [prefixWord, tailWord_5410020, baseEnd_5410020] using wordTrace_append hprefix tailTrace_5410020
  have hstable : (prefixWord ++ tailWord_5410020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410020).length < 2 ^ (prefixWord ++ tailWord_5410020).sum := by decide
  have hdescent : baseEnd_5410020 < baseStart_5410020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410090 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5410090 : Nat := 118140960795 + 5410090 * 2 ^ 59
def prefixEnd_5410090 : Nat := 4983230072969 + 3 ^ 40 * 5410090 * 2
def baseEnd_5410090 : Nat := 925992184694281077231485

theorem tailTrace_5410090 : CollatzResearch.WordTrace tailWord_5410090 prefixEnd_5410090 925992184694281077231485 := by
  unfold tailWord_5410090
  simp only [CollatzResearch.WordTrace]
  refine ⟨49330548242543843664028931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131548128646783583104077149 49330548242543843664028931)
  ·
    refine ⟨73995822363815765496043397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49330548242543843664028931 73995822363815765496043397)
    ·
      refine ⟨13874216693215456030508137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73995822363815765496043397 13874216693215456030508137)
      ·
        refine ⟨10405662519911592022881103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13874216693215456030508137 10405662519911592022881103)
        ·
          refine ⟨15608493779867388034321655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10405662519911592022881103 15608493779867388034321655)
          ·
            refine ⟨23412740669801082051482483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15608493779867388034321655 23412740669801082051482483)
            ·
              refine ⟨35119111004701623077223725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23412740669801082051482483 35119111004701623077223725)
              ·
                refine ⟨13169666626763108653958897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35119111004701623077223725 13169666626763108653958897)
                ·
                  refine ⟨9877249970072331490469173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13169666626763108653958897 9877249970072331490469173)
                  ·
                    refine ⟨925992184694281077231485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9877249970072331490469173 925992184694281077231485)
                    ·
                      rfl

theorem cell23_5410090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5410090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410090 prefixEnd_5410090 := by exact prefixLift 5410090
  have htrace : WordTrace (prefixWord ++ tailWord_5410090) baseStart_5410090 baseEnd_5410090 := by
    simpa [prefixWord, tailWord_5410090, baseEnd_5410090] using wordTrace_append hprefix tailTrace_5410090
  have hstable : (prefixWord ++ tailWord_5410090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410090).length < 2 ^ (prefixWord ++ tailWord_5410090).sum := by decide
  have hdescent : baseEnd_5410090 < baseStart_5410090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410110 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5410110 : Nat := 118140960795 + 5410110 * 2 ^ 59
def prefixEnd_5410110 : Nat := 4983230072969 + 3 ^ 40 * 5410110 * 2
def baseEnd_5410110 : Nat := 2777986823695933153444363

theorem tailTrace_5410110 : CollatzResearch.WordTrace tailWord_5410110 prefixEnd_5410110 2777986823695933153444363 := by
  unfold tailWord_5410110
  simp only [CollatzResearch.WordTrace]
  refine ⟨24665365303762864758980473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131548614953401945381229189 24665365303762864758980473)
  ·
    refine ⟨18499023977822148569235355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24665365303762864758980473 18499023977822148569235355)
    ·
      refine ⟨27748535966733222853853033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18499023977822148569235355 27748535966733222853853033)
      ·
        refine ⟨20811401975049917140389775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27748535966733222853853033 20811401975049917140389775)
        ·
          refine ⟨31217102962574875710584663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20811401975049917140389775 31217102962574875710584663)
          ·
            refine ⟨46825654443862313565876995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31217102962574875710584663 46825654443862313565876995)
            ·
              refine ⟨70238481665793470348815493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46825654443862313565876995 70238481665793470348815493)
              ·
                refine ⟨13169715312336275690402905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70238481665793470348815493 13169715312336275690402905)
                ·
                  refine ⟨9877286484252206767802179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13169715312336275690402905 9877286484252206767802179)
                  ·
                    refine ⟨14815929726378310151703269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9877286484252206767802179 14815929726378310151703269)
                    ·
                      refine ⟨2777986823695933153444363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14815929726378310151703269 2777986823695933153444363)
                      ·
                        rfl

theorem cell23_5410110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5410110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410110 prefixEnd_5410110 := by exact prefixLift 5410110
  have htrace : WordTrace (prefixWord ++ tailWord_5410110) baseStart_5410110 baseEnd_5410110 := by
    simpa [prefixWord, tailWord_5410110, baseEnd_5410110] using wordTrace_append hprefix tailTrace_5410110
  have hstable : (prefixWord ++ tailWord_5410110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410110).length < 2 ^ (prefixWord ++ tailWord_5410110).sum := by decide
  have hdescent : baseEnd_5410110 < baseStart_5410110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410141 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5410141 : Nat := 118140960795 + 5410141 * 2 ^ 59
def prefixEnd_5410141 : Nat := 4983230072969 + 3 ^ 40 * 5410141 * 2
def baseEnd_5410141 : Nat := 926000913865407510718907

theorem tailTrace_5410141 : CollatzResearch.WordTrace tailWord_5410141 prefixEnd_5410141 926000913865407510718907 := by
  unfold tailWord_5410141
  simp only [CollatzResearch.WordTrace]
  refine ⟨197324053092990610366222277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131549368728660406910814851 197324053092990610366222277)
  ·
    refine ⟨36998259954935739443666677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197324053092990610366222277 36998259954935739443666677)
    ·
      refine ⟨3468586870775225572843751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36998259954935739443666677 3468586870775225572843751)
      ·
        refine ⟨5202880306162838359265627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468586870775225572843751 5202880306162838359265627)
        ·
          refine ⟨7804320459244257538898441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5202880306162838359265627 7804320459244257538898441)
          ·
            refine ⟨5853240344433193154173831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804320459244257538898441 5853240344433193154173831)
            ·
              refine ⟨8779860516649789731260747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853240344433193154173831 8779860516649789731260747)
              ·
                refine ⟨13169790774974684596891121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779860516649789731260747 13169790774974684596891121)
                ·
                  refine ⟨9877343081231013447668341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13169790774974684596891121 9877343081231013447668341)
                  ·
                    refine ⟨926000913865407510718907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9877343081231013447668341 926000913865407510718907)
                    ·
                      rfl

theorem cell23_5410141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5410141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410141 prefixEnd_5410141 := by exact prefixLift 5410141
  have htrace : WordTrace (prefixWord ++ tailWord_5410141) baseStart_5410141 baseEnd_5410141 := by
    simpa [prefixWord, tailWord_5410141, baseEnd_5410141] using wordTrace_append hprefix tailTrace_5410141
  have hstable : (prefixWord ++ tailWord_5410141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410141).length < 2 ^ (prefixWord ++ tailWord_5410141).sum := by decide
  have hdescent : baseEnd_5410141 < baseStart_5410141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410147 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 3]
def baseStart_5410147 : Nat := 118140960795 + 5410147 * 2 ^ 59
def prefixEnd_5410147 : Nat := 4983230072969 + 3 ^ 40 * 5410147 * 2
def baseEnd_5410147 : Nat := 2778005822480149508681693

theorem tailTrace_5410147 : CollatzResearch.WordTrace tailWord_5410147 prefixEnd_5410147 2778005822480149508681693 := by
  unfold tailWord_5410147
  simp only [CollatzResearch.WordTrace]
  refine ⟨197324271930968873390940695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131549514620645915593960463 197324271930968873390940695)
  ·
    refine ⟨295986407896453310086411043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197324271930968873390940695 295986407896453310086411043)
    ·
      refine ⟨443979611844679965129616565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295986407896453310086411043 443979611844679965129616565)
      ·
        refine ⟨41623088610438746730901553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 443979611844679965129616565 41623088610438746730901553)
        ·
          refine ⟨31217316457829060048176165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41623088610438746730901553 31217316457829060048176165)
          ·
            refine ⟨5853246835842948759033031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31217316457829060048176165 5853246835842948759033031)
            ·
              refine ⟨8779870253764423138549547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853246835842948759033031 8779870253764423138549547)
              ·
                refine ⟨13169805380646634707824321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779870253764423138549547 13169805380646634707824321)
                ·
                  refine ⟨9877354035484976030868241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13169805380646634707824321 9877354035484976030868241)
                  ·
                    refine ⟨7408015526613732023151181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9877354035484976030868241 7408015526613732023151181)
                    ·
                      refine ⟨2778005822480149508681693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408015526613732023151181 2778005822480149508681693)
                      ·
                        rfl

theorem cell23_5410147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_5410147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410147 prefixEnd_5410147 := by exact prefixLift 5410147
  have htrace : WordTrace (prefixWord ++ tailWord_5410147) baseStart_5410147 baseEnd_5410147 := by
    simpa [prefixWord, tailWord_5410147, baseEnd_5410147] using wordTrace_append hprefix tailTrace_5410147
  have hstable : (prefixWord ++ tailWord_5410147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410147).length < 2 ^ (prefixWord ++ tailWord_5410147).sum := by decide
  have hdescent : baseEnd_5410147 < baseStart_5410147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410160 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 5, 1, 3]
def baseStart_5410160 : Nat := 118140960795 + 5410160 * 2 ^ 59
def prefixEnd_5410160 : Nat := 4983230072969 + 3 ^ 40 * 5410160 * 2
def baseEnd_5410160 : Nat := 2778012497728657957819133

theorem tailTrace_5410160 : CollatzResearch.WordTrace tailWord_5410160 prefixEnd_5410160 2778012497728657957819133 := by
  unfold tailWord_5410160
  simp only [CollatzResearch.WordTrace]
  refine ⟨98662373039960888305581967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131549830719947851074109289 98662373039960888305581967)
  ·
    refine ⟨147993559559941332458372951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98662373039960888305581967 147993559559941332458372951)
    ·
      refine ⟨221990339339911998687559427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147993559559941332458372951 221990339339911998687559427)
      ·
        refine ⟨332985509009867998031339141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221990339339911998687559427 332985509009867998031339141)
        ·
          refine ⟨62434782939350249630876089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332985509009867998031339141 62434782939350249630876089)
          ·
            refine ⟨46826087204512687223157067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62434782939350249630876089 46826087204512687223157067)
            ·
              refine ⟨70239130806769030834735601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46826087204512687223157067 70239130806769030834735601)
              ·
                refine ⟨52679348105076773126051701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70239130806769030834735601 52679348105076773126051701)
                ·
                  refine ⟨4938688884850947480567347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52679348105076773126051701 4938688884850947480567347)
                  ·
                    refine ⟨7408033327276421220851021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4938688884850947480567347 7408033327276421220851021)
                    ·
                      refine ⟨2778012497728657957819133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408033327276421220851021 2778012497728657957819133)
                      ·
                        rfl

theorem cell23_5410160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_5410160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410160 prefixEnd_5410160 := by exact prefixLift 5410160
  have htrace : WordTrace (prefixWord ++ tailWord_5410160) baseStart_5410160 baseEnd_5410160 := by
    simpa [prefixWord, tailWord_5410160, baseEnd_5410160] using wordTrace_append hprefix tailTrace_5410160
  have hstable : (prefixWord ++ tailWord_5410160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410160).length < 2 ^ (prefixWord ++ tailWord_5410160).sum := by decide
  have hdescent : baseEnd_5410160 < baseStart_5410160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410244 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5410244 : Nat := 118140960795 + 5410244 * 2 ^ 59
def prefixEnd_5410244 : Nat := 4983230072969 + 3 ^ 40 * 5410244 * 2
def baseEnd_5410244 : Nat := 926018543367878543056249

theorem tailTrace_5410244 : CollatzResearch.WordTrace tailWord_5410244 prefixEnd_5410244 926018543367878543056249 := by
  unfold tailWord_5410244
  simp only [CollatzResearch.WordTrace]
  refine ⟨98663904905808729478610893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131551873207744972638147857 98663904905808729478610893)
  ·
    refine ⟨36998964339678273554479085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98663904905808729478610893 36998964339678273554479085)
    ·
      refine ⟨13874611627379352582929657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36998964339678273554479085 13874611627379352582929657)
      ·
        refine ⟨10405958720534514437197243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13874611627379352582929657 10405958720534514437197243)
        ·
          refine ⟨15608938080801771655795865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10405958720534514437197243 15608938080801771655795865)
          ·
            refine ⟨11706703560601328741846899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15608938080801771655795865 11706703560601328741846899)
            ·
              refine ⟨17560055340901993112770349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11706703560601328741846899 17560055340901993112770349)
              ·
                refine ⟨6585020752838247417288881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17560055340901993112770349 6585020752838247417288881)
                ·
                  refine ⟨4938765564628685562966661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6585020752838247417288881 4938765564628685562966661)
                  ·
                    refine ⟨926018543367878543056249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4938765564628685562966661 926018543367878543056249)
                    ·
                      rfl

theorem cell23_5410244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5410244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410244 prefixEnd_5410244 := by exact prefixLift 5410244
  have htrace : WordTrace (prefixWord ++ tailWord_5410244) baseStart_5410244 baseEnd_5410244 := by
    simpa [prefixWord, tailWord_5410244, baseEnd_5410244] using wordTrace_append hprefix tailTrace_5410244
  have hstable : (prefixWord ++ tailWord_5410244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410244).length < 2 ^ (prefixWord ++ tailWord_5410244).sum := by decide
  have hdescent : baseEnd_5410244 < baseStart_5410244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410263 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5410263 : Nat := 118140960795 + 5410263 * 2 ^ 59
def prefixEnd_5410263 : Nat := 4983230072969 + 3 ^ 40 * 5410263 * 2
def baseEnd_5410263 : Nat := 2778065386236071054831159

theorem tailTrace_5410263 : CollatzResearch.WordTrace tailWord_5410263 prefixEnd_5410263 2778065386236071054831159 := by
  unfold tailWord_5410263
  simp only [CollatzResearch.WordTrace]
  refine ⟨197328502798548625202163443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131552335199032416801442295 197328502798548625202163443)
  ·
    refine ⟨295992754197822937803245165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197328502798548625202163443 295992754197822937803245165)
    ·
      refine ⟨110997282824183601676216937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295992754197822937803245165 110997282824183601676216937)
      ·
        refine ⟨83247962118137701257162703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110997282824183601676216937 83247962118137701257162703)
        ·
          refine ⟨124871943177206551885744055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83247962118137701257162703 124871943177206551885744055)
          ·
            refine ⟨187307914765809827828616083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124871943177206551885744055 187307914765809827828616083)
            ·
              refine ⟨280961872148714741742924125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187307914765809827828616083 280961872148714741742924125)
              ·
                refine ⟨105360702055768028153596547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280961872148714741742924125 105360702055768028153596547)
                ·
                  refine ⟨158041053083652042230394821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105360702055768028153596547 158041053083652042230394821)
                  ·
                    refine ⟨29632697453184757918199029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158041053083652042230394821 29632697453184757918199029)
                    ·
                      refine ⟨2778065386236071054831159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29632697453184757918199029 2778065386236071054831159)
                      ·
                        rfl

theorem cell23_5410263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5410263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410263 prefixEnd_5410263 := by exact prefixLift 5410263
  have htrace : WordTrace (prefixWord ++ tailWord_5410263) baseStart_5410263 baseEnd_5410263 := by
    simpa [prefixWord, tailWord_5410263, baseEnd_5410263] using wordTrace_append hprefix tailTrace_5410263
  have hstable : (prefixWord ++ tailWord_5410263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410263).length < 2 ^ (prefixWord ++ tailWord_5410263).sum := by decide
  have hdescent : baseEnd_5410263 < baseStart_5410263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410294 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5410294 : Nat := 118140960795 + 5410294 * 2 ^ 59
def prefixEnd_5410294 : Nat := 4983230072969 + 3 ^ 40 * 5410294 * 2
def baseEnd_5410294 : Nat := 2778081304136360433543517

theorem tailTrace_5410294 : CollatzResearch.WordTrace tailWord_5410294 prefixEnd_5410294 2778081304136360433543517 := by
  unfold tailWord_5410294
  simp only [CollatzResearch.WordTrace]
  refine ⟨12333102091339769843533871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131553088974290878331027957 12333102091339769843533871)
  ·
    refine ⟨18499653137009654765300807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12333102091339769843533871 18499653137009654765300807)
    ·
      refine ⟨27749479705514482147951211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18499653137009654765300807 27749479705514482147951211)
      ·
        refine ⟨41624219558271723221926817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27749479705514482147951211 41624219558271723221926817)
        ·
          refine ⟨31218164668703792416445113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41624219558271723221926817 31218164668703792416445113)
          ·
            refine ⟨23413623501527844312333835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31218164668703792416445113 23413623501527844312333835)
            ·
              refine ⟨35120435252291766468500753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23413623501527844312333835 35120435252291766468500753)
              ·
                refine ⟨26340326439218824851375565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35120435252291766468500753 26340326439218824851375565)
                ·
                  refine ⟨9877622414707059319265837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26340326439218824851375565 9877622414707059319265837)
                  ·
                    refine ⟨3704108405515147244724689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9877622414707059319265837 3704108405515147244724689)
                    ·
                      refine ⟨2778081304136360433543517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704108405515147244724689 2778081304136360433543517)
                      ·
                        rfl

theorem cell23_5410294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5410294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410294 prefixEnd_5410294 := by exact prefixLift 5410294
  have htrace : WordTrace (prefixWord ++ tailWord_5410294) baseStart_5410294 baseEnd_5410294 := by
    simpa [prefixWord, tailWord_5410294, baseEnd_5410294] using wordTrace_append hprefix tailTrace_5410294
  have hstable : (prefixWord ++ tailWord_5410294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410294).length < 2 ^ (prefixWord ++ tailWord_5410294).sum := by decide
  have hdescent : baseEnd_5410294 < baseStart_5410294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410328 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 1, 3, 2]
def baseStart_5410328 : Nat := 118140960795 + 5410328 * 2 ^ 59
def prefixEnd_5410328 : Nat := 4983230072969 + 3 ^ 40 * 5410328 * 2
def baseEnd_5410328 : Nat := 2778098762478613300518361

theorem tailTrace_5410328 : CollatzResearch.WordTrace tailWord_5410328 prefixEnd_5410328 2778098762478613300518361 := by
  unfold tailWord_5410328
  simp only [CollatzResearch.WordTrace]
  refine ⟨98665436771656570651639819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131553915695542094202186425 98665436771656570651639819)
  ·
    refine ⟨147998155157484855977459729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98665436771656570651639819 147998155157484855977459729)
    ·
      refine ⟨110998616368113641983094797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147998155157484855977459729 110998616368113641983094797)
      ·
        refine ⟨41624481138042615743660549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110998616368113641983094797 41624481138042615743660549)
        ·
          refine ⟨7804590213382990451936353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41624481138042615743660549 7804590213382990451936353)
          ·
            refine ⟨5853442660037242838952265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804590213382990451936353 5853442660037242838952265)
            ·
              refine ⟨4390081995027932129214199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853442660037242838952265 4390081995027932129214199)
              ·
                refine ⟨6585122992541898193821299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390081995027932129214199 6585122992541898193821299)
                ·
                  refine ⟨9877684488812847290731949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585122992541898193821299 9877684488812847290731949)
                  ·
                    refine ⟨3704131683304817734024481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9877684488812847290731949 3704131683304817734024481)
                    ·
                      refine ⟨2778098762478613300518361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704131683304817734024481 2778098762478613300518361)
                      ·
                        rfl

theorem cell23_5410328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_5410328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410328 prefixEnd_5410328 := by exact prefixLift 5410328
  have htrace : WordTrace (prefixWord ++ tailWord_5410328) baseStart_5410328 baseEnd_5410328 := by
    simpa [prefixWord, tailWord_5410328, baseEnd_5410328] using wordTrace_append hprefix tailTrace_5410328
  have hstable : (prefixWord ++ tailWord_5410328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410328).length < 2 ^ (prefixWord ++ tailWord_5410328).sum := by decide
  have hdescent : baseEnd_5410328 < baseStart_5410328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410357 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_5410357 : Nat := 118140960795 + 5410357 * 2 ^ 59
def prefixEnd_5410357 : Nat := 4983230072969 + 3 ^ 40 * 5410357 * 2
def baseEnd_5410357 : Nat := 2778113653417593687055727

theorem tailTrace_5410357 : CollatzResearch.WordTrace tailWord_5410357 prefixEnd_5410357 2778113653417593687055727 := by
  unfold tailWord_5410357
  simp only [CollatzResearch.WordTrace]
  refine ⟨197331931260208079256085325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131554620840138719504056883 197331931260208079256085325)
  ·
    refine ⟨73999474222578029721031997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197331931260208079256085325 73999474222578029721031997)
    ·
      refine ⟨27749802833466761145386999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73999474222578029721031997 27749802833466761145386999)
      ·
        refine ⟨41624704250200141718080499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27749802833466761145386999 41624704250200141718080499)
        ·
          refine ⟨62437056375300212577120749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41624704250200141718080499 62437056375300212577120749)
          ·
            refine ⟨23413896140737579716420281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62437056375300212577120749 23413896140737579716420281)
            ·
              refine ⟨17560422105553184787315211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23413896140737579716420281 17560422105553184787315211)
              ·
                refine ⟨26340633158329777180972817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17560422105553184787315211 26340633158329777180972817)
                ·
                  refine ⟨19755474868747332885729613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26340633158329777180972817 19755474868747332885729613)
                  ·
                    refine ⟨7408303075780249832148605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19755474868747332885729613 7408303075780249832148605)
                    ·
                      refine ⟨2778113653417593687055727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408303075780249832148605 2778113653417593687055727)
                      ·
                        rfl

theorem cell23_5410357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_5410357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410357 prefixEnd_5410357 := by exact prefixLift 5410357
  have htrace : WordTrace (prefixWord ++ tailWord_5410357) baseStart_5410357 baseEnd_5410357 := by
    simpa [prefixWord, tailWord_5410357, baseEnd_5410357] using wordTrace_append hprefix tailTrace_5410357
  have hstable : (prefixWord ++ tailWord_5410357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410357).length < 2 ^ (prefixWord ++ tailWord_5410357).sum := by decide
  have hdescent : baseEnd_5410357 < baseStart_5410357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410358 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5410358 : Nat := 118140960795 + 5410358 * 2 ^ 59
def prefixEnd_5410358 : Nat := 4983230072969 + 3 ^ 40 * 5410358 * 2
def baseEnd_5410358 : Nat := 2778114166898248183143223

theorem tailTrace_5410358 : CollatzResearch.WordTrace tailWord_5410358 prefixEnd_5410358 2778114166898248183143223 := by
  unfold tailWord_5410358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12333247983325278526679483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131554645155469637617914485 12333247983325278526679483)
  ·
    refine ⟨18499871974987917790019225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12333247983325278526679483 18499871974987917790019225)
    ·
      refine ⟨13874903981240938342514419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18499871974987917790019225 13874903981240938342514419)
      ·
        refine ⟨20812355971861407513771629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13874903981240938342514419 20812355971861407513771629)
        ·
          refine ⟨7804633489448027817664361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20812355971861407513771629 7804633489448027817664361)
          ·
            refine ⟨5853475117086020863248271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804633489448027817664361 5853475117086020863248271)
            ·
              refine ⟨8780212675629031294872407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853475117086020863248271 8780212675629031294872407)
              ·
                refine ⟨13170319013443546942308611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8780212675629031294872407 13170319013443546942308611)
                ·
                  refine ⟨19755478520165320413462917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13170319013443546942308611 19755478520165320413462917)
                  ·
                    refine ⟨3704152222530997577524297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19755478520165320413462917 3704152222530997577524297)
                    ·
                      refine ⟨2778114166898248183143223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704152222530997577524297 2778114166898248183143223)
                      ·
                        rfl

theorem cell23_5410358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5410358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410358 prefixEnd_5410358 := by exact prefixLift 5410358
  have htrace : WordTrace (prefixWord ++ tailWord_5410358) baseStart_5410358 baseEnd_5410358 := by
    simpa [prefixWord, tailWord_5410358, baseEnd_5410358] using wordTrace_append hprefix tailTrace_5410358
  have hstable : (prefixWord ++ tailWord_5410358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410358).length < 2 ^ (prefixWord ++ tailWord_5410358).sum := by decide
  have hdescent : baseEnd_5410358 < baseStart_5410358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410360 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_5410360 : Nat := 118140960795 + 5410360 * 2 ^ 59
def prefixEnd_5410360 : Nat := 4983230072969 + 3 ^ 40 * 5410360 * 2
def baseEnd_5410360 : Nat := 926038397953185725106071

theorem tailTrace_5410360 : CollatzResearch.WordTrace tailWord_5410360 prefixEnd_5410360 926038397953185725106071 := by
  unfold tailWord_5410360
  simp only [CollatzResearch.WordTrace]
  refine ⟨98666020339598605384222267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131554693786131473845629689 98666020339598605384222267)
  ·
    refine ⟨147999030509397908076333401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98666020339598605384222267 147999030509397908076333401)
    ·
      refine ⟨110999272882048431057250051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147999030509397908076333401 110999272882048431057250051)
      ·
        refine ⟨166498909323072646585875077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110999272882048431057250051 166498909323072646585875077)
        ·
          refine ⟨31218545498076121234851577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166498909323072646585875077 31218545498076121234851577)
          ·
            refine ⟨23413909123557090926138683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31218545498076121234851577 23413909123557090926138683)
            ·
              refine ⟨35120863685335636389208025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23413909123557090926138683 35120863685335636389208025)
              ·
                refine ⟨26340647764001727291906019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35120863685335636389208025 26340647764001727291906019)
                ·
                  refine ⟨39510971646002590937859029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26340647764001727291906019 39510971646002590937859029)
                  ·
                    refine ⟨926038397953185725106071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39510971646002590937859029 926038397953185725106071)
                    ·
                      rfl

theorem cell23_5410360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_5410360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410360 prefixEnd_5410360 := by exact prefixLift 5410360
  have htrace : WordTrace (prefixWord ++ tailWord_5410360) baseStart_5410360 baseEnd_5410360 := by
    simpa [prefixWord, tailWord_5410360, baseEnd_5410360] using wordTrace_append hprefix tailTrace_5410360
  have hstable : (prefixWord ++ tailWord_5410360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410360).length < 2 ^ (prefixWord ++ tailWord_5410360).sum := by decide
  have hdescent : baseEnd_5410360 < baseStart_5410360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410477 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5410477 : Nat := 118140960795 + 5410477 * 2 ^ 59
def prefixEnd_5410477 : Nat := 4983230072969 + 3 ^ 40 * 5410477 * 2
def baseEnd_5410477 : Nat := 2778175271096133217555175

theorem tailTrace_5410477 : CollatzResearch.WordTrace tailWord_5410477 prefixEnd_5410477 2778175271096133217555175 := by
  unfold tailWord_5410477
  simp only [CollatzResearch.WordTrace]
  refine ⟨197336308019773339750453685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131557538679848893166969123 197336308019773339750453685)
  ·
    refine ⟨18500278876853750601605033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197336308019773339750453685 18500278876853750601605033)
    ·
      refine ⟨13875209157640312951203775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18500278876853750601605033 13875209157640312951203775)
      ·
        refine ⟨20812813736460469426805663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13875209157640312951203775 20812813736460469426805663)
        ·
          refine ⟨31219220604690704140208495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20812813736460469426805663 31219220604690704140208495)
          ·
            refine ⟨46828830907036056210312743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31219220604690704140208495 46828830907036056210312743)
            ·
              refine ⟨70243246360554084315469115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46828830907036056210312743 70243246360554084315469115)
              ·
                refine ⟨105364869540831126473203673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70243246360554084315469115 105364869540831126473203673)
                ·
                  refine ⟨79023652155623344854902755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105364869540831126473203673 79023652155623344854902755)
                  ·
                    refine ⟨118535478233435017282354133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79023652155623344854902755 118535478233435017282354133)
                    ·
                      refine ⟨2778175271096133217555175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118535478233435017282354133 2778175271096133217555175)
                      ·
                        rfl

theorem cell23_5410477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5410477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410477 prefixEnd_5410477 := by exact prefixLift 5410477
  have htrace : WordTrace (prefixWord ++ tailWord_5410477) baseStart_5410477 baseEnd_5410477 := by
    simpa [prefixWord, tailWord_5410477, baseEnd_5410477] using wordTrace_append hprefix tailTrace_5410477
  have hstable : (prefixWord ++ tailWord_5410477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410477).length < 2 ^ (prefixWord ++ tailWord_5410477).sum := by decide
  have hdescent : baseEnd_5410477 < baseStart_5410477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410504 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_5410504 : Nat := 118140960795 + 5410504 * 2 ^ 59
def prefixEnd_5410504 : Nat := 4983230072969 + 3 ^ 40 * 5410504 * 2
def baseEnd_5410504 : Nat := 2778189135073804611917551

theorem tailTrace_5410504 : CollatzResearch.WordTrace tailWord_5410504 prefixEnd_5410504 2778189135073804611917551 := by
  unfold tailWord_5410504
  simp only [CollatzResearch.WordTrace]
  refine ⟨98668646395337761680843283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131558195193783682241124377 98668646395337761680843283)
  ·
    refine ⟨148002969593006642521264925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98668646395337761680843283 148002969593006642521264925)
    ·
      refine ⟨55501113597377490945474347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148002969593006642521264925 55501113597377490945474347)
      ·
        refine ⟨83251670396066236418211521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55501113597377490945474347 83251670396066236418211521)
        ·
          refine ⟨62438752797049677313658641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83251670396066236418211521 62438752797049677313658641)
          ·
            refine ⟨46829064597787257985243981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62438752797049677313658641 46829064597787257985243981)
            ·
              refine ⟨17560899224170221744466493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46829064597787257985243981 17560899224170221744466493)
              ·
                refine ⟨6585337209063833154174935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17560899224170221744466493 6585337209063833154174935)
                ·
                  refine ⟨9878005813595749731262403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585337209063833154174935 9878005813595749731262403)
                  ·
                    refine ⟨14817008720393624596893605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9878005813595749731262403 14817008720393624596893605)
                    ·
                      refine ⟨2778189135073804611917551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14817008720393624596893605 2778189135073804611917551)
                      ·
                        rfl

theorem cell23_5410504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_5410504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410504 prefixEnd_5410504 := by exact prefixLift 5410504
  have htrace : WordTrace (prefixWord ++ tailWord_5410504) baseStart_5410504 baseEnd_5410504 := by
    simpa [prefixWord, tailWord_5410504, baseEnd_5410504] using wordTrace_append hprefix tailTrace_5410504
  have hstable : (prefixWord ++ tailWord_5410504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410504).length < 2 ^ (prefixWord ++ tailWord_5410504).sum := by decide
  have hdescent : baseEnd_5410504 < baseStart_5410504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410521 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 3, 2, 2]
def baseStart_5410521 : Nat := 118140960795 + 5410521 * 2 ^ 59
def prefixEnd_5410521 : Nat := 4983230072969 + 3 ^ 40 * 5410521 * 2
def baseEnd_5410521 : Nat := 2778197864244931045404973

theorem tailTrace_5410521 : CollatzResearch.WordTrace tailWord_5410521 prefixEnd_5410521 2778197864244931045404973 := by
  unfold tailWord_5410521
  simp only [CollatzResearch.WordTrace]
  refine ⟨197337912831613935265055417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131558608554409290176703611 197337912831613935265055417)
  ·
    refine ⟨148003434623710451448791563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197337912831613935265055417 148003434623710451448791563)
    ·
      refine ⟨222005151935565677173187345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148003434623710451448791563 222005151935565677173187345)
      ·
        refine ⟨166503863951674257879890509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222005151935565677173187345 166503863951674257879890509)
        ·
          refine ⟨62438948981877846704958941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166503863951674257879890509 62438948981877846704958941)
          ·
            refine ⟨23414605868204192514359603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62438948981877846704958941 23414605868204192514359603)
            ·
              refine ⟨35121908802306288771539405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23414605868204192514359603 35121908802306288771539405)
              ·
                refine ⟨13170715800864858289327277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35121908802306288771539405 13170715800864858289327277)
                ·
                  refine ⟨4939018425324321858497729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13170715800864858289327277 4939018425324321858497729)
                  ·
                    refine ⟨3704263818993241393873297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939018425324321858497729 3704263818993241393873297)
                    ·
                      refine ⟨2778197864244931045404973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704263818993241393873297 2778197864244931045404973)
                      ·
                        rfl

theorem cell23_5410521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_5410521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410521 prefixEnd_5410521 := by exact prefixLift 5410521
  have htrace : WordTrace (prefixWord ++ tailWord_5410521) baseStart_5410521 baseEnd_5410521 := by
    simpa [prefixWord, tailWord_5410521, baseEnd_5410521] using wordTrace_append hprefix tailTrace_5410521
  have hstable : (prefixWord ++ tailWord_5410521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410521).length < 2 ^ (prefixWord ++ tailWord_5410521).sum := by decide
  have hdescent : baseEnd_5410521 < baseStart_5410521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410531 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 1, 6]
def baseStart_5410531 : Nat := 118140960795 + 5410531 * 2 ^ 59
def prefixEnd_5410531 : Nat := 4983230072969 + 3 ^ 40 * 5410531 * 2
def baseEnd_5410531 : Nat := 926067666350492002093309

theorem tailTrace_5410531 : CollatzResearch.WordTrace tailWord_5410531 prefixEnd_5410531 926067666350492002093309 := by
  unfold tailWord_5410531
  simp only [CollatzResearch.WordTrace]
  refine ⟨197338277561577706972919447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131558851707718471315279631 197338277561577706972919447)
  ·
    refine ⟨296007416342366560459379171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197338277561577706972919447 296007416342366560459379171)
    ·
      refine ⟨444011124513549840689068757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296007416342366560459379171 444011124513549840689068757)
      ·
        refine ⟨10406510730786324391150049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 444011124513549840689068757 10406510730786324391150049)
        ·
          refine ⟨7804883048089743293362537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10406510730786324391150049 7804883048089743293362537)
          ·
            refine ⟨5853662286067307470021903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804883048089743293362537 5853662286067307470021903)
            ·
              refine ⟨8780493429100961205032855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853662286067307470021903 8780493429100961205032855)
              ·
                refine ⟨13170740143651441807549283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8780493429100961205032855 13170740143651441807549283)
                ·
                  refine ⟨19756110215477162711323925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13170740143651441807549283 19756110215477162711323925)
                  ·
                    refine ⟨926067666350492002093309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19756110215477162711323925 926067666350492002093309)
                    ·
                      rfl

theorem cell23_5410531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 6].length) (baseStart_5410531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410531 prefixEnd_5410531 := by exact prefixLift 5410531
  have htrace : WordTrace (prefixWord ++ tailWord_5410531) baseStart_5410531 baseEnd_5410531 := by
    simpa [prefixWord, tailWord_5410531, baseEnd_5410531] using wordTrace_append hprefix tailTrace_5410531
  have hstable : (prefixWord ++ tailWord_5410531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410531).length < 2 ^ (prefixWord ++ tailWord_5410531).sum := by decide
  have hdescent : baseEnd_5410531 < baseStart_5410531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410541 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5410541 : Nat := 118140960795 + 5410541 * 2 ^ 59
def prefixEnd_5410541 : Nat := 4983230072969 + 3 ^ 40 * 5410541 * 2
def baseEnd_5410541 : Nat := 2778208133858020967154881

theorem tailTrace_5410541 : CollatzResearch.WordTrace tailWord_5410541 prefixEnd_5410541 2778208133858020967154881 := by
  unfold tailWord_5410541
  simp only [CollatzResearch.WordTrace]
  refine ⟨197338642291541478680783477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131559094861027652453855651 197338642291541478680783477)
  ·
    refine ⟨18500497714832013626323451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197338642291541478680783477 18500497714832013626323451)
    ·
      refine ⟨27750746572248020439485177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18500497714832013626323451 27750746572248020439485177)
      ·
        refine ⟨20813059929186015329613883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27750746572248020439485177 20813059929186015329613883)
        ·
          refine ⟨31219589893779022994420825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20813059929186015329613883 31219589893779022994420825)
          ·
            refine ⟨23414692420334267245815619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31219589893779022994420825 23414692420334267245815619)
            ·
              refine ⟨35122038630501400868723429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23414692420334267245815619 35122038630501400868723429)
              ·
                refine ⟨6585382243219012662885643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35122038630501400868723429 6585382243219012662885643)
                ·
                  refine ⟨9878073364828518994328465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585382243219012662885643 9878073364828518994328465)
                  ·
                    refine ⟨7408555023621389245746349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9878073364828518994328465 7408555023621389245746349)
                    ·
                      refine ⟨2778208133858020967154881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408555023621389245746349 2778208133858020967154881)
                      ·
                        rfl

theorem cell23_5410541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5410541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410541 prefixEnd_5410541 := by exact prefixLift 5410541
  have htrace : WordTrace (prefixWord ++ tailWord_5410541) baseStart_5410541 baseEnd_5410541 := by
    simpa [prefixWord, tailWord_5410541, baseEnd_5410541] using wordTrace_append hprefix tailTrace_5410541
  have hstable : (prefixWord ++ tailWord_5410541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410541).length < 2 ^ (prefixWord ++ tailWord_5410541).sum := by decide
  have hdescent : baseEnd_5410541 < baseStart_5410541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410548 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5410548 : Nat := 118140960795 + 5410548 * 2 ^ 59
def prefixEnd_5410548 : Nat := 4983230072969 + 3 ^ 40 * 5410548 * 2
def baseEnd_5410548 : Nat := 926070576074200813255783

theorem tailTrace_5410548 : CollatzResearch.WordTrace tailWord_5410548 prefixEnd_5410548 926070576074200813255783 := by
  unfold tailWord_5410548
  simp only [CollatzResearch.WordTrace]
  refine ⟨98669448801258059438144149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131559265068344079250858865 98669448801258059438144149)
  ·
    refine ⟨4625130412558971536163007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98669448801258059438144149 4625130412558971536163007)
    ·
      refine ⟨6937695618838457304244511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625130412558971536163007 6937695618838457304244511)
      ·
        refine ⟨10406543428257685956366767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937695618838457304244511 10406543428257685956366767)
        ·
          refine ⟨15609815142386528934550151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10406543428257685956366767 15609815142386528934550151)
          ·
            refine ⟨23414722713579793401825227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15609815142386528934550151 23414722713579793401825227)
            ·
              refine ⟨35122084070369690102737841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23414722713579793401825227 35122084070369690102737841)
              ·
                refine ⟨26341563052777267577053381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35122084070369690102737841 26341563052777267577053381)
                ·
                  refine ⟨4939043072395737670697509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26341563052777267577053381 4939043072395737670697509)
                  ·
                    refine ⟨926070576074200813255783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939043072395737670697509 926070576074200813255783)
                    ·
                      rfl

theorem cell23_5410548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5410548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410548 prefixEnd_5410548 := by exact prefixLift 5410548
  have htrace : WordTrace (prefixWord ++ tailWord_5410548) baseStart_5410548 baseEnd_5410548 := by
    simpa [prefixWord, tailWord_5410548, baseEnd_5410548] using wordTrace_append hprefix tailTrace_5410548
  have hstable : (prefixWord ++ tailWord_5410548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410548).length < 2 ^ (prefixWord ++ tailWord_5410548).sum := by decide
  have hdescent : baseEnd_5410548 < baseStart_5410548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410566 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5410566 : Nat := 118140960795 + 5410566 * 2 ^ 59
def prefixEnd_5410566 : Nat := 4983230072969 + 3 ^ 40 * 5410566 * 2
def baseEnd_5410566 : Nat := 2778220970874383369342267

theorem tailTrace_5410566 : CollatzResearch.WordTrace tailWord_5410566 prefixEnd_5410566 2778220970874383369342267 := by
  unfold tailWord_5410566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166861066139090873451361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131559702744300605300295701 6166861066139090873451361)
  ·
    refine ⟨4625145799604318155088521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6166861066139090873451361 4625145799604318155088521)
    ·
      refine ⟨3468859349703238616316391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4625145799604318155088521 3468859349703238616316391)
      ·
        refine ⟨5203289024554857924474587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468859349703238616316391 5203289024554857924474587)
        ·
          refine ⟨7804933536832286886711881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203289024554857924474587 7804933536832286886711881)
          ·
            refine ⟨5853700152624215165033911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804933536832286886711881 5853700152624215165033911)
            ·
              refine ⟨8780550228936322747550867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853700152624215165033911 8780550228936322747550867)
              ·
                refine ⟨13170825343404484121326301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8780550228936322747550867 13170825343404484121326301)
                ·
                  refine ⟨4939059503776681545497363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13170825343404484121326301 4939059503776681545497363)
                  ·
                    refine ⟨7408589255665022318246045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4939059503776681545497363 7408589255665022318246045)
                    ·
                      refine ⟨2778220970874383369342267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408589255665022318246045 2778220970874383369342267)
                      ·
                        rfl

theorem cell23_5410566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5410566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410566 prefixEnd_5410566 := by exact prefixLift 5410566
  have htrace : WordTrace (prefixWord ++ tailWord_5410566) baseStart_5410566 baseEnd_5410566 := by
    simpa [prefixWord, tailWord_5410566, baseEnd_5410566] using wordTrace_append hprefix tailTrace_5410566
  have hstable : (prefixWord ++ tailWord_5410566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410566).length < 2 ^ (prefixWord ++ tailWord_5410566).sum := by decide
  have hdescent : baseEnd_5410566 < baseStart_5410566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410577 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_5410577 : Nat := 118140960795 + 5410577 * 2 ^ 59
def prefixEnd_5410577 : Nat := 4983230072969 + 3 ^ 40 * 5410577 * 2
def baseEnd_5410577 : Nat := 2778226619161582826304715

theorem tailTrace_5410577 : CollatzResearch.WordTrace tailWord_5410577 prefixEnd_5410577 2778226619161582826304715 := by
  unfold tailWord_5410577
  simp only [CollatzResearch.WordTrace]
  refine ⟨197339955319411056829093985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131559970212940704552729323 197339955319411056829093985)
  ·
    refine ⟨148004966489558292621820489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197339955319411056829093985 148004966489558292621820489)
    ·
      refine ⟨111003724867168719466365367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148004966489558292621820489 111003724867168719466365367)
      ·
        refine ⟨166505587300753079199548051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111003724867168719466365367 166505587300753079199548051)
        ·
          refine ⟨249758380951129618799322077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166505587300753079199548051 249758380951129618799322077)
          ·
            refine ⟨93659392856673607049745779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249758380951129618799322077 93659392856673607049745779)
            ·
              refine ⟨140489089285010410574618669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93659392856673607049745779 140489089285010410574618669)
              ·
                refine ⟨52683408481878903965482001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140489089285010410574618669 52683408481878903965482001)
                ·
                  refine ⟨39512556361409177974111501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52683408481878903965482001 39512556361409177974111501)
                  ·
                    refine ⟨14817208635528441740291813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39512556361409177974111501 14817208635528441740291813)
                    ·
                      refine ⟨2778226619161582826304715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14817208635528441740291813 2778226619161582826304715)
                      ·
                        rfl

theorem cell23_5410577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_5410577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410577 prefixEnd_5410577 := by exact prefixLift 5410577
  have htrace : WordTrace (prefixWord ++ tailWord_5410577) baseStart_5410577 baseEnd_5410577 := by
    simpa [prefixWord, tailWord_5410577, baseEnd_5410577] using wordTrace_append hprefix tailTrace_5410577
  have hstable : (prefixWord ++ tailWord_5410577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410577).length < 2 ^ (prefixWord ++ tailWord_5410577).sum := by decide
  have hdescent : baseEnd_5410577 < baseStart_5410577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410607 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_5410607 : Nat := 118140960795 + 5410607 * 2 ^ 59
def prefixEnd_5410607 : Nat := 4983230072969 + 3 ^ 40 * 5410607 * 2
def baseEnd_5410607 : Nat := 2778242023581217708929577

theorem tailTrace_5410607 : CollatzResearch.WordTrace tailWord_5410607 prefixEnd_5410607 2778242023581217708929577 := by
  unfold tailWord_5410607
  simp only [CollatzResearch.WordTrace]
  refine ⟨197341049509302371952686075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131560699672868247968457383 197341049509302371952686075)
  ·
    refine ⟨296011574263953557929029113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197341049509302371952686075 296011574263953557929029113)
    ·
      refine ⟨222008680697965168446771835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296011574263953557929029113 222008680697965168446771835)
      ·
        refine ⟨333013021046947752670157753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222008680697965168446771835 333013021046947752670157753)
        ·
          refine ⟨249759765785210814502618315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333013021046947752670157753 249759765785210814502618315)
          ·
            refine ⟨374639648677816221753927473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249759765785210814502618315 374639648677816221753927473)
            ·
              refine ⟨280979736508362166315445605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374639648677816221753927473 280979736508362166315445605)
              ·
                refine ⟨52683700595317906184146051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280979736508362166315445605 52683700595317906184146051)
                ·
                  refine ⟨79025550892976859276219077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52683700595317906184146051 79025550892976859276219077)
                  ·
                    refine ⟨14817290792433161114291077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79025550892976859276219077 14817290792433161114291077)
                    ·
                      refine ⟨2778242023581217708929577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14817290792433161114291077 2778242023581217708929577)
                      ·
                        rfl

theorem cell23_5410607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_5410607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410607 prefixEnd_5410607 := by exact prefixLift 5410607
  have htrace : WordTrace (prefixWord ++ tailWord_5410607) baseStart_5410607 baseEnd_5410607 := by
    simpa [prefixWord, tailWord_5410607, baseEnd_5410607] using wordTrace_append hprefix tailTrace_5410607
  have hstable : (prefixWord ++ tailWord_5410607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410607).length < 2 ^ (prefixWord ++ tailWord_5410607).sum := by decide
  have hdescent : baseEnd_5410607 < baseStart_5410607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410664 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5410664 : Nat := 118140960795 + 5410664 * 2 ^ 59
def prefixEnd_5410664 : Nat := 4983230072969 + 3 ^ 40 * 5410664 * 2
def baseEnd_5410664 : Nat := 926090430659507995305605

theorem tailTrace_5410664 : CollatzResearch.WordTrace tailWord_5410664 prefixEnd_5410664 926090430659507995305605 := by
  unfold tailWord_5410664
  simp only [CollatzResearch.WordTrace]
  refine ⟨98671564235047935343755523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131562085646730580458340697 98671564235047935343755523)
  ·
    refine ⟨148007346352571903015633285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98671564235047935343755523 148007346352571903015633285)
    ·
      refine ⟨27751377441107231815431241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148007346352571903015633285 27751377441107231815431241)
      ·
        refine ⟨20813533080830423861573431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27751377441107231815431241 20813533080830423861573431)
        ·
          refine ⟨31220299621245635792360147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20813533080830423861573431 31220299621245635792360147)
          ·
            refine ⟨46830449431868453688540221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31220299621245635792360147 46830449431868453688540221)
            ·
              refine ⟨17561418536950670133202583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46830449431868453688540221 17561418536950670133202583)
              ·
                refine ⟨26342127805426005199803875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17561418536950670133202583 26342127805426005199803875)
                ·
                  refine ⟨39513191708139007799705813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26342127805426005199803875 39513191708139007799705813)
                  ·
                    refine ⟨926090430659507995305605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39513191708139007799705813 926090430659507995305605)
                    ·
                      rfl

theorem cell23_5410664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5410664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410664 prefixEnd_5410664 := by exact prefixLift 5410664
  have htrace : WordTrace (prefixWord ++ tailWord_5410664) baseStart_5410664 baseEnd_5410664 := by
    simpa [prefixWord, tailWord_5410664, baseEnd_5410664] using wordTrace_append hprefix tailTrace_5410664
  have hstable : (prefixWord ++ tailWord_5410664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410664).length < 2 ^ (prefixWord ++ tailWord_5410664).sum := by decide
  have hdescent : baseEnd_5410664 < baseStart_5410664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410704 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_5410704 : Nat := 118140960795 + 5410704 * 2 ^ 59
def prefixEnd_5410704 : Nat := 4983230072969 + 3 ^ 40 * 5410704 * 2
def baseEnd_5410704 : Nat := 2778291831204703829416631

theorem tailTrace_5410704 : CollatzResearch.WordTrace tailWord_5410704 prefixEnd_5410704 2778291831204703829416631 := by
  unfold tailWord_5410704
  simp only [CollatzResearch.WordTrace]
  refine ⟨98672293694975478759483583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131563058259967305012644777 98672293694975478759483583)
  ·
    refine ⟨148008440542463218139225375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98672293694975478759483583 148008440542463218139225375)
    ·
      refine ⟨222012660813694827208838063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148008440542463218139225375 222012660813694827208838063)
      ·
        refine ⟨333018991220542240813257095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222012660813694827208838063 333018991220542240813257095)
        ·
          refine ⟨499528486830813361219885643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333018991220542240813257095 499528486830813361219885643)
          ·
            refine ⟨749292730246220041829828465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499528486830813361219885643 749292730246220041829828465)
            ·
              refine ⟨561969547684665031372371349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749292730246220041829828465 561969547684665031372371349)
              ·
                refine ⟨26342322547718673345579907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 561969547684665031372371349 26342322547718673345579907)
                ·
                  refine ⟨39513483821578010018369861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26342322547718673345579907 39513483821578010018369861)
                  ·
                    refine ⟨7408778216545876878444349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39513483821578010018369861 7408778216545876878444349)
                    ·
                      refine ⟨2778291831204703829416631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408778216545876878444349 2778291831204703829416631)
                      ·
                        rfl

theorem cell23_5410704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_5410704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410704 prefixEnd_5410704 := by exact prefixLift 5410704
  have htrace : WordTrace (prefixWord ++ tailWord_5410704) baseStart_5410704 baseEnd_5410704 := by
    simpa [prefixWord, tailWord_5410704, baseEnd_5410704] using wordTrace_append hprefix tailTrace_5410704
  have hstable : (prefixWord ++ tailWord_5410704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410704).length < 2 ^ (prefixWord ++ tailWord_5410704).sum := by decide
  have hdescent : baseEnd_5410704 < baseStart_5410704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410711 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 3, 4]
def baseStart_5410711 : Nat := 118140960795 + 5410711 * 2 ^ 59
def prefixEnd_5410711 : Nat := 4983230072969 + 3 ^ 40 * 5410711 * 2
def baseEnd_5410711 : Nat := 926098475189761767343033

theorem tailTrace_5410711 : CollatzResearch.WordTrace tailWord_5410711 prefixEnd_5410711 926098475189761767343033 := by
  unfold tailWord_5410711
  simp only [CollatzResearch.WordTrace]
  refine ⟨197344842700925597714471987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131563228467283731809647991 197344842700925597714471987)
  ·
    refine ⟨296017264051388396571707981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197344842700925597714471987 296017264051388396571707981)
    ·
      refine ⟨111006474019270648714390493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296017264051388396571707981 111006474019270648714390493)
      ·
        refine ⟨41627427757226493267896435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111006474019270648714390493 41627427757226493267896435)
        ·
          refine ⟨62441141635839739901844653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41627427757226493267896435 62441141635839739901844653)
          ·
            refine ⟨23415428113439902463191745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62441141635839739901844653 23415428113439902463191745)
            ·
              refine ⟨17561571085079926847393809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23415428113439902463191745 17561571085079926847393809)
              ·
                refine ⟨13171178313809945135545357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17561571085079926847393809 13171178313809945135545357)
                ·
                  refine ⟨4939191867678729425829509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13171178313809945135545357 4939191867678729425829509)
                  ·
                    refine ⟨926098475189761767343033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939191867678729425829509 926098475189761767343033)
                    ·
                      rfl

theorem cell23_5410711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_5410711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410711 prefixEnd_5410711 := by exact prefixLift 5410711
  have htrace : WordTrace (prefixWord ++ tailWord_5410711) baseStart_5410711 baseEnd_5410711 := by
    simpa [prefixWord, tailWord_5410711, baseEnd_5410711] using wordTrace_append hprefix tailTrace_5410711
  have hstable : (prefixWord ++ tailWord_5410711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410711).length < 2 ^ (prefixWord ++ tailWord_5410711).sum := by decide
  have hdescent : baseEnd_5410711 < baseStart_5410711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410724 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 8]
def baseStart_5410724 : Nat := 118140960795 + 5410724 * 2 ^ 59
def prefixEnd_5410724 : Nat := 4983230072969 + 3 ^ 40 * 5410724 * 2
def baseEnd_5410724 : Nat := 308700233424199305685171

theorem tailTrace_5410724 : CollatzResearch.WordTrace tailWord_5410724 prefixEnd_5410724 308700233424199305685171 := by
  unfold tailWord_5410724
  simp only [CollatzResearch.WordTrace]
  refine ⟨98672658424939250467347613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131563544566585667289796817 98672658424939250467347613)
  ·
    refine ⟨37002246909352218925255355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98672658424939250467347613 37002246909352218925255355)
    ·
      refine ⟨55503370364028328387883033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37002246909352218925255355 55503370364028328387883033)
      ·
        refine ⟨41627527773021246290912275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55503370364028328387883033 41627527773021246290912275)
        ·
          refine ⟨62441291659531869436368413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41627527773021246290912275 62441291659531869436368413)
          ·
            refine ⟨23415484372324451038638155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62441291659531869436368413 23415484372324451038638155)
            ·
              refine ⟨35123226558486676557957233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23415484372324451038638155 35123226558486676557957233)
              ·
                refine ⟨26342419918865007418467925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35123226558486676557957233 26342419918865007418467925)
                ·
                  refine ⟨308700233424199305685171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26342419918865007418467925 308700233424199305685171)
                  ·
                    rfl

theorem cell23_5410724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_5410724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410724 prefixEnd_5410724 := by exact prefixLift 5410724
  have htrace : WordTrace (prefixWord ++ tailWord_5410724) baseStart_5410724 baseEnd_5410724 := by
    simpa [prefixWord, tailWord_5410724, baseEnd_5410724] using wordTrace_append hprefix tailTrace_5410724
  have hstable : (prefixWord ++ tailWord_5410724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410724).length < 2 ^ (prefixWord ++ tailWord_5410724).sum := by decide
  have hdescent : baseEnd_5410724 < baseStart_5410724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410745 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 1, 4]
def baseStart_5410745 : Nat := 118140960795 + 5410745 * 2 ^ 59
def prefixEnd_5410745 : Nat := 4983230072969 + 3 ^ 40 * 5410745 * 2
def baseEnd_5410745 : Nat := 926104294637179389667981

theorem tailTrace_5410745 : CollatzResearch.WordTrace tailWord_5410745 prefixEnd_5410745 926104294637179389667981 := by
  unfold tailWord_5410745
  simp only [CollatzResearch.WordTrace]
  refine ⟨197346082782802421521209689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131564055188534947680806459 197346082782802421521209689)
  ·
    refine ⟨148009562087101816140907267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197346082782802421521209689 148009562087101816140907267)
    ·
      refine ⟨222014343130652724211360901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148009562087101816140907267 222014343130652724211360901)
      ·
        refine ⟨41627689336997385789630169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222014343130652724211360901 41627689336997385789630169)
        ·
          refine ⟨31220767002748039342222627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41627689336997385789630169 31220767002748039342222627)
          ·
            refine ⟨46831150504122059013333941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31220767002748039342222627 46831150504122059013333941)
            ·
              refine ⟨4390420359761443032500057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46831150504122059013333941 4390420359761443032500057)
              ·
                refine ⟨3292815269821082274375043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4390420359761443032500057 3292815269821082274375043)
                ·
                  refine ⟨4939222904731623411562565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292815269821082274375043 4939222904731623411562565)
                  ·
                    refine ⟨926104294637179389667981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939222904731623411562565 926104294637179389667981)
                    ·
                      rfl

theorem cell23_5410745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 4].length) (baseStart_5410745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410745 prefixEnd_5410745 := by exact prefixLift 5410745
  have htrace : WordTrace (prefixWord ++ tailWord_5410745) baseStart_5410745 baseEnd_5410745 := by
    simpa [prefixWord, tailWord_5410745, baseEnd_5410745] using wordTrace_append hprefix tailTrace_5410745
  have hstable : (prefixWord ++ tailWord_5410745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410745).length < 2 ^ (prefixWord ++ tailWord_5410745).sum := by decide
  have hdescent : baseEnd_5410745 < baseStart_5410745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410788 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_5410788 : Nat := 118140960795 + 5410788 * 2 ^ 59
def prefixEnd_5410788 : Nat := 4983230072969 + 3 ^ 40 * 5410788 * 2
def baseEnd_5410788 : Nat := 926111654526560500255415

theorem tailTrace_5410788 : CollatzResearch.WordTrace tailWord_5410788 prefixEnd_5410788 926111654526560500255415 := by
  unfold tailWord_5410788
  simp only [CollatzResearch.WordTrace]
  refine ⟨98673825560823319932512509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131565100747764426576683345 98673825560823319932512509)
  ·
    refine ⟨37002684585308744974692191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98673825560823319932512509 37002684585308744974692191)
    ·
      refine ⟨55504026877963117462038287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37002684585308744974692191 55504026877963117462038287)
      ·
        refine ⟨83256040316944676193057431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55504026877963117462038287 83256040316944676193057431)
        ·
          refine ⟨124884060475417014289586147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83256040316944676193057431 124884060475417014289586147)
          ·
            refine ⟨187326090713125521434379221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124884060475417014289586147 187326090713125521434379221)
            ·
              refine ⟨4390455251088879408618263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 187326090713125521434379221 4390455251088879408618263)
              ·
                refine ⟨6585682876633319112927395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390455251088879408618263 6585682876633319112927395)
                ·
                  refine ⟨9878524314949978669391093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585682876633319112927395 9878524314949978669391093)
                  ·
                    refine ⟨926111654526560500255415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9878524314949978669391093 926111654526560500255415)
                    ·
                      rfl

theorem cell23_5410788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_5410788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410788 prefixEnd_5410788 := by exact prefixLift 5410788
  have htrace : WordTrace (prefixWord ++ tailWord_5410788) baseStart_5410788 baseEnd_5410788 := by
    simpa [prefixWord, tailWord_5410788, baseEnd_5410788] using wordTrace_append hprefix tailTrace_5410788
  have hstable : (prefixWord ++ tailWord_5410788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410788).length < 2 ^ (prefixWord ++ tailWord_5410788).sum := by decide
  have hdescent : baseEnd_5410788 < baseStart_5410788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410811 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 3]
def baseStart_5410811 : Nat := 118140960795 + 5410811 * 2 ^ 59
def prefixEnd_5410811 : Nat := 4983230072969 + 3 ^ 40 * 5410811 * 2
def baseEnd_5410811 : Nat := 2778346773634734910778639

theorem tailTrace_5410811 : CollatzResearch.WordTrace tailWord_5410811 prefixEnd_5410811 2778346773634734910778639 := by
  unfold tailWord_5410811
  simp only [CollatzResearch.WordTrace]
  refine ⟨197348490000563314793112287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131565660000375543195408191 197348490000563314793112287)
  ·
    refine ⟨296022735000844972189668431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197348490000563314793112287 296022735000844972189668431)
    ·
      refine ⟨444034102501267458284502647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296022735000844972189668431 444034102501267458284502647)
      ·
        refine ⟨666051153751901187426753971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444034102501267458284502647 666051153751901187426753971)
        ·
          refine ⟨999076730627851781140130957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666051153751901187426753971 999076730627851781140130957)
          ·
            refine ⟨374653773985444417927549109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 999076730627851781140130957 374653773985444417927549109)
            ·
              refine ⟨35123791311135414180707729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 374653773985444417927549109 35123791311135414180707729)
              ·
                refine ⟨26342843483351560635530797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35123791311135414180707729 26342843483351560635530797)
                ·
                  refine ⟨9878566306256835238324049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26342843483351560635530797 9878566306256835238324049)
                  ·
                    refine ⟨7408924729692626428743037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9878566306256835238324049 7408924729692626428743037)
                    ·
                      refine ⟨2778346773634734910778639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408924729692626428743037 2778346773634734910778639)
                      ·
                        rfl

theorem cell23_5410811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 3].length) (baseStart_5410811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410811 prefixEnd_5410811 := by exact prefixLift 5410811
  have htrace : WordTrace (prefixWord ++ tailWord_5410811) baseStart_5410811 baseEnd_5410811 := by
    simpa [prefixWord, tailWord_5410811, baseEnd_5410811] using wordTrace_append hprefix tailTrace_5410811
  have hstable : (prefixWord ++ tailWord_5410811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410811).length < 2 ^ (prefixWord ++ tailWord_5410811).sum := by decide
  have hdescent : baseEnd_5410811 < baseStart_5410811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410821 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_5410821 : Nat := 118140960795 + 5410821 * 2 ^ 59
def prefixEnd_5410821 : Nat := 4983230072969 + 3 ^ 40 * 5410821 * 2
def baseEnd_5410821 : Nat := 2778351908441279871653593

theorem tailTrace_5410821 : CollatzResearch.WordTrace tailWord_5410821 prefixEnd_5410821 2778351908441279871653593 := by
  unfold tailWord_5410821
  simp only [CollatzResearch.WordTrace]
  refine ⟨197348854730527086500976317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131565903153684724333984211 197348854730527086500976317)
  ·
    refine ⟨74005820523947657437866119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197348854730527086500976317 74005820523947657437866119)
    ·
      refine ⟨111008730785921486156799179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74005820523947657437866119 111008730785921486156799179)
      ·
        refine ⟨166513096178882229235198769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111008730785921486156799179 166513096178882229235198769)
        ·
          refine ⟨124884822134161671926399077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166513096178882229235198769 124884822134161671926399077)
          ·
            refine ⟨23415904150155313486199827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124884822134161671926399077 23415904150155313486199827)
            ·
              refine ⟨35123856225232970229299741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23415904150155313486199827 35123856225232970229299741)
              ·
                refine ⟨13171446084462363835987403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35123856225232970229299741 13171446084462363835987403)
                ·
                  refine ⟨19757169126693545753981105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13171446084462363835987403 19757169126693545753981105)
                  ·
                    refine ⟨14817876845020159315485829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19757169126693545753981105 14817876845020159315485829)
                    ·
                      refine ⟨2778351908441279871653593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14817876845020159315485829 2778351908441279871653593)
                      ·
                        rfl

theorem cell23_5410821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_5410821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410821 prefixEnd_5410821 := by exact prefixLift 5410821
  have htrace : WordTrace (prefixWord ++ tailWord_5410821) baseStart_5410821 baseEnd_5410821 := by
    simpa [prefixWord, tailWord_5410821, baseEnd_5410821] using wordTrace_append hprefix tailTrace_5410821
  have hstable : (prefixWord ++ tailWord_5410821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410821).length < 2 ^ (prefixWord ++ tailWord_5410821).sum := by decide
  have hdescent : baseEnd_5410821 < baseStart_5410821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410828 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_5410828 : Nat := 118140960795 + 5410828 * 2 ^ 59
def prefixEnd_5410828 : Nat := 4983230072969 + 3 ^ 40 * 5410828 * 2
def baseEnd_5410828 : Nat := 2778355502805861344266061

theorem tailTrace_5410828 : CollatzResearch.WordTrace tailWord_5410828 prefixEnd_5410828 2778355502805861344266061 := by
  unfold tailWord_5410828
  simp only [CollatzResearch.WordTrace]
  refine ⟨98674555020750863348240569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131566073361001151130987425 98674555020750863348240569)
  ·
    refine ⟨74005916265563147511180427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98674555020750863348240569 74005916265563147511180427)
    ·
      refine ⟨111008874398344721266770641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74005916265563147511180427 111008874398344721266770641)
      ·
        refine ⟨83256655798758540950077981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111008874398344721266770641 83256655798758540950077981)
        ·
          refine ⟨31221245924534452856279243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83256655798758540950077981 31221245924534452856279243)
          ·
            refine ⟨46831868886801679284418865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31221245924534452856279243 46831868886801679284418865)
            ·
              refine ⟨35123901665101259463314149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46831868886801679284418865 35123901665101259463314149)
              ·
                refine ⟨6585731562206486149371403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35123901665101259463314149 6585731562206486149371403)
                ·
                  refine ⟨9878597343309729224057105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585731562206486149371403 9878597343309729224057105)
                  ·
                    refine ⟨7408948007482296918042829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9878597343309729224057105 7408948007482296918042829)
                    ·
                      refine ⟨2778355502805861344266061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408948007482296918042829 2778355502805861344266061)
                      ·
                        rfl

theorem cell23_5410828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_5410828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410828 prefixEnd_5410828 := by exact prefixLift 5410828
  have htrace : WordTrace (prefixWord ++ tailWord_5410828) baseStart_5410828 baseEnd_5410828 := by
    simpa [prefixWord, tailWord_5410828, baseEnd_5410828] using wordTrace_append hprefix tailTrace_5410828
  have hstable : (prefixWord ++ tailWord_5410828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410828).length < 2 ^ (prefixWord ++ tailWord_5410828).sum := by decide
  have hdescent : baseEnd_5410828 < baseStart_5410828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410829 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5410829 : Nat := 118140960795 + 5410829 * 2 ^ 59
def prefixEnd_5410829 : Nat := 4983230072969 + 3 ^ 40 * 5410829 * 2
def baseEnd_5410829 : Nat := 2778356016286515840353557

theorem tailTrace_5410829 : CollatzResearch.WordTrace tailWord_5410829 prefixEnd_5410829 2778356016286515840353557 := by
  unfold tailWord_5410829
  simp only [CollatzResearch.WordTrace]
  refine ⟨197349146514498103867267541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131566097676332069244845027 197349146514498103867267541)
  ·
    refine ⟨4625370621433549309389083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 197349146514498103867267541 4625370621433549309389083)
    ·
      refine ⟨6938055932150323964083625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625370621433549309389083 6938055932150323964083625)
      ·
        refine ⟨5203541949112742973062719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6938055932150323964083625 5203541949112742973062719)
        ·
          refine ⟨7805312923669114459594079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203541949112742973062719 7805312923669114459594079)
          ·
            refine ⟨11707969385503671689391119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805312923669114459594079 11707969385503671689391119)
            ·
              refine ⟨17561954078255507534086679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11707969385503671689391119 17561954078255507534086679)
              ·
                refine ⟨26342931117383261301130019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17561954078255507534086679 26342931117383261301130019)
                ·
                  refine ⟨39514396676074891951695029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26342931117383261301130019 39514396676074891951695029)
                  ·
                    refine ⟨3704474688382021120471409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39514396676074891951695029 3704474688382021120471409)
                    ·
                      refine ⟨2778356016286515840353557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704474688382021120471409 2778356016286515840353557)
                      ·
                        rfl

theorem cell23_5410829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5410829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410829 prefixEnd_5410829 := by exact prefixLift 5410829
  have htrace : WordTrace (prefixWord ++ tailWord_5410829) baseStart_5410829 baseEnd_5410829 := by
    simpa [prefixWord, tailWord_5410829, baseEnd_5410829] using wordTrace_append hprefix tailTrace_5410829
  have hstable : (prefixWord ++ tailWord_5410829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410829).length < 2 ^ (prefixWord ++ tailWord_5410829).sum := by decide
  have hdescent : baseEnd_5410829 < baseStart_5410829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410836 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5410836 : Nat := 118140960795 + 5410836 * 2 ^ 59
def prefixEnd_5410836 : Nat := 4983230072969 + 3 ^ 40 * 5410836 * 2
def baseEnd_5410836 : Nat := 2778359610651097312966025

theorem tailTrace_5410836 : CollatzResearch.WordTrace tailWord_5410836 prefixEnd_5410836 2778359610651097312966025 := by
  unfold tailWord_5410836
  simp only [CollatzResearch.WordTrace]
  refine ⟨98674700912736372031386181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131566267883648496041848241 98674700912736372031386181)
  ·
    refine ⟨18501506421138069755884909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98674700912736372031386181 18501506421138069755884909)
    ·
      refine ⟨6938064907926776158456841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18501506421138069755884909 6938064907926776158456841)
      ·
        refine ⟨5203548680945082118842631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6938064907926776158456841 5203548680945082118842631)
        ·
          refine ⟨7805323021417623178263947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203548680945082118842631 7805323021417623178263947)
          ·
            refine ⟨11707984532126434767395921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805323021417623178263947 11707984532126434767395921)
            ·
              refine ⟨8780988399094826075546941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11707984532126434767395921 8780988399094826075546941)
              ·
                refine ⟨3292870649660559778330103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8780988399094826075546941 3292870649660559778330103)
                ·
                  refine ⟨4939305974490839667495155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292870649660559778330103 4939305974490839667495155)
                  ·
                    refine ⟨7408958961736259501242733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4939305974490839667495155 7408958961736259501242733)
                    ·
                      refine ⟨2778359610651097312966025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408958961736259501242733 2778359610651097312966025)
                      ·
                        rfl

theorem cell23_5410836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5410836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410836 prefixEnd_5410836 := by exact prefixLift 5410836
  have htrace : WordTrace (prefixWord ++ tailWord_5410836) baseStart_5410836 baseEnd_5410836 := by
    simpa [prefixWord, tailWord_5410836, baseEnd_5410836] using wordTrace_append hprefix tailTrace_5410836
  have hstable : (prefixWord ++ tailWord_5410836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410836).length < 2 ^ (prefixWord ++ tailWord_5410836).sum := by decide
  have hdescent : baseEnd_5410836 < baseStart_5410836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410842 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2]
def baseStart_5410842 : Nat := 118140960795 + 5410842 * 2 ^ 59
def prefixEnd_5410842 : Nat := 4983230072969 + 3 ^ 40 * 5410842 * 2
def baseEnd_5410842 : Nat := 2778362691535024289490997

theorem tailTrace_5410842 : CollatzResearch.WordTrace tailWord_5410842 prefixEnd_5410842 2778362691535024289490997 := by
  unfold tailWord_5410842
  simp only [CollatzResearch.WordTrace]
  refine ⟨49337405165862751771872695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131566413775634004724993853 49337405165862751771872695)
  ·
    refine ⟨74006107748794127657809043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49337405165862751771872695 74006107748794127657809043)
    ·
      refine ⟨111009161623191191486713565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74006107748794127657809043 111009161623191191486713565)
      ·
        refine ⟨41628435608696696807517587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111009161623191191486713565 41628435608696696807517587)
        ·
          refine ⟨62442653413045045211276381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41628435608696696807517587 62442653413045045211276381)
          ·
            refine ⟨23415995029891891954228643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62442653413045045211276381 23415995029891891954228643)
            ·
              refine ⟨35123992544837837931342965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23415995029891891954228643 35123992544837837931342965)
              ·
                refine ⟨3292874301078547306063403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35123992544837837931342965 3292874301078547306063403)
                ·
                  refine ⟨4939311451617820959095105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292874301078547306063403 4939311451617820959095105)
                  ·
                    refine ⟨3704483588713365719321329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939311451617820959095105 3704483588713365719321329)
                    ·
                      refine ⟨2778362691535024289490997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704483588713365719321329 2778362691535024289490997)
                      ·
                        rfl

theorem cell23_5410842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_5410842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410842 prefixEnd_5410842 := by exact prefixLift 5410842
  have htrace : WordTrace (prefixWord ++ tailWord_5410842) baseStart_5410842 baseEnd_5410842 := by
    simpa [prefixWord, tailWord_5410842, baseEnd_5410842] using wordTrace_append hprefix tailTrace_5410842
  have hstable : (prefixWord ++ tailWord_5410842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410842).length < 2 ^ (prefixWord ++ tailWord_5410842).sum := by decide
  have hdescent : baseEnd_5410842 < baseStart_5410842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410845 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_5410845 : Nat := 118140960795 + 5410845 * 2 ^ 59
def prefixEnd_5410845 : Nat := 4983230072969 + 3 ^ 40 * 5410845 * 2
def baseEnd_5410845 : Nat := 2778364231976987777753483

theorem tailTrace_5410845 : CollatzResearch.WordTrace tailWord_5410845 prefixEnd_5410845 2778364231976987777753483 := by
  unfold tailWord_5410845
  simp only [CollatzResearch.WordTrace]
  refine ⟨197349730082440138599849989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131566486721626759066566659 197349730082440138599849989)
  ·
    refine ⟨37003074390457525987471873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197349730082440138599849989 37003074390457525987471873)
    ·
      refine ⟨27752305792843144490603905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37003074390457525987471873 27752305792843144490603905)
      ·
        refine ⟨20814229344632358367952929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27752305792843144490603905 20814229344632358367952929)
        ·
          refine ⟨15610672008474268775964697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20814229344632358367952929 15610672008474268775964697)
          ·
            refine ⟨11708004006355701581973523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15610672008474268775964697 11708004006355701581973523)
            ·
              refine ⟨17562006009533552372960285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11708004006355701581973523 17562006009533552372960285)
              ·
                refine ⟨6585752253575082139860107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17562006009533552372960285 6585752253575082139860107)
                ·
                  refine ⟨9878628380362623209790161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585752253575082139860107 9878628380362623209790161)
                  ·
                    refine ⟨7408971285271967407342621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9878628380362623209790161 7408971285271967407342621)
                    ·
                      refine ⟨2778364231976987777753483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7408971285271967407342621 2778364231976987777753483)
                      ·
                        rfl

theorem cell23_5410845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_5410845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410845 prefixEnd_5410845 := by exact prefixLift 5410845
  have htrace : WordTrace (prefixWord ++ tailWord_5410845) baseStart_5410845 baseEnd_5410845 := by
    simpa [prefixWord, tailWord_5410845, baseEnd_5410845] using wordTrace_append hprefix tailTrace_5410845
  have hstable : (prefixWord ++ tailWord_5410845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410845).length < 2 ^ (prefixWord ++ tailWord_5410845).sum := by decide
  have hdescent : baseEnd_5410845 < baseStart_5410845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410852 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_5410852 : Nat := 118140960795 + 5410852 * 2 ^ 59
def prefixEnd_5410852 : Nat := 4983230072969 + 3 ^ 40 * 5410852 * 2
def baseEnd_5410852 : Nat := 926122608780523083455317

theorem tailTrace_5410852 : CollatzResearch.WordTrace tailWord_5410852 prefixEnd_5410852 926122608780523083455317 := by
  unfold tailWord_5410852
  simp only [CollatzResearch.WordTrace]
  refine ⟨98674992696707389397677405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131566656928943185863569873 98674992696707389397677405)
  ·
    refine ⟨37003122261265271024129027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98674992696707389397677405 37003122261265271024129027)
    ·
      refine ⟨55504683391897906536193541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37003122261265271024129027 55504683391897906536193541)
      ·
        refine ⟨10407128135980857475536289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55504683391897906536193541 10407128135980857475536289)
        ·
          refine ⟨7805346101985643106652217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10407128135980857475536289 7805346101985643106652217)
          ·
            refine ⟨5854009576489232329989163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7805346101985643106652217 5854009576489232329989163)
            ·
              refine ⟨8781014364733848494983745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854009576489232329989163 8781014364733848494983745)
              ·
                refine ⟨6585760773550386371237809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8781014364733848494983745 6585760773550386371237809)
                ·
                  refine ⟨4939320580162789778428357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6585760773550386371237809 4939320580162789778428357)
                  ·
                    refine ⟨926122608780523083455317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939320580162789778428357 926122608780523083455317)
                    ·
                      rfl

theorem cell23_5410852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_5410852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410852 prefixEnd_5410852 := by exact prefixLift 5410852
  have htrace : WordTrace (prefixWord ++ tailWord_5410852) baseStart_5410852 baseEnd_5410852 := by
    simpa [prefixWord, tailWord_5410852, baseEnd_5410852] using wordTrace_append hprefix tailTrace_5410852
  have hstable : (prefixWord ++ tailWord_5410852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410852).length < 2 ^ (prefixWord ++ tailWord_5410852).sum := by decide
  have hdescent : baseEnd_5410852 < baseStart_5410852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410901 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5410901 : Nat := 118140960795 + 5410901 * 2 ^ 59
def prefixEnd_5410901 : Nat := 4983230072969 + 3 ^ 40 * 5410901 * 2
def baseEnd_5410901 : Nat := 2778392986893639558653225

theorem tailTrace_5410901 : CollatzResearch.WordTrace tailWord_5410901 prefixEnd_5410901 2778392986893639558653225 := by
  unfold tailWord_5410901
  simp only [CollatzResearch.WordTrace]
  refine ⟨197351772570237260163888557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131567848380158173442592371 197351772570237260163888557)
  ·
    refine ⟨74006914713838972561458209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197351772570237260163888557 74006914713838972561458209)
    ·
      refine ⟨55505186035379229421093657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74006914713838972561458209 55505186035379229421093657)
      ·
        refine ⟨41628889526534422065820243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55505186035379229421093657 41628889526534422065820243)
        ·
          refine ⟨62443334289801633098730365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41628889526534422065820243 62443334289801633098730365)
          ·
            refine ⟨23416250358675612412023887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62443334289801633098730365 23416250358675612412023887)
            ·
              refine ⟨35124375538013418618035831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23416250358675612412023887 35124375538013418618035831)
              ·
                refine ⟨52686563307020127927053747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35124375538013418618035831 52686563307020127927053747)
                ·
                  refine ⟨79029844960530191890580621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52686563307020127927053747 79029844960530191890580621)
                  ·
                    refine ⟨29636191860198821958967733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79029844960530191890580621 29636191860198821958967733)
                    ·
                      refine ⟨2778392986893639558653225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29636191860198821958967733 2778392986893639558653225)
                      ·
                        rfl

theorem cell23_5410901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5410901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410901 prefixEnd_5410901 := by exact prefixLift 5410901
  have htrace : WordTrace (prefixWord ++ tailWord_5410901) baseStart_5410901 baseEnd_5410901 := by
    simpa [prefixWord, tailWord_5410901, baseEnd_5410901] using wordTrace_append hprefix tailTrace_5410901
  have hstable : (prefixWord ++ tailWord_5410901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410901).length < 2 ^ (prefixWord ++ tailWord_5410901).sum := by decide
  have hdescent : baseEnd_5410901 < baseStart_5410901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410910 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5410910 : Nat := 118140960795 + 5410910 * 2 ^ 59
def prefixEnd_5410910 : Nat := 4983230072969 + 3 ^ 40 * 5410910 * 2
def baseEnd_5410910 : Nat := 2778397608219530023440685

theorem tailTrace_5410910 : CollatzResearch.WordTrace tailWord_5410910 prefixEnd_5410910 2778397608219530023440685 := by
  unfold tailWord_5410910
  simp only [CollatzResearch.WordTrace]
  refine ⟨24669012603400581837620773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131568067218136436467310789 24669012603400581837620773)
  ·
    refine ⟨4625439863137609094553895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24669012603400581837620773 4625439863137609094553895)
    ·
      refine ⟨6938159794706413641830843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625439863137609094553895 6938159794706413641830843)
      ·
        refine ⟨10407239692059620462746265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6938159794706413641830843 10407239692059620462746265)
        ·
          refine ⟨7805429769044715347059699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10407239692059620462746265 7805429769044715347059699)
          ·
            refine ⟨11708144653567073020589549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805429769044715347059699 11708144653567073020589549)
            ·
              refine ⟨4390554245087652382721081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11708144653567073020589549 4390554245087652382721081)
              ·
                refine ⟨3292915683815739287040811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4390554245087652382721081 3292915683815739287040811)
                ·
                  refine ⟨4939373525723608930561217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292915683815739287040811 4939373525723608930561217)
                  ·
                    refine ⟨3704530144292706697920913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939373525723608930561217 3704530144292706697920913)
                    ·
                      refine ⟨2778397608219530023440685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704530144292706697920913 2778397608219530023440685)
                      ·
                        rfl

theorem cell23_5410910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5410910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410910 prefixEnd_5410910 := by exact prefixLift 5410910
  have htrace : WordTrace (prefixWord ++ tailWord_5410910) baseStart_5410910 baseEnd_5410910 := by
    simpa [prefixWord, tailWord_5410910, baseEnd_5410910] using wordTrace_append hprefix tailTrace_5410910
  have hstable : (prefixWord ++ tailWord_5410910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410910).length < 2 ^ (prefixWord ++ tailWord_5410910).sum := by decide
  have hdescent : baseEnd_5410910 < baseStart_5410910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410911 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_5410911 : Nat := 118140960795 + 5410911 * 2 ^ 59
def prefixEnd_5410911 : Nat := 4983230072969 + 3 ^ 40 * 5410911 * 2
def baseEnd_5410911 : Nat := 2778398121700184519528179

theorem tailTrace_5410911 : CollatzResearch.WordTrace tailWord_5410911 prefixEnd_5410911 2778398121700184519528179 := by
  unfold tailWord_5410911
  simp only [CollatzResearch.WordTrace]
  refine ⟨197352137300201031871752587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131568091533467354581168391 197352137300201031871752587)
  ·
    refine ⟨296028205950301547807628881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197352137300201031871752587 296028205950301547807628881)
    ·
      refine ⟨222021154462726160855721661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296028205950301547807628881 222021154462726160855721661)
      ·
        refine ⟨83257932923522310320895623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222021154462726160855721661 83257932923522310320895623)
        ·
          refine ⟨124886899385283465481343435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83257932923522310320895623 124886899385283465481343435)
          ·
            refine ⟨187330349077925198222015153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124886899385283465481343435 187330349077925198222015153)
            ·
              refine ⟨140497761808443898666511365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187330349077925198222015153 140497761808443898666511365)
              ·
                refine ⟨26343330339083230999970881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140497761808443898666511365 26343330339083230999970881)
                ·
                  refine ⟨19757497754312423249978161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26343330339083230999970881 19757497754312423249978161)
                  ·
                    refine ⟨14818123315734317437483621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19757497754312423249978161 14818123315734317437483621)
                    ·
                      refine ⟨2778398121700184519528179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14818123315734317437483621 2778398121700184519528179)
                      ·
                        rfl

theorem cell23_5410911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_5410911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410911 prefixEnd_5410911 := by exact prefixLift 5410911
  have htrace : WordTrace (prefixWord ++ tailWord_5410911) baseStart_5410911 baseEnd_5410911 := by
    simpa [prefixWord, tailWord_5410911, baseEnd_5410911] using wordTrace_append hprefix tailTrace_5410911
  have hstable : (prefixWord ++ tailWord_5410911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410911).length < 2 ^ (prefixWord ++ tailWord_5410911).sum := by decide
  have hdescent : baseEnd_5410911 < baseStart_5410911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410915 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 4, 2, 2]
def baseStart_5410915 : Nat := 118140960795 + 5410915 * 2 ^ 59
def prefixEnd_5410915 : Nat := 4983230072969 + 3 ^ 40 * 5410915 * 2
def baseEnd_5410915 : Nat := 2778400175622802503878161

theorem tailTrace_5410915 : CollatzResearch.WordTrace tailWord_5410915 prefixEnd_5410915 2778400175622802503878161 := by
  unfold tailWord_5410915
  simp only [CollatzResearch.WordTrace]
  refine ⟨197352283192186540554898199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131568188794791027036598799 197352283192186540554898199)
  ·
    refine ⟨296028424788279810832347299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197352283192186540554898199 296028424788279810832347299)
    ·
      refine ⟨444042637182419716248520949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296028424788279810832347299 444042637182419716248520949)
      ·
        refine ⟨41628997235851848398298839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 444042637182419716248520949 41628997235851848398298839)
        ·
          refine ⟨62443495853777772597448259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41628997235851848398298839 62443495853777772597448259)
          ·
            refine ⟨93665243780666658896172389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62443495853777772597448259 93665243780666658896172389)
            ·
              refine ⟨17562233208874998543032323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93665243780666658896172389 17562233208874998543032323)
              ·
                refine ⟨26343349813312497814548485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17562233208874998543032323 26343349813312497814548485)
                ·
                  refine ⟨4939378089996093340227841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26343349813312497814548485 4939378089996093340227841)
                  ·
                    refine ⟨3704533567497070005170881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939378089996093340227841 3704533567497070005170881)
                    ·
                      refine ⟨2778400175622802503878161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704533567497070005170881 2778400175622802503878161)
                      ·
                        rfl

theorem cell23_5410915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_5410915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410915 prefixEnd_5410915 := by exact prefixLift 5410915
  have htrace : WordTrace (prefixWord ++ tailWord_5410915) baseStart_5410915 baseEnd_5410915 := by
    simpa [prefixWord, tailWord_5410915, baseEnd_5410915] using wordTrace_append hprefix tailTrace_5410915
  have hstable : (prefixWord ++ tailWord_5410915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410915).length < 2 ^ (prefixWord ++ tailWord_5410915).sum := by decide
  have hdescent : baseEnd_5410915 < baseStart_5410915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410951 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 1, 7]
def baseStart_5410951 : Nat := 118140960795 + 5410951 * 2 ^ 59
def prefixEnd_5410951 : Nat := 4983230072969 + 3 ^ 40 * 5410951 * 2
def baseEnd_5410951 : Nat := 926139553642121454342665

theorem tailTrace_5410951 : CollatzResearch.WordTrace tailWord_5410951 prefixEnd_5410951 926139553642121454342665 := by
  unfold tailWord_5410951
  simp only [CollatzResearch.WordTrace]
  refine ⟨197353596220056118703208707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131569064146704079135472471 197353596220056118703208707)
  ·
    refine ⟨296030394330084178054813061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197353596220056118703208707 296030394330084178054813061)
    ·
      refine ⟨55505698936890783385277449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296030394330084178054813061 55505698936890783385277449)
      ·
        refine ⟨41629274202668087538958087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55505698936890783385277449 41629274202668087538958087)
        ·
          refine ⟨62443911304002131308437131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41629274202668087538958087 62443911304002131308437131)
          ·
            refine ⟨93665866956003196962655697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62443911304002131308437131 93665866956003196962655697)
            ·
              refine ⟨70249400217002397721991773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93665866956003196962655697 70249400217002397721991773)
              ·
                refine ⟨26343525081375899145746915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70249400217002397721991773 26343525081375899145746915)
                ·
                  refine ⟨39515287622063848718620373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26343525081375899145746915 39515287622063848718620373)
                  ·
                    refine ⟨926139553642121454342665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39515287622063848718620373 926139553642121454342665)
                    ·
                      rfl

theorem cell23_5410951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_5410951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410951 prefixEnd_5410951 := by exact prefixLift 5410951
  have htrace : WordTrace (prefixWord ++ tailWord_5410951) baseStart_5410951 baseEnd_5410951 := by
    simpa [prefixWord, tailWord_5410951, baseEnd_5410951] using wordTrace_append hprefix tailTrace_5410951
  have hstable : (prefixWord ++ tailWord_5410951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410951).length < 2 ^ (prefixWord ++ tailWord_5410951).sum := by decide
  have hdescent : baseEnd_5410951 < baseStart_5410951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410975 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5410975 : Nat := 118140960795 + 5410975 * 2 ^ 59
def prefixEnd_5410975 : Nat := 4983230072969 + 3 ^ 40 * 5410975 * 2
def baseEnd_5410975 : Nat := 2778430984462072269127885

theorem tailTrace_5410975 : CollatzResearch.WordTrace tailWord_5410975 prefixEnd_5410975 2778430984462072269127885 := by
  unfold tailWord_5410975
  simp only [CollatzResearch.WordTrace]
  refine ⟨197354471571969170802082379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131569647714646113868054919 197354471571969170802082379)
  ·
    refine ⟨296031707357953756203123569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197354471571969170802082379 296031707357953756203123569)
    ·
      refine ⟨222023780518465317152342677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296031707357953756203123569 222023780518465317152342677)
      ·
        refine ⟨10407364711803061741516063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222023780518465317152342677 10407364711803061741516063)
        ·
          refine ⟨15611047067704592612274095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10407364711803061741516063 15611047067704592612274095)
          ·
            refine ⟨23416570601556888918411143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15611047067704592612274095 23416570601556888918411143)
            ·
              refine ⟨35124855902335333377616715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23416570601556888918411143 35124855902335333377616715)
              ·
                refine ⟨52687283853503000066425073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35124855902335333377616715 52687283853503000066425073)
                ·
                  refine ⟨39515462890127250049818805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52687283853503000066425073 39515462890127250049818805)
                  ·
                    refine ⟨3704574645949429692170513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39515462890127250049818805 3704574645949429692170513)
                    ·
                      refine ⟨2778430984462072269127885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704574645949429692170513 2778430984462072269127885)
                      ·
                        rfl

theorem cell23_5410975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5410975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5410975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5410975 prefixEnd_5410975 := by exact prefixLift 5410975
  have htrace : WordTrace (prefixWord ++ tailWord_5410975) baseStart_5410975 baseEnd_5410975 := by
    simpa [prefixWord, tailWord_5410975, baseEnd_5410975] using wordTrace_append hprefix tailTrace_5410975
  have hstable : (prefixWord ++ tailWord_5410975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410975).length < 2 ^ (prefixWord ++ tailWord_5410975).sum := by decide
  have hdescent : baseEnd_5410975 < baseStart_5410975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411032 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 1, 4]
def baseStart_5411032 : Nat := 118140960795 + 5411032 * 2 ^ 59
def prefixEnd_5411032 : Nat := 4983230072969 + 3 ^ 40 * 5411032 * 2
def baseEnd_5411032 : Nat := 926153417619792848705041

theorem tailTrace_5411032 : CollatzResearch.WordTrace tailWord_5411032 prefixEnd_5411032 926153417619792848705041 := by
  unfold tailWord_5411032
  simp only [CollatzResearch.WordTrace]
  refine ⟨98678275266381334768453675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131571033688508446357938233 98678275266381334768453675)
  ·
    refine ⟨148017412899572002152680513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98678275266381334768453675 148017412899572002152680513)
    ·
      refine ⟨111013059674679001614510385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148017412899572002152680513 111013059674679001614510385)
      ·
        refine ⟨83259794756009251210882789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111013059674679001614510385 83259794756009251210882789)
        ·
          refine ⟨15611211516751734602040523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83259794756009251210882789 15611211516751734602040523)
          ·
            refine ⟨23416817275127601903060785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15611211516751734602040523 23416817275127601903060785)
            ·
              refine ⟨17562612956345701427295589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23416817275127601903060785 17562612956345701427295589)
              ·
                refine ⟨3292989929314819017617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17562612956345701427295589 3292989929314819017617923)
                ·
                  refine ⟨4939484893972228526426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292989929314819017617923 4939484893972228526426885)
                  ·
                    refine ⟨926153417619792848705041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939484893972228526426885 926153417619792848705041)
                    ·
                      rfl

theorem cell23_5411032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_5411032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411032 prefixEnd_5411032 := by exact prefixLift 5411032
  have htrace : WordTrace (prefixWord ++ tailWord_5411032) baseStart_5411032 baseEnd_5411032 := by
    simpa [prefixWord, tailWord_5411032, baseEnd_5411032] using wordTrace_append hprefix tailTrace_5411032
  have hstable : (prefixWord ++ tailWord_5411032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411032).length < 2 ^ (prefixWord ++ tailWord_5411032).sum := by decide
  have hdescent : baseEnd_5411032 < baseStart_5411032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411109 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_5411109 : Nat := 118140960795 + 5411109 * 2 ^ 59
def prefixEnd_5411109 : Nat := 4983230072969 + 3 ^ 40 * 5411109 * 2
def baseEnd_5411109 : Nat := 926166596956591581617423

theorem tailTrace_5411109 : CollatzResearch.WordTrace tailWord_5411109 prefixEnd_5411109 926166596956591581617423 := by
  unfold tailWord_5411109
  simp only [CollatzResearch.WordTrace]
  refine ⟨197359358953483711687460381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131572905968989141124973587 197359358953483711687460381)
  ·
    refine ⟨74009759607556391882797643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197359358953483711687460381 74009759607556391882797643)
    ·
      refine ⟨111014639411334587824196465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74009759607556391882797643 111014639411334587824196465)
      ·
        refine ⟨83260979558500940868147349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111014639411334587824196465 83260979558500940868147349)
        ·
          refine ⟨3902858416804731603194407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83260979558500940868147349 3902858416804731603194407)
          ·
            refine ⟨5854287625207097404791611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902858416804731603194407 5854287625207097404791611)
            ·
              refine ⟨8781431437810646107187417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854287625207097404791611 8781431437810646107187417)
              ·
                refine ⟨6586073578357984580390563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8781431437810646107187417 6586073578357984580390563)
                ·
                  refine ⟨9879110367536976870585845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6586073578357984580390563 9879110367536976870585845)
                  ·
                    refine ⟨926166596956591581617423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9879110367536976870585845 926166596956591581617423)
                    ·
                      rfl

theorem cell23_5411109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_5411109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411109 prefixEnd_5411109 := by exact prefixLift 5411109
  have htrace : WordTrace (prefixWord ++ tailWord_5411109) baseStart_5411109 baseEnd_5411109 := by
    simpa [prefixWord, tailWord_5411109, baseEnd_5411109] using wordTrace_append hprefix tailTrace_5411109
  have hstable : (prefixWord ++ tailWord_5411109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411109).length < 2 ^ (prefixWord ++ tailWord_5411109).sum := by decide
  have hdescent : baseEnd_5411109 < baseStart_5411109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411112 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_5411112 : Nat := 118140960795 + 5411112 * 2 ^ 59
def prefixEnd_5411112 : Nat := 4983230072969 + 3 ^ 40 * 5411112 * 2
def baseEnd_5411112 : Nat := 2778501331311738233114755

theorem tailTrace_5411112 : CollatzResearch.WordTrace tailWord_5411112 prefixEnd_5411112 2778501331311738233114755 := by
  unfold tailWord_5411112
  simp only [CollatzResearch.WordTrace]
  refine ⟨98679734186236421599909795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131572978914981895466546393 98679734186236421599909795)
  ·
    refine ⟨148019601279354632399864693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98679734186236421599909795 148019601279354632399864693)
    ·
      refine ⟨13876837619939496787487315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148019601279354632399864693 13876837619939496787487315)
      ·
        refine ⟨20815256429909245181230973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13876837619939496787487315 20815256429909245181230973)
        ·
          refine ⟨7805721161215966942961615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20815256429909245181230973 7805721161215966942961615)
          ·
            refine ⟨11708581741823950414442423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805721161215966942961615 11708581741823950414442423)
            ·
              refine ⟨17562872612735925621663635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11708581741823950414442423 17562872612735925621663635)
              ·
                refine ⟨26344308919103888432495453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17562872612735925621663635 26344308919103888432495453)
                ·
                  refine ⟨9879115844663958162185795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26344308919103888432495453 9879115844663958162185795)
                  ·
                    refine ⟨14818673766995937243278693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9879115844663958162185795 14818673766995937243278693)
                    ·
                      refine ⟨2778501331311738233114755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14818673766995937243278693 2778501331311738233114755)
                      ·
                        rfl

theorem cell23_5411112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_5411112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411112 prefixEnd_5411112 := by exact prefixLift 5411112
  have htrace : WordTrace (prefixWord ++ tailWord_5411112) baseStart_5411112 baseEnd_5411112 := by
    simpa [prefixWord, tailWord_5411112, baseEnd_5411112] using wordTrace_append hprefix tailTrace_5411112
  have hstable : (prefixWord ++ tailWord_5411112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411112).length < 2 ^ (prefixWord ++ tailWord_5411112).sum := by decide
  have hdescent : baseEnd_5411112 < baseStart_5411112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411125 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_5411125 : Nat := 118140960795 + 5411125 * 2 ^ 59
def prefixEnd_5411125 : Nat := 4983230072969 + 3 ^ 40 * 5411125 * 2
def baseEnd_5411125 : Nat := 2778508006560246682252195

theorem tailTrace_5411125 : CollatzResearch.WordTrace tailWord_5411125 prefixEnd_5411125 2778508006560246682252195 := by
  unfold tailWord_5411125
  simp only [CollatzResearch.WordTrace]
  refine ⟨197359942521425746420042829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131573295014283830946695219 197359942521425746420042829)
  ·
    refine ⟨74009978445534654907516061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197359942521425746420042829 74009978445534654907516061)
    ·
      refine ⟨27753741917075495590318523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74009978445534654907516061 27753741917075495590318523)
      ·
        refine ⟨41630612875613243385477785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27753741917075495590318523 41630612875613243385477785)
        ·
          refine ⟨31222959656709932539108339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41630612875613243385477785 31222959656709932539108339)
          ·
            refine ⟨46834439485064898808662509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31222959656709932539108339 46834439485064898808662509)
            ·
              refine ⟨17562914806899337053248441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46834439485064898808662509 17562914806899337053248441)
              ·
                refine ⟨13172186105174502789936331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17562914806899337053248441 13172186105174502789936331)
                ·
                  refine ⟨19758279157761754184904497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13172186105174502789936331 19758279157761754184904497)
                  ·
                    refine ⟨14818709368321315638678373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19758279157761754184904497 14818709368321315638678373)
                    ·
                      refine ⟨2778508006560246682252195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14818709368321315638678373 2778508006560246682252195)
                      ·
                        rfl

theorem cell23_5411125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_5411125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411125 prefixEnd_5411125 := by exact prefixLift 5411125
  have htrace : WordTrace (prefixWord ++ tailWord_5411125) baseStart_5411125 baseEnd_5411125 := by
    simpa [prefixWord, tailWord_5411125, baseEnd_5411125] using wordTrace_append hprefix tailTrace_5411125
  have hstable : (prefixWord ++ tailWord_5411125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411125).length < 2 ^ (prefixWord ++ tailWord_5411125).sum := by decide
  have hdescent : baseEnd_5411125 < baseStart_5411125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411129 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5411129 : Nat := 118140960795 + 5411129 * 2 ^ 59
def prefixEnd_5411129 : Nat := 4983230072969 + 3 ^ 40 * 5411129 * 2
def baseEnd_5411129 : Nat := 2778510060482864666602177

theorem tailTrace_5411129 : CollatzResearch.WordTrace tailWord_5411129 prefixEnd_5411129 2778510060482864666602177 := by
  unfold tailWord_5411129
  simp only [CollatzResearch.WordTrace]
  refine ⟨197360088413411255103188441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131573392275607503402125627 197360088413411255103188441)
  ·
    refine ⟨148020066310058441327391331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197360088413411255103188441 148020066310058441327391331)
    ·
      refine ⟨222030099465087661991086997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148020066310058441327391331 222030099465087661991086997)
      ·
        refine ⟨10407660912425984155832203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222030099465087661991086997 10407660912425984155832203)
        ·
          refine ⟨15611491368638976233748305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10407660912425984155832203 15611491368638976233748305)
          ·
            refine ⟨11708618526479232175311229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15611491368638976233748305 11708618526479232175311229)
            ·
              refine ⟨4390731947429712065741711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11708618526479232175311229 4390731947429712065741711)
              ·
                refine ⟨6586097921144568098612567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390731947429712065741711 6586097921144568098612567)
                ·
                  refine ⟨9879146881716852147918851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6586097921144568098612567 9879146881716852147918851)
                  ·
                    refine ⟨14818720322575278221878277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9879146881716852147918851 14818720322575278221878277)
                    ·
                      refine ⟨2778510060482864666602177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14818720322575278221878277 2778510060482864666602177)
                      ·
                        rfl

theorem cell23_5411129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5411129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411129 prefixEnd_5411129 := by exact prefixLift 5411129
  have htrace : WordTrace (prefixWord ++ tailWord_5411129) baseStart_5411129 baseEnd_5411129 := by
    simpa [prefixWord, tailWord_5411129, baseEnd_5411129] using wordTrace_append hprefix tailTrace_5411129
  have hstable : (prefixWord ++ tailWord_5411129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411129).length < 2 ^ (prefixWord ++ tailWord_5411129).sum := by decide
  have hdescent : baseEnd_5411129 < baseStart_5411129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411140 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5411140 : Nat := 118140960795 + 5411140 * 2 ^ 59
def prefixEnd_5411140 : Nat := 4983230072969 + 3 ^ 40 * 5411140 * 2
def baseEnd_5411140 : Nat := 2778515708770064123564627

theorem tailTrace_5411140 : CollatzResearch.WordTrace tailWord_5411140 prefixEnd_5411140 2778515708770064123564627 := by
  unfold tailWord_5411140
  simp only [CollatzResearch.WordTrace]
  refine ⟨98680244808185701990919437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131573659744247602654559249 98680244808185701990919437)
  ·
    refine ⟨37005091803069638246594789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98680244808185701990919437 37005091803069638246594789)
    ·
      refine ⟨6938454713075557171236523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37005091803069638246594789 6938454713075557171236523)
      ·
        refine ⟨10407682069613335756854785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6938454713075557171236523 10407682069613335756854785)
        ·
          refine ⟨7805761552210001817641089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10407682069613335756854785 7805761552210001817641089)
          ·
            refine ⟨5854321164157501363230817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7805761552210001817641089 5854321164157501363230817)
            ·
              refine ⟨4390740873118126022423113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854321164157501363230817 4390740873118126022423113)
              ·
                refine ⟨3293055654838594516817335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4390740873118126022423113 3293055654838594516817335)
                ·
                  refine ⟨4939583482257891775226003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293055654838594516817335 4939583482257891775226003)
                  ·
                    refine ⟨7409375223386837662839005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4939583482257891775226003 7409375223386837662839005)
                    ·
                      refine ⟨2778515708770064123564627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7409375223386837662839005 2778515708770064123564627)
                      ·
                        rfl

theorem cell23_5411140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5411140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411140 prefixEnd_5411140 := by exact prefixLift 5411140
  have htrace : WordTrace (prefixWord ++ tailWord_5411140) baseStart_5411140 baseEnd_5411140 := by
    simpa [prefixWord, tailWord_5411140, baseEnd_5411140] using wordTrace_append hprefix tailTrace_5411140
  have hstable : (prefixWord ++ tailWord_5411140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411140).length < 2 ^ (prefixWord ++ tailWord_5411140).sum := by decide
  have hdescent : baseEnd_5411140 < baseStart_5411140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411148 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_5411148 : Nat := 118140960795 + 5411148 * 2 ^ 59
def prefixEnd_5411148 : Nat := 4983230072969 + 3 ^ 40 * 5411148 * 2
def baseEnd_5411148 : Nat := 926173272205100030754863

theorem tailTrace_5411148 : CollatzResearch.WordTrace tailWord_5411148 prefixEnd_5411148 926173272205100030754863 := by
  unfold tailWord_5411148
  simp only [CollatzResearch.WordTrace]
  refine ⟨98680390700171210674065049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131573854266894947565420065 98680390700171210674065049)
  ·
    refine ⟨74010293025128408005548787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98680390700171210674065049 74010293025128408005548787)
    ·
      refine ⟨111015439537692612008323181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74010293025128408005548787 111015439537692612008323181)
      ·
        refine ⟨41630789826634729503121193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111015439537692612008323181 41630789826634729503121193)
        ·
          refine ⟨31223092369976047127340895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41630789826634729503121193 31223092369976047127340895)
          ·
            refine ⟨46834638554964070691011343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31223092369976047127340895 46834638554964070691011343)
            ·
              refine ⟨70251957832446106036517015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46834638554964070691011343 70251957832446106036517015)
              ·
                refine ⟨105377936748669159054775523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70251957832446106036517015 105377936748669159054775523)
                ·
                  refine ⟨158066905123003738582163285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105377936748669159054775523 158066905123003738582163285)
                  ·
                    refine ⟨926173272205100030754863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158066905123003738582163285 926173272205100030754863)
                    ·
                      rfl

theorem cell23_5411148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_5411148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411148 prefixEnd_5411148 := by exact prefixLift 5411148
  have htrace : WordTrace (prefixWord ++ tailWord_5411148) baseStart_5411148 baseEnd_5411148 := by
    simpa [prefixWord, tailWord_5411148, baseEnd_5411148] using wordTrace_append hprefix tailTrace_5411148
  have hstable : (prefixWord ++ tailWord_5411148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411148).length < 2 ^ (prefixWord ++ tailWord_5411148).sum := by decide
  have hdescent : baseEnd_5411148 < baseStart_5411148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411172 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_5411172 : Nat := 118140960795 + 5411172 * 2 ^ 59
def prefixEnd_5411172 : Nat := 4983230072969 + 3 ^ 40 * 5411172 * 2
def baseEnd_5411172 : Nat := 2778532140151007998364479

theorem tailTrace_5411172 : CollatzResearch.WordTrace tailWord_5411172 prefixEnd_5411172 2778532140151007998364479 := by
  unfold tailWord_5411172
  simp only [CollatzResearch.WordTrace]
  refine ⟨98680828376127736723501885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131574437834836982298002513 98680828376127736723501885)
  ·
    refine ⟨37005310641047901271313207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98680828376127736723501885 37005310641047901271313207)
    ·
      refine ⟨55507965961571851906969811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37005310641047901271313207 55507965961571851906969811)
      ·
        refine ⟨83261948942357777860454717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55507965961571851906969811 83261948942357777860454717)
        ·
          refine ⟨31223230853384166697670519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83261948942357777860454717 31223230853384166697670519)
          ·
            refine ⟨46834846280076250046505779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31223230853384166697670519 46834846280076250046505779)
            ·
              refine ⟨70252269420114375069758669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46834846280076250046505779 70252269420114375069758669)
              ·
                refine ⟨26344601032542890651159501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70252269420114375069758669 26344601032542890651159501)
                ·
                  refine ⟨9879225387203583994184813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26344601032542890651159501 9879225387203583994184813)
                  ·
                    refine ⟨3704709520201343997819305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9879225387203583994184813 3704709520201343997819305)
                    ·
                      refine ⟨2778532140151007998364479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704709520201343997819305 2778532140151007998364479)
                      ·
                        rfl

theorem cell23_5411172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_5411172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411172 prefixEnd_5411172 := by exact prefixLift 5411172
  have htrace : WordTrace (prefixWord ++ tailWord_5411172) baseStart_5411172 baseEnd_5411172 := by
    simpa [prefixWord, tailWord_5411172, baseEnd_5411172] using wordTrace_append hprefix tailTrace_5411172
  have hstable : (prefixWord ++ tailWord_5411172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411172).length < 2 ^ (prefixWord ++ tailWord_5411172).sum := by decide
  have hdescent : baseEnd_5411172 < baseStart_5411172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411255 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 4, 5]
def baseStart_5411255 : Nat := 118140960795 + 5411255 * 2 ^ 59
def prefixEnd_5411255 : Nat := 4983230072969 + 3 ^ 40 * 5411255 * 2
def baseEnd_5411255 : Nat := 926191586348443724542199

theorem tailTrace_5411255 : CollatzResearch.WordTrace tailWord_5411255 prefixEnd_5411255 926191586348443724542199 := by
  unfold tailWord_5411255
  simp only [CollatzResearch.WordTrace]
  refine ⟨197364684010954778622275219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131576456007303185748183479 197364684010954778622275219)
  ·
    refine ⟨296047026016432167933412829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197364684010954778622275219 296047026016432167933412829)
    ·
      refine ⟨111017634756162062975029811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296047026016432167933412829 111017634756162062975029811)
      ·
        refine ⟨166526452134243094462544717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111017634756162062975029811 166526452134243094462544717)
        ·
          refine ⟨62447419550341160423454269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166526452134243094462544717 62447419550341160423454269)
          ·
            refine ⟨23417782331377935158795351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62447419550341160423454269 23417782331377935158795351)
            ·
              refine ⟨35126673497066902738193027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23417782331377935158795351 35126673497066902738193027)
              ·
                refine ⟨52690010245600354107289541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35126673497066902738193027 52690010245600354107289541)
                ·
                  refine ⟨9879376921050066395116789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52690010245600354107289541 9879376921050066395116789)
                  ·
                    refine ⟨926191586348443724542199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9879376921050066395116789 926191586348443724542199)
                    ·
                      rfl

theorem cell23_5411255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_5411255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411255 prefixEnd_5411255 := by exact prefixLift 5411255
  have htrace : WordTrace (prefixWord ++ tailWord_5411255) baseStart_5411255 baseEnd_5411255 := by
    simpa [prefixWord, tailWord_5411255, baseEnd_5411255] using wordTrace_append hprefix tailTrace_5411255
  have hstable : (prefixWord ++ tailWord_5411255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411255).length < 2 ^ (prefixWord ++ tailWord_5411255).sum := by decide
  have hdescent : baseEnd_5411255 < baseStart_5411255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411275 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 4]
def baseStart_5411275 : Nat := 118140960795 + 5411275 * 2 ^ 59
def prefixEnd_5411275 : Nat := 4983230072969 + 3 ^ 40 * 5411275 * 2
def baseEnd_5411275 : Nat := 2778585028658421095376505

theorem tailTrace_5411275 : CollatzResearch.WordTrace tailWord_5411275 prefixEnd_5411275 2778585028658421095376505 := by
  unfold tailWord_5411275
  simp only [CollatzResearch.WordTrace]
  refine ⟨197365413470882322038003279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131576942313921548025335519 197365413470882322038003279)
  ·
    refine ⟨296048120206323483057004919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197365413470882322038003279 296048120206323483057004919)
    ·
      refine ⟨444072180309485224585507379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296048120206323483057004919 444072180309485224585507379)
      ·
        refine ⟨666108270464227836878261069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444072180309485224585507379 666108270464227836878261069)
        ·
          refine ⟨249790601424085438829347901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 666108270464227836878261069 249790601424085438829347901)
          ·
            refine ⟨93671475534032039561005463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249790601424085438829347901 93671475534032039561005463)
            ·
              refine ⟨140507213301048059341508195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93671475534032039561005463 140507213301048059341508195)
              ·
                refine ⟨210760819951572089012262293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140507213301048059341508195 210760819951572089012262293)
                ·
                  refine ⟨9879413435229941672449795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210760819951572089012262293 9879413435229941672449795)
                  ·
                    refine ⟨14819120152844912508674693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9879413435229941672449795 14819120152844912508674693)
                    ·
                      refine ⟨2778585028658421095376505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14819120152844912508674693 2778585028658421095376505)
                      ·
                        rfl

theorem cell23_5411275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 4].length) (baseStart_5411275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411275 prefixEnd_5411275 := by exact prefixLift 5411275
  have htrace : WordTrace (prefixWord ++ tailWord_5411275) baseStart_5411275 baseEnd_5411275 := by
    simpa [prefixWord, tailWord_5411275, baseEnd_5411275] using wordTrace_append hprefix tailTrace_5411275
  have hstable : (prefixWord ++ tailWord_5411275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411275).length < 2 ^ (prefixWord ++ tailWord_5411275).sum := by decide
  have hdescent : baseEnd_5411275 < baseStart_5411275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411309 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5411309 : Nat := 118140960795 + 5411309 * 2 ^ 59
def prefixEnd_5411309 : Nat := 4983230072969 + 3 ^ 40 * 5411309 * 2
def baseEnd_5411309 : Nat := 2778602487000673962351349

theorem tailTrace_5411309 : CollatzResearch.WordTrace tailWord_5411309 prefixEnd_5411309 2778602487000673962351349 := by
  unfold tailWord_5411309
  simp only [CollatzResearch.WordTrace]
  refine ⟨197366653552759145844740981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131577769035172763896493987 197366653552759145844740981)
  ·
    refine ⟨18503123770571169922944467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197366653552759145844740981 18503123770571169922944467)
    ·
      refine ⟨27754685655856754884416701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18503123770571169922944467 27754685655856754884416701)
      ·
        refine ⟨10408007120946283081656263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27754685655856754884416701 10408007120946283081656263)
        ·
          refine ⟨15612010681419424622484395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10408007120946283081656263 15612010681419424622484395)
          ·
            refine ⟨23418016022129136933726593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15612010681419424622484395 23418016022129136933726593)
            ·
              refine ⟨17563512016596852700294945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23418016022129136933726593 17563512016596852700294945)
              ·
                refine ⟨13172634012447639525221209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17563512016596852700294945 13172634012447639525221209)
                ·
                  refine ⟨9879475509335729643915907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13172634012447639525221209 9879475509335729643915907)
                  ·
                    refine ⟨14819213264003594465873861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9879475509335729643915907 14819213264003594465873861)
                    ·
                      refine ⟨2778602487000673962351349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14819213264003594465873861 2778602487000673962351349)
                      ·
                        rfl

theorem cell23_5411309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5411309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411309 prefixEnd_5411309 := by exact prefixLift 5411309
  have htrace : WordTrace (prefixWord ++ tailWord_5411309) baseStart_5411309 baseEnd_5411309 := by
    simpa [prefixWord, tailWord_5411309, baseEnd_5411309] using wordTrace_append hprefix tailTrace_5411309
  have hstable : (prefixWord ++ tailWord_5411309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411309).length < 2 ^ (prefixWord ++ tailWord_5411309).sum := by decide
  have hdescent : baseEnd_5411309 < baseStart_5411309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411312 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_5411312 : Nat := 118140960795 + 5411312 * 2 ^ 59
def prefixEnd_5411312 : Nat := 4983230072969 + 3 ^ 40 * 5411312 * 2
def baseEnd_5411312 : Nat := 2778604027442637450613835

theorem tailTrace_5411312 : CollatzResearch.WordTrace tailWord_5411312 prefixEnd_5411312 2778604027442637450613835 := by
  unfold tailWord_5411312
  simp only [CollatzResearch.WordTrace]
  refine ⟨98683381485874138678550095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131577841981165518238066793 98683381485874138678550095)
  ·
    refine ⟨148025072228811208017825143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98683381485874138678550095 148025072228811208017825143)
    ·
      refine ⟨222037608343216812026737715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148025072228811208017825143 222037608343216812026737715)
      ·
        refine ⟨333056412514825218040106573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222037608343216812026737715 333056412514825218040106573)
        ·
          refine ⟨124896154693059456765039965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333056412514825218040106573 124896154693059456765039965)
          ·
            refine ⟨46836058009897296286889987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124896154693059456765039965 46836058009897296286889987)
            ·
              refine ⟨70254087014845944430334981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46836058009897296286889987 70254087014845944430334981)
              ·
                refine ⟨13172641315283614580687809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70254087014845944430334981 13172641315283614580687809)
                ·
                  refine ⟨9879480986462710935515857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13172641315283614580687809 9879480986462710935515857)
                  ·
                    refine ⟨7409610739847033201636893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9879480986462710935515857 7409610739847033201636893)
                    ·
                      refine ⟨2778604027442637450613835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7409610739847033201636893 2778604027442637450613835)
                      ·
                        rfl

theorem cell23_5411312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_5411312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411312 prefixEnd_5411312 := by exact prefixLift 5411312
  have htrace : WordTrace (prefixWord ++ tailWord_5411312) baseStart_5411312 baseEnd_5411312 := by
    simpa [prefixWord, tailWord_5411312, baseEnd_5411312] using wordTrace_append hprefix tailTrace_5411312
  have hstable : (prefixWord ++ tailWord_5411312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411312).length < 2 ^ (prefixWord ++ tailWord_5411312).sum := by decide
  have hdescent : baseEnd_5411312 < baseStart_5411312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411376 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 1, 1, 3]
def baseStart_5411376 : Nat := 118140960795 + 5411376 * 2 ^ 59
def prefixEnd_5411376 : Nat := 4983230072969 + 3 ^ 40 * 5411376 * 2
def baseEnd_5411376 : Nat := 2778636890204525200213541

theorem tailTrace_5411376 : CollatzResearch.WordTrace tailWord_5411376 prefixEnd_5411376 2778636890204525200213541 := by
  unfold tailWord_5411376
  simp only [CollatzResearch.WordTrace]
  refine ⟨98684548621758208143714991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131579398162344277524953321 98684548621758208143714991)
  ·
    refine ⟨148026822932637312215572487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98684548621758208143714991 148026822932637312215572487)
    ·
      refine ⟨222040234398955968323358731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148026822932637312215572487 222040234398955968323358731)
      ·
        refine ⟨333060351598433952485038097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222040234398955968323358731 333060351598433952485038097)
        ·
          refine ⟨249795263698825464363778573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333060351598433952485038097 249795263698825464363778573)
          ·
            refine ⟨93673223887059549136416965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249795263698825464363778573 93673223887059549136416965)
            ·
              refine ⟨17563729478823665463078181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93673223887059549136416965 17563729478823665463078181)
              ·
                refine ⟨3293199277279437274327159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17563729478823665463078181 3293199277279437274327159)
                ·
                  refine ⟨4939798915919155911490739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293199277279437274327159 4939798915919155911490739)
                  ·
                    refine ⟨7409698373878733867236109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4939798915919155911490739 7409698373878733867236109)
                    ·
                      refine ⟨2778636890204525200213541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7409698373878733867236109 2778636890204525200213541)
                      ·
                        rfl

theorem cell23_5411376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 1, 3].length) (baseStart_5411376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411376 prefixEnd_5411376 := by exact prefixLift 5411376
  have htrace : WordTrace (prefixWord ++ tailWord_5411376) baseStart_5411376 baseEnd_5411376 := by
    simpa [prefixWord, tailWord_5411376, baseEnd_5411376] using wordTrace_append hprefix tailTrace_5411376
  have hstable : (prefixWord ++ tailWord_5411376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411376).length < 2 ^ (prefixWord ++ tailWord_5411376).sum := by decide
  have hdescent : baseEnd_5411376 < baseStart_5411376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411392 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 1, 6]
def baseStart_5411392 : Nat := 118140960795 + 5411392 * 2 ^ 59
def prefixEnd_5411392 : Nat := 4983230072969 + 3 ^ 40 * 5411392 * 2
def baseEnd_5411392 : Nat := 926215035298332379204489

theorem tailTrace_5411392 : CollatzResearch.WordTrace tailWord_5411392 prefixEnd_5411392 926215035298332379204489 := by
  unfold tailWord_5411392
  simp only [CollatzResearch.WordTrace]
  refine ⟨98684840405729225510006215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131579787207638967346674953 98684840405729225510006215)
  ·
    refine ⟨148027260608593838265009323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98684840405729225510006215 148027260608593838265009323)
    ·
      refine ⟨222040890912890757397513985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148027260608593838265009323 222040890912890757397513985)
      ·
        refine ⟨166530668184668068048135489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222040890912890757397513985 166530668184668068048135489)
        ·
          refine ⟨124898001138501051036101617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166530668184668068048135489 124898001138501051036101617)
          ·
            refine ⟨93673500853875788277076213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124898001138501051036101617 93673500853875788277076213)
            ·
              refine ⟨8781890705050855150975895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93673500853875788277076213 8781890705050855150975895)
              ·
                refine ⟨13172836057576282726463843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8781890705050855150975895 13172836057576282726463843)
                ·
                  refine ⟨19759254086364424089695765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13172836057576282726463843 19759254086364424089695765)
                  ·
                    refine ⟨926215035298332379204489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19759254086364424089695765 926215035298332379204489)
                    ·
                      rfl

theorem cell23_5411392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_5411392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411392 prefixEnd_5411392 := by exact prefixLift 5411392
  have htrace : WordTrace (prefixWord ++ tailWord_5411392) baseStart_5411392 baseEnd_5411392 := by
    simpa [prefixWord, tailWord_5411392, baseEnd_5411392] using wordTrace_append hprefix tailTrace_5411392
  have hstable : (prefixWord ++ tailWord_5411392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411392).length < 2 ^ (prefixWord ++ tailWord_5411392).sum := by decide
  have hdescent : baseEnd_5411392 < baseStart_5411392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411399 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_5411399 : Nat := 118140960795 + 5411399 * 2 ^ 59
def prefixEnd_5411399 : Nat := 4983230072969 + 3 ^ 40 * 5411399 * 2
def baseEnd_5411399 : Nat := 2778648700259578610225935

theorem tailTrace_5411399 : CollatzResearch.WordTrace tailWord_5411399 prefixEnd_5411399 2778648700259578610225935 := by
  unfold tailWord_5411399
  simp only [CollatzResearch.WordTrace]
  refine ⟨197369936122433091215517251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131579957414955394143678167 197369936122433091215517251)
  ·
    refine ⟨296054904183649636823275877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197369936122433091215517251 296054904183649636823275877)
    ·
      refine ⟨55510294534434306904364227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296054904183649636823275877 55510294534434306904364227)
      ·
        refine ⟨83265441801651460356546341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55510294534434306904364227 83265441801651460356546341)
        ·
          refine ⟨15612270337809648816852439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83265441801651460356546341 15612270337809648816852439)
          ·
            refine ⟨23418405506714473225278659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15612270337809648816852439 23418405506714473225278659)
            ·
              refine ⟨35127608260071709837917989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23418405506714473225278659 35127608260071709837917989)
              ·
                refine ⟨6586426548763445594609623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35127608260071709837917989 6586426548763445594609623)
                ·
                  refine ⟨9879639823145168391914435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6586426548763445594609623 9879639823145168391914435)
                  ·
                    refine ⟨14819459734717752587871653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9879639823145168391914435 14819459734717752587871653)
                    ·
                      refine ⟨2778648700259578610225935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14819459734717752587871653 2778648700259578610225935)
                      ·
                        rfl

theorem cell23_5411399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_5411399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411399 prefixEnd_5411399 := by exact prefixLift 5411399
  have htrace : WordTrace (prefixWord ++ tailWord_5411399) baseStart_5411399 baseEnd_5411399 := by
    simpa [prefixWord, tailWord_5411399, baseEnd_5411399] using wordTrace_append hprefix tailTrace_5411399
  have hstable : (prefixWord ++ tailWord_5411399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411399).length < 2 ^ (prefixWord ++ tailWord_5411399).sum := by decide
  have hdescent : baseEnd_5411399 < baseStart_5411399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411453 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_5411453 : Nat := 118140960795 + 5411453 * 2 ^ 59
def prefixEnd_5411453 : Nat := 4983230072969 + 3 ^ 40 * 5411453 * 2
def baseEnd_5411453 : Nat := 2778676428214921398950687

theorem tailTrace_5411453 : CollatzResearch.WordTrace tailWord_5411453 prefixEnd_5411453 2778676428214921398950687 := by
  unfold tailWord_5411453
  simp only [CollatzResearch.WordTrace]
  refine ⟨197371905664237458437983013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131581270442824972291988675 197371905664237458437983013)
  ·
    refine ⟨37007232312044523457121815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197371905664237458437983013 37007232312044523457121815)
    ·
      refine ⟨55510848468066785185682723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37007232312044523457121815 55510848468066785185682723)
      ·
        refine ⟨83266272702100177778524085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55510848468066785185682723 83266272702100177778524085)
        ·
          refine ⟨7806213065821891666736633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83266272702100177778524085 7806213065821891666736633)
          ·
            refine ⟨5854659799366418750052475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7806213065821891666736633 5854659799366418750052475)
            ·
              refine ⟨8781989699049628125078713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854659799366418750052475 8781989699049628125078713)
              ·
                refine ⟨6586492274287221093809035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8781989699049628125078713 6586492274287221093809035)
                ·
                  refine ⟨9879738411430831640713553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6586492274287221093809035 9879738411430831640713553)
                  ·
                    refine ⟨7409803808573123730535165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9879738411430831640713553 7409803808573123730535165)
                    ·
                      refine ⟨2778676428214921398950687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7409803808573123730535165 2778676428214921398950687)
                      ·
                        rfl

theorem cell23_5411453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_5411453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411453 prefixEnd_5411453 := by exact prefixLift 5411453
  have htrace : WordTrace (prefixWord ++ tailWord_5411453) baseStart_5411453 baseEnd_5411453 := by
    simpa [prefixWord, tailWord_5411453, baseEnd_5411453] using wordTrace_append hprefix tailTrace_5411453
  have hstable : (prefixWord ++ tailWord_5411453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411453).length < 2 ^ (prefixWord ++ tailWord_5411453).sum := by decide
  have hdescent : baseEnd_5411453 < baseStart_5411453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411466 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_5411466 : Nat := 118140960795 + 5411466 * 2 ^ 59
def prefixEnd_5411466 : Nat := 4983230072969 + 3 ^ 40 * 5411466 * 2
def baseEnd_5411466 : Nat := 2778683103463429848088127

theorem tailTrace_5411466 : CollatzResearch.WordTrace tailWord_5411466 prefixEnd_5411466 2778683103463429848088127 := by
  unfold tailWord_5411466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49343094953297590414551563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131581586542126907772137501 49343094953297590414551563)
  ·
    refine ⟨74014642429946385621827345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49343094953297590414551563 74014642429946385621827345)
    ·
      refine ⟨55510981822459789216370509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74014642429946385621827345 55510981822459789216370509)
      ·
        refine ⟨20816618183422420956138941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55510981822459789216370509 20816618183422420956138941)
        ·
          refine ⟨7806231818783407858552103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20816618183422420956138941 7806231818783407858552103)
          ·
            refine ⟨11709347728175111787828155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806231818783407858552103 11709347728175111787828155)
            ·
              refine ⟨17564021592262667681742233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11709347728175111787828155 17564021592262667681742233)
              ·
                refine ⟨13173016194197000761306675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17564021592262667681742233 13173016194197000761306675)
                ·
                  refine ⟨19759524291295501141960013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13173016194197000761306675 19759524291295501141960013)
                  ·
                    refine ⟨7409821609235812928235005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19759524291295501141960013 7409821609235812928235005)
                    ·
                      refine ⟨2778683103463429848088127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7409821609235812928235005 2778683103463429848088127)
                      ·
                        rfl

theorem cell23_5411466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_5411466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411466 prefixEnd_5411466 := by exact prefixLift 5411466
  have htrace : WordTrace (prefixWord ++ tailWord_5411466) baseStart_5411466 baseEnd_5411466 := by
    simpa [prefixWord, tailWord_5411466, baseEnd_5411466] using wordTrace_append hprefix tailTrace_5411466
  have hstable : (prefixWord ++ tailWord_5411466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411466).length < 2 ^ (prefixWord ++ tailWord_5411466).sum := by decide
  have hdescent : baseEnd_5411466 < baseStart_5411466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411506 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_5411506 : Nat := 118140960795 + 5411506 * 2 ^ 59
def prefixEnd_5411506 : Nat := 4983230072969 + 3 ^ 40 * 5411506 * 2
def baseEnd_5411506 : Nat := 2778703642689609691587943

theorem tailTrace_5411506 : CollatzResearch.WordTrace tailWord_5411506 prefixEnd_5411506 2778703642689609691587943 := by
  unfold tailWord_5411506
  simp only [CollatzResearch.WordTrace]
  refine ⟨49343459683261362122415593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131582559155363632326441581 49343459683261362122415593)
  ·
    refine ⟨37007594762446021591811695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49343459683261362122415593 37007594762446021591811695)
    ·
      refine ⟨55511392143669032387717543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37007594762446021591811695 55511392143669032387717543)
      ·
        refine ⟨83267088215503548581576315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55511392143669032387717543 83267088215503548581576315)
        ·
          refine ⟨124900632323255322872364473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83267088215503548581576315 124900632323255322872364473)
          ·
            refine ⟨93675474242441492154273355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124900632323255322872364473 93675474242441492154273355)
            ·
              refine ⟨140513211363662238231410033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93675474242441492154273355 140513211363662238231410033)
              ·
                refine ⟨105384908522746678673557525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140513211363662238231410033 105384908522746678673557525)
                ·
                  refine ⟨4939917587003750562823009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105384908522746678673557525 4939917587003750562823009)
                  ·
                    refine ⟨3704938190252812922117257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939917587003750562823009 3704938190252812922117257)
                    ·
                      refine ⟨2778703642689609691587943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704938190252812922117257 2778703642689609691587943)
                      ·
                        rfl

theorem cell23_5411506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_5411506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411506 prefixEnd_5411506 := by exact prefixLift 5411506
  have htrace : WordTrace (prefixWord ++ tailWord_5411506) baseStart_5411506 baseEnd_5411506 := by
    simpa [prefixWord, tailWord_5411506, baseEnd_5411506] using wordTrace_append hprefix tailTrace_5411506
  have hstable : (prefixWord ++ tailWord_5411506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411506).length < 2 ^ (prefixWord ++ tailWord_5411506).sum := by decide
  have hdescent : baseEnd_5411506 < baseStart_5411506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411540 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5411540 : Nat := 118140960795 + 5411540 * 2 ^ 59
def prefixEnd_5411540 : Nat := 4983230072969 + 3 ^ 40 * 5411540 * 2
def baseEnd_5411540 : Nat := 2778721101031862558562787

theorem tailTrace_5411540 : CollatzResearch.WordTrace tailWord_5411540 prefixEnd_5411540 2778721101031862558562787 := by
  unfold tailWord_5411540
  simp only [CollatzResearch.WordTrace]
  refine ⟨98687539407461136148200037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131583385876614848197600049 98687539407461136148200037)
  ·
    refine ⟨18503913638898963027787507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98687539407461136148200037 18503913638898963027787507)
    ·
      refine ⟨27755870458348444541681261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18503913638898963027787507 27755870458348444541681261)
      ·
        refine ⟨10408451421880666703130473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27755870458348444541681261 10408451421880666703130473)
        ·
          refine ⟨7806338566410500027347855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10408451421880666703130473 7806338566410500027347855)
          ·
            refine ⟨11709507849615750041021783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806338566410500027347855 11709507849615750041021783)
            ·
              refine ⟨17564261774423625061532675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11709507849615750041021783 17564261774423625061532675)
              ·
                refine ⟨26346392661635437592299013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17564261774423625061532675 26346392661635437592299013)
                ·
                  refine ⟨4939948624056644548556065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26346392661635437592299013 4939948624056644548556065)
                  ·
                    refine ⟨3704961468042483411417049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939948624056644548556065 3704961468042483411417049)
                    ·
                      refine ⟨2778721101031862558562787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3704961468042483411417049 2778721101031862558562787)
                      ·
                        rfl

theorem cell23_5411540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5411540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411540 prefixEnd_5411540 := by exact prefixLift 5411540
  have htrace : WordTrace (prefixWord ++ tailWord_5411540) baseStart_5411540 baseEnd_5411540 := by
    simpa [prefixWord, tailWord_5411540, baseEnd_5411540] using wordTrace_append hprefix tailTrace_5411540
  have hstable : (prefixWord ++ tailWord_5411540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411540).length < 2 ^ (prefixWord ++ tailWord_5411540).sum := by decide
  have hdescent : baseEnd_5411540 < baseStart_5411540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411552 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_5411552 : Nat := 118140960795 + 5411552 * 2 ^ 59
def prefixEnd_5411552 : Nat := 4983230072969 + 3 ^ 40 * 5411552 * 2
def baseEnd_5411552 : Nat := 2778727262799716511612731

theorem tailTrace_5411552 : CollatzResearch.WordTrace tailWord_5411552 prefixEnd_5411552 2778727262799716511612731 := by
  unfold tailWord_5411552
  simp only [CollatzResearch.WordTrace]
  refine ⟨98687758245439399172918455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131583677660585865563891273 98687758245439399172918455)
  ·
    refine ⟨148031637368159098759377683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98687758245439399172918455 148031637368159098759377683)
    ·
      refine ⟨222047456052238648139066525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148031637368159098759377683 222047456052238648139066525)
      ·
        refine ⟨83267796019589493052149947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222047456052238648139066525 83267796019589493052149947)
        ·
          refine ⟨124901694029384239578224921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83267796019589493052149947 124901694029384239578224921)
          ·
            refine ⟨93676270522038179683668691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124901694029384239578224921 93676270522038179683668691)
            ·
              refine ⟨140514405783057269525503037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93676270522038179683668691 140514405783057269525503037)
              ·
                refine ⟨52692902168646476072063639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140514405783057269525503037 52692902168646476072063639)
                ·
                  refine ⟨79039353252969714108095459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52692902168646476072063639 79039353252969714108095459)
                  ·
                    refine ⟨118559029879454571162143189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79039353252969714108095459 118559029879454571162143189)
                    ·
                      refine ⟨2778727262799716511612731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118559029879454571162143189 2778727262799716511612731)
                      ·
                        rfl

theorem cell23_5411552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_5411552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411552 prefixEnd_5411552 := by exact prefixLift 5411552
  have htrace : WordTrace (prefixWord ++ tailWord_5411552) baseStart_5411552 baseEnd_5411552 := by
    simpa [prefixWord, tailWord_5411552, baseEnd_5411552] using wordTrace_append hprefix tailTrace_5411552
  have hstable : (prefixWord ++ tailWord_5411552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411552).length < 2 ^ (prefixWord ++ tailWord_5411552).sum := by decide
  have hdescent : baseEnd_5411552 < baseStart_5411552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411589 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_5411589 : Nat := 118140960795 + 5411589 * 2 ^ 59
def prefixEnd_5411589 : Nat := 4983230072969 + 3 ^ 40 * 5411589 * 2
def baseEnd_5411589 : Nat := 926248753861310955616687

theorem tailTrace_5411589 : CollatzResearch.WordTrace tailWord_5411589 prefixEnd_5411589 926248753861310955616687 := by
  unfold tailWord_5411589
  simp only [CollatzResearch.WordTrace]
  refine ⟨197376865991744753664933821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131584577327829835776622547 197376865991744753664933821)
  ·
    refine ⟨74016324746904282624350183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197376865991744753664933821 74016324746904282624350183)
    ·
      refine ⟨111024487120356423936525275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74016324746904282624350183 111024487120356423936525275)
      ·
        refine ⟨166536730680534635904787913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111024487120356423936525275 166536730680534635904787913)
        ·
          refine ⟨124902548010400976928590935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166536730680534635904787913 124902548010400976928590935)
          ·
            refine ⟨187353822015601465392886403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124902548010400976928590935 187353822015601465392886403)
            ·
              refine ⟨281030733023402198089329605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187353822015601465392886403 281030733023402198089329605)
              ·
                refine ⟨52693262441887912141749301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281030733023402198089329605 52693262441887912141749301)
                ·
                  refine ⟨4939993353926991763288997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52693262441887912141749301 4939993353926991763288997)
                  ·
                    refine ⟨926248753861310955616687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939993353926991763288997 926248753861310955616687)
                    ·
                      rfl

theorem cell23_5411589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_5411589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411589 prefixEnd_5411589 := by exact prefixLift 5411589
  have htrace : WordTrace (prefixWord ++ tailWord_5411589) baseStart_5411589 baseEnd_5411589 := by
    simpa [prefixWord, tailWord_5411589, baseEnd_5411589] using wordTrace_append hprefix tailTrace_5411589
  have hstable : (prefixWord ++ tailWord_5411589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411589).length < 2 ^ (prefixWord ++ tailWord_5411589).sum := by decide
  have hdescent : baseEnd_5411589 < baseStart_5411589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411714 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5411714 : Nat := 118140960795 + 5411714 * 2 ^ 59
def prefixEnd_5411714 : Nat := 4983230072969 + 3 ^ 40 * 5411714 * 2
def baseEnd_5411714 : Nat := 2778810446665744877786987

theorem tailTrace_5411714 : CollatzResearch.WordTrace tailWord_5411714 prefixEnd_5411714 2778810446665744877786987 := by
  unfold tailWord_5411714
  simp only [CollatzResearch.WordTrace]
  refine ⟨49345356279072975003308549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131587616744194600008822797 49345356279072975003308549)
  ·
    refine ⟨9252254302326182813120353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49345356279072975003308549 9252254302326182813120353)
    ·
      refine ⟨6939190726744637109840265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9252254302326182813120353 6939190726744637109840265)
      ·
        refine ⟨5204393045058477832380199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6939190726744637109840265 5204393045058477832380199)
        ·
          refine ⟨7806589567587716748570299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204393045058477832380199 7806589567587716748570299)
          ·
            refine ⟨11709884351381575122855449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806589567587716748570299 11709884351381575122855449)
            ·
              refine ⟨8782413263536181342141587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11709884351381575122855449 8782413263536181342141587)
              ·
                refine ⟨13173619895304272013212381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8782413263536181342141587 13173619895304272013212381)
                ·
                  refine ⟨4940107460739102004954643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13173619895304272013212381 4940107460739102004954643)
                  ·
                    refine ⟨7410161191108653007431965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4940107460739102004954643 7410161191108653007431965)
                    ·
                      refine ⟨2778810446665744877786987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7410161191108653007431965 2778810446665744877786987)
                      ·
                        rfl

theorem cell23_5411714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5411714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411714 prefixEnd_5411714 := by exact prefixLift 5411714
  have htrace : WordTrace (prefixWord ++ tailWord_5411714) baseStart_5411714 baseEnd_5411714 := by
    simpa [prefixWord, tailWord_5411714, baseEnd_5411714] using wordTrace_append hprefix tailTrace_5411714
  have hstable : (prefixWord ++ tailWord_5411714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411714).length < 2 ^ (prefixWord ++ tailWord_5411714).sum := by decide
  have hdescent : baseEnd_5411714 < baseStart_5411714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411720 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_5411720 : Nat := 118140960795 + 5411720 * 2 ^ 59
def prefixEnd_5411720 : Nat := 4983230072969 + 3 ^ 40 * 5411720 * 2
def baseEnd_5411720 : Nat := 2778813527549671854311959

theorem tailTrace_5411720 : CollatzResearch.WordTrace tailWord_5411720 prefixEnd_5411720 2778813527549671854311959 := by
  unfold tailWord_5411720
  simp only [CollatzResearch.WordTrace]
  refine ⟨98690821977135081518976307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131587762636180108691968409 98690821977135081518976307)
  ·
    refine ⟨148036232965702622278464461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98690821977135081518976307 148036232965702622278464461)
    ·
      refine ⟨55513587362138483354424173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148036232965702622278464461 55513587362138483354424173)
      ·
        refine ⟨20817595260801931257909065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55513587362138483354424173 20817595260801931257909065)
        ·
          refine ⟨15613196445601448443431799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20817595260801931257909065 15613196445601448443431799)
          ·
            refine ⟨23419794668402172665147699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15613196445601448443431799 23419794668402172665147699)
            ·
              refine ⟨35129692002603258997721549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23419794668402172665147699 35129692002603258997721549)
              ·
                refine ⟨13173634500976222124145581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35129692002603258997721549 13173634500976222124145581)
                ·
                  refine ⟨4940112937866083296554593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13173634500976222124145581 4940112937866083296554593)
                  ·
                    refine ⟨3705084703399562472415945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4940112937866083296554593 3705084703399562472415945)
                    ·
                      refine ⟨2778813527549671854311959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705084703399562472415945 2778813527549671854311959)
                      ·
                        rfl

theorem cell23_5411720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_5411720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411720 prefixEnd_5411720 := by exact prefixLift 5411720
  have htrace : WordTrace (prefixWord ++ tailWord_5411720) baseStart_5411720 baseEnd_5411720 := by
    simpa [prefixWord, tailWord_5411720, baseEnd_5411720] using wordTrace_append hprefix tailTrace_5411720
  have hstable : (prefixWord ++ tailWord_5411720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411720).length < 2 ^ (prefixWord ++ tailWord_5411720).sum := by decide
  have hdescent : baseEnd_5411720 < baseStart_5411720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411730 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_5411730 : Nat := 118140960795 + 5411730 * 2 ^ 59
def prefixEnd_5411730 : Nat := 4983230072969 + 3 ^ 40 * 5411730 * 2
def baseEnd_5411730 : Nat := 926272887452072271728971

theorem tailTrace_5411730 : CollatzResearch.WordTrace tailWord_5411730 prefixEnd_5411730 926272887452072271728971 := by
  unfold tailWord_5411730
  simp only [CollatzResearch.WordTrace]
  refine ⟨49345502171058483686454161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131588005789489289830544429 49345502171058483686454161)
  ·
    refine ⟨37009126628293862764840621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49345502171058483686454161 37009126628293862764840621)
    ·
      refine ⟨13878422485610198536815233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37009126628293862764840621 13878422485610198536815233)
      ·
        refine ⟨10408816864207648902611425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13878422485610198536815233 10408816864207648902611425)
        ·
          refine ⟨7806612648155736676958569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10408816864207648902611425 7806612648155736676958569)
          ·
            refine ⟨5854959486116802507718927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7806612648155736676958569 5854959486116802507718927)
            ·
              refine ⟨8782439229175203761578391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854959486116802507718927 8782439229175203761578391)
              ·
                refine ⟨13173658843762805642367587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8782439229175203761578391 13173658843762805642367587)
                ·
                  refine ⟨19760488265644208463551381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13173658843762805642367587 19760488265644208463551381)
                  ·
                    refine ⟨926272887452072271728971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19760488265644208463551381 926272887452072271728971)
                    ·
                      rfl

theorem cell23_5411730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_5411730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411730 prefixEnd_5411730 := by exact prefixLift 5411730
  have htrace : WordTrace (prefixWord ++ tailWord_5411730) baseStart_5411730 baseEnd_5411730 := by
    simpa [prefixWord, tailWord_5411730, baseEnd_5411730] using wordTrace_append hprefix tailTrace_5411730
  have hstable : (prefixWord ++ tailWord_5411730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411730).length < 2 ^ (prefixWord ++ tailWord_5411730).sum := by decide
  have hdescent : baseEnd_5411730 < baseStart_5411730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411733 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_5411733 : Nat := 118140960795 + 5411733 * 2 ^ 59
def prefixEnd_5411733 : Nat := 4983230072969 + 3 ^ 40 * 5411733 * 2
def baseEnd_5411733 : Nat := 2778820202798180303449399

theorem tailTrace_5411733 : CollatzResearch.WordTrace tailWord_5411733 prefixEnd_5411733 2778820202798180303449399 := by
  unfold tailWord_5411733
  simp only [CollatzResearch.WordTrace]
  refine ⟨197382118103223066258175853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131588078735482044172117235 197382118103223066258175853)
  ·
    refine ⟨74018294288708649846815945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197382118103223066258175853 74018294288708649846815945)
    ·
      refine ⟨55513720716531487385111959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74018294288708649846815945 55513720716531487385111959)
      ·
        refine ⟨83270581074797231077667939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55513720716531487385111959 83270581074797231077667939)
        ·
          refine ⟨124905871612195846616501909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83270581074797231077667939 124905871612195846616501909)
          ·
            refine ⟨5854962731821680310148527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124905871612195846616501909 5854962731821680310148527)
            ·
              refine ⟨8782444097732520465222791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854962731821680310148527 8782444097732520465222791)
              ·
                refine ⟨13173666146598780697834187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8782444097732520465222791 13173666146598780697834187)
                ·
                  refine ⟨19760499219898171046751281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13173666146598780697834187 19760499219898171046751281)
                  ·
                    refine ⟨14820374414923628285063461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19760499219898171046751281 14820374414923628285063461)
                    ·
                      refine ⟨2778820202798180303449399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14820374414923628285063461 2778820202798180303449399)
                      ·
                        rfl

theorem cell23_5411733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_5411733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411733 prefixEnd_5411733 := by exact prefixLift 5411733
  have htrace : WordTrace (prefixWord ++ tailWord_5411733) baseStart_5411733 baseEnd_5411733 := by
    simpa [prefixWord, tailWord_5411733, baseEnd_5411733] using wordTrace_append hprefix tailTrace_5411733
  have hstable : (prefixWord ++ tailWord_5411733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411733).length < 2 ^ (prefixWord ++ tailWord_5411733).sum := by decide
  have hdescent : baseEnd_5411733 < baseStart_5411733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411743 : List Nat := [1, 1, 2, 5, 2, 3, 2, 7]
def baseStart_5411743 : Nat := 118140960795 + 5411743 * 2 ^ 59
def prefixEnd_5411743 : Nat := 4983230072969 + 3 ^ 40 * 5411743 * 2
def baseEnd_5411743 : Nat := 102919456948323157937939

theorem tailTrace_5411743 : CollatzResearch.WordTrace tailWord_5411743 prefixEnd_5411743 102919456948323157937939 := by
  unfold tailWord_5411743
  simp only [CollatzResearch.WordTrace]
  refine ⟨197382482833186837966039883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131588321888791225310693255 197382482833186837966039883)
  ·
    refine ⟨296073724249780256949059825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197382482833186837966039883 296073724249780256949059825)
    ·
      refine ⟨222055293187335192711794869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296073724249780256949059825 222055293187335192711794869)
      ·
        refine ⟨20817683736312674316730769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222055293187335192711794869 20817683736312674316730769)
        ·
          refine ⟨15613262802234505737548077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20817683736312674316730769 15613262802234505737548077)
          ·
            refine ⟨5854973550837939651580529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15613262802234505737548077 5854973550837939651580529)
            ·
              refine ⟨4391230163128454738685397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854973550837939651580529 4391230163128454738685397)
              ·
                refine ⟨102919456948323157937939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4391230163128454738685397 102919456948323157937939)
                ·
                  rfl

theorem cell23_5411743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 7].length) (baseStart_5411743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411743 prefixEnd_5411743 := by exact prefixLift 5411743
  have htrace : WordTrace (prefixWord ++ tailWord_5411743) baseStart_5411743 baseEnd_5411743 := by
    simpa [prefixWord, tailWord_5411743, baseEnd_5411743] using wordTrace_append hprefix tailTrace_5411743
  have hstable : (prefixWord ++ tailWord_5411743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411743).length < 2 ^ (prefixWord ++ tailWord_5411743).sum := by decide
  have hdescent : baseEnd_5411743 < baseStart_5411743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411787 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 2, 1, 3]
def baseStart_5411787 : Nat := 118140960795 + 5411787 * 2 ^ 59
def prefixEnd_5411787 : Nat := 4983230072969 + 3 ^ 40 * 5411787 * 2
def baseEnd_5411787 : Nat := 2778847930753523092174151

theorem tailTrace_5411787 : CollatzResearch.WordTrace tailWord_5411787 prefixEnd_5411787 2778847930753523092174151 := by
  unfold tailWord_5411787
  simp only [CollatzResearch.WordTrace]
  refine ⟨197384087645027433480641615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131589391763351622320427743 197384087645027433480641615)
  ·
    refine ⟨296076131467541150220962423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197384087645027433480641615 296076131467541150220962423)
    ·
      refine ⟨444114197201311725331443635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296076131467541150220962423 444114197201311725331443635)
      ·
        refine ⟨666171295801967587997165453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444114197201311725331443635 666171295801967587997165453)
        ·
          refine ⟨249814235925737845498937045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 666171295801967587997165453 249814235925737845498937045)
          ·
            refine ⟨5855021154509480753881337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 249814235925737845498937045 5855021154509480753881337)
            ·
              refine ⟨4391265865882110565411003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855021154509480753881337 4391265865882110565411003)
              ·
                refine ⟨6586898798823165848116505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391265865882110565411003 6586898798823165848116505)
                ·
                  refine ⟨4940174099117374386087379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586898798823165848116505 4940174099117374386087379)
                  ·
                    refine ⟨7410261148676061579131069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4940174099117374386087379 7410261148676061579131069)
                    ·
                      refine ⟨2778847930753523092174151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7410261148676061579131069 2778847930753523092174151)
                      ·
                        rfl

theorem cell23_5411787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 1, 3].length) (baseStart_5411787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411787 prefixEnd_5411787 := by exact prefixLift 5411787
  have htrace : WordTrace (prefixWord ++ tailWord_5411787) baseStart_5411787 baseEnd_5411787 := by
    simpa [prefixWord, tailWord_5411787, baseEnd_5411787] using wordTrace_append hprefix tailTrace_5411787
  have hstable : (prefixWord ++ tailWord_5411787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411787).length < 2 ^ (prefixWord ++ tailWord_5411787).sum := by decide
  have hdescent : baseEnd_5411787 < baseStart_5411787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411793 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 1, 4, 2]
def baseStart_5411793 : Nat := 118140960795 + 5411793 * 2 ^ 59
def prefixEnd_5411793 : Nat := 4983230072969 + 3 ^ 40 * 5411793 * 2
def baseEnd_5411793 : Nat := 2778851011637450068699123

theorem tailTrace_5411793 : CollatzResearch.WordTrace tailWord_5411793 prefixEnd_5411793 2778851011637450068699123 := by
  unfold tailWord_5411793
  simp only [CollatzResearch.WordTrace]
  refine ⟨197384306483005696505360033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131589537655337131003573355 197384306483005696505360033)
  ·
    refine ⟨148038229862254272379020025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197384306483005696505360033 148038229862254272379020025)
    ·
      refine ⟨111028672396690704284265019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148038229862254272379020025 111028672396690704284265019)
      ·
        refine ⟨166543008595036056426397529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111028672396690704284265019 166543008595036056426397529)
        ·
          refine ⟨124907256446277042319798147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166543008595036056426397529 124907256446277042319798147)
          ·
            refine ⟨187360884669415563479697221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124907256446277042319798147 187360884669415563479697221)
            ·
              refine ⟨35130165875515418152443229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187360884669415563479697221 35130165875515418152443229)
              ·
                refine ⟨13173812203318281807166211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35130165875515418152443229 13173812203318281807166211)
                ·
                  refine ⟨19760718304977422710749317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13173812203318281807166211 19760718304977422710749317)
                  ·
                    refine ⟨3705134682183266758265497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19760718304977422710749317 3705134682183266758265497)
                    ·
                      refine ⟨2778851011637450068699123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705134682183266758265497 2778851011637450068699123)
                      ·
                        rfl

theorem cell23_5411793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_5411793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411793 prefixEnd_5411793 := by exact prefixLift 5411793
  have htrace : WordTrace (prefixWord ++ tailWord_5411793) baseStart_5411793 baseEnd_5411793 := by
    simpa [prefixWord, tailWord_5411793, baseEnd_5411793] using wordTrace_append hprefix tailTrace_5411793
  have hstable : (prefixWord ++ tailWord_5411793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411793).length < 2 ^ (prefixWord ++ tailWord_5411793).sum := by decide
  have hdescent : baseEnd_5411793 < baseStart_5411793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411833 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 5]
def baseStart_5411833 : Nat := 118140960795 + 5411833 * 2 ^ 59
def prefixEnd_5411833 : Nat := 4983230072969 + 3 ^ 40 * 5411833 * 2
def baseEnd_5411833 : Nat := 308763505651514434688771

theorem tailTrace_5411833 : CollatzResearch.WordTrace tailWord_5411833 prefixEnd_5411833 308763505651514434688771 := by
  unfold tailWord_5411833
  simp only [CollatzResearch.WordTrace]
  refine ⟨197385765402860783336816153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131590510268573855557877435 197385765402860783336816153)
  ·
    refine ⟨148039324052145587502612115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197385765402860783336816153 148039324052145587502612115)
    ·
      refine ⟨222058986078218381253918173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148039324052145587502612115 222058986078218381253918173)
      ·
        refine ⟨83272119779331892970219315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222058986078218381253918173 83272119779331892970219315)
        ·
          refine ⟨124908179668997839455328973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83272119779331892970219315 124908179668997839455328973)
          ·
            refine ⟨46840567375874189795748365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124908179668997839455328973 46840567375874189795748365)
            ·
              refine ⟨17565212765952821173405637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46840567375874189795748365 17565212765952821173405637)
              ·
                refine ⟨3293477393616153970013557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17565212765952821173405637 3293477393616153970013557)
                ·
                  refine ⟨308763505651514434688771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3293477393616153970013557 308763505651514434688771)
                  ·
                    rfl

theorem cell23_5411833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 5].length) (baseStart_5411833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411833 prefixEnd_5411833 := by exact prefixLift 5411833
  have htrace : WordTrace (prefixWord ++ tailWord_5411833) baseStart_5411833 baseEnd_5411833 := by
    simpa [prefixWord, tailWord_5411833, baseEnd_5411833] using wordTrace_append hprefix tailTrace_5411833
  have hstable : (prefixWord ++ tailWord_5411833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411833).length < 2 ^ (prefixWord ++ tailWord_5411833).sum := by decide
  have hdescent : baseEnd_5411833 < baseStart_5411833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411863 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 1, 7]
def baseStart_5411863 : Nat := 118140960795 + 5411863 * 2 ^ 59
def prefixEnd_5411863 : Nat := 4983230072969 + 3 ^ 40 * 5411863 * 2
def baseEnd_5411863 : Nat := 926295651761088264941267

theorem tailTrace_5411863 : CollatzResearch.WordTrace tailWord_5411863 prefixEnd_5411863 926295651761088264941267 := by
  unfold tailWord_5411863
  simp only [CollatzResearch.WordTrace]
  refine ⟨197386859592752098460408243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131591239728501398973605495 197386859592752098460408243)
  ·
    refine ⟨296080289389128147690612365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197386859592752098460408243 296080289389128147690612365)
    ·
      refine ⟨111030108520923055383979637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296080289389128147690612365 111030108520923055383979637)
      ·
        refine ⟨10409072673836536442248091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111030108520923055383979637 10409072673836536442248091)
        ·
          refine ⟨15613609010754804663372137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10409072673836536442248091 15613609010754804663372137)
          ·
            refine ⟨11710206758066103497529103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15613609010754804663372137 11710206758066103497529103)
            ·
              refine ⟨17565310137099155246293655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11710206758066103497529103 17565310137099155246293655)
              ·
                refine ⟨26347965205648732869440483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17565310137099155246293655 26347965205648732869440483)
                ·
                  refine ⟨39521947808473099304160725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26347965205648732869440483 39521947808473099304160725)
                  ·
                    refine ⟨926295651761088264941267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39521947808473099304160725 926295651761088264941267)
                    ·
                      rfl

theorem cell23_5411863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_5411863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411863 prefixEnd_5411863 := by exact prefixLift 5411863
  have htrace : WordTrace (prefixWord ++ tailWord_5411863) baseStart_5411863 baseEnd_5411863 := by
    simpa [prefixWord, tailWord_5411863, baseEnd_5411863] using wordTrace_append hprefix tailTrace_5411863
  have hstable : (prefixWord ++ tailWord_5411863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411863).length < 2 ^ (prefixWord ++ tailWord_5411863).sum := by decide
  have hdescent : baseEnd_5411863 < baseStart_5411863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411883 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 4, 4, 2]
def baseStart_5411883 : Nat := 118140960795 + 5411883 * 2 ^ 59
def prefixEnd_5411883 : Nat := 4983230072969 + 3 ^ 40 * 5411883 * 2
def baseEnd_5411883 : Nat := 2778897224896354716573709

theorem tailTrace_5411883 : CollatzResearch.WordTrace tailWord_5411883 prefixEnd_5411883 2778897224896354716573709 := by
  unfold tailWord_5411883
  simp only [CollatzResearch.WordTrace]
  refine ⟨197387589052679641876136303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131591726035119761250757535 197387589052679641876136303)
  ·
    refine ⟨296081383579019462814204455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197387589052679641876136303 296081383579019462814204455)
    ·
      refine ⟨444122075368529194221306683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296081383579019462814204455 444122075368529194221306683)
      ·
        refine ⟨666183113052793791331960025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444122075368529194221306683 666183113052793791331960025)
        ·
          refine ⟨499637334789595343498970019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666183113052793791331960025 499637334789595343498970019)
          ·
            refine ⟨749456002184393015248455029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499637334789595343498970019 749456002184393015248455029)
            ·
              refine ⟨70261500204786845179542659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 749456002184393015248455029 70261500204786845179542659)
              ·
                refine ⟨105392250307180267769313989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70261500204786845179542659 105392250307180267769313989)
                ·
                  refine ⟨19761046932596300206746373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105392250307180267769313989 19761046932596300206746373)
                  ·
                    refine ⟨3705196299861806288764945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19761046932596300206746373 3705196299861806288764945)
                    ·
                      refine ⟨2778897224896354716573709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705196299861806288764945 2778897224896354716573709)
                      ·
                        rfl

theorem cell23_5411883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4, 2].length) (baseStart_5411883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411883 prefixEnd_5411883 := by exact prefixLift 5411883
  have htrace : WordTrace (prefixWord ++ tailWord_5411883) baseStart_5411883 baseEnd_5411883 := by
    simpa [prefixWord, tailWord_5411883, baseEnd_5411883] using wordTrace_append hprefix tailTrace_5411883
  have hstable : (prefixWord ++ tailWord_5411883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411883).length < 2 ^ (prefixWord ++ tailWord_5411883).sum := by decide
  have hdescent : baseEnd_5411883 < baseStart_5411883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411900 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_5411900 : Nat := 118140960795 + 5411900 * 2 ^ 59
def prefixEnd_5411900 : Nat := 4983230072969 + 3 ^ 40 * 5411900 * 2
def baseEnd_5411900 : Nat := 2778905954067481150061131

theorem tailTrace_5411900 : CollatzResearch.WordTrace tailWord_5411900 prefixEnd_5411900 2778905954067481150061131 := by
  unfold tailWord_5411900
  simp only [CollatzResearch.WordTrace]
  refine ⟨98694104546809026889752577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131592139395745369186336769 98694104546809026889752577)
  ·
    refine ⟨74020578410106770167314433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98694104546809026889752577 74020578410106770167314433)
    ·
      refine ⟨55515433807580077625485825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74020578410106770167314433 55515433807580077625485825)
      ·
        refine ⟨41636575355685058219114369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55515433807580077625485825 41636575355685058219114369)
        ·
          refine ⟨31227431516763793664335777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41636575355685058219114369 31227431516763793664335777)
          ·
            refine ⟨23420573637572845248251833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31227431516763793664335777 23420573637572845248251833)
            ·
              refine ⟨17565430228179633936188875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23420573637572845248251833 17565430228179633936188875)
              ·
                refine ⟨26348145342269450904283313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17565430228179633936188875 26348145342269450904283313)
                ·
                  refine ⟨19761109006702088178212485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26348145342269450904283313 19761109006702088178212485)
                  ·
                    refine ⟨3705207938756641533414841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19761109006702088178212485 3705207938756641533414841)
                    ·
                      refine ⟨2778905954067481150061131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705207938756641533414841 2778905954067481150061131)
                      ·
                        rfl

theorem cell23_5411900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_5411900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411900 prefixEnd_5411900 := by exact prefixLift 5411900
  have htrace : WordTrace (prefixWord ++ tailWord_5411900) baseStart_5411900 baseEnd_5411900 := by
    simpa [prefixWord, tailWord_5411900, baseEnd_5411900] using wordTrace_append hprefix tailTrace_5411900
  have hstable : (prefixWord ++ tailWord_5411900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411900).length < 2 ^ (prefixWord ++ tailWord_5411900).sum := by decide
  have hdescent : baseEnd_5411900 < baseStart_5411900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411934 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5411934 : Nat := 118140960795 + 5411934 * 2 ^ 59
def prefixEnd_5411934 : Nat := 4983230072969 + 3 ^ 40 * 5411934 * 2
def baseEnd_5411934 : Nat := 2778923412409734017035975

theorem tailTrace_5411934 : CollatzResearch.WordTrace tailWord_5411934 prefixEnd_5411934 2778923412409734017035975 := by
  unfold tailWord_5411934
  simp only [CollatzResearch.WordTrace]
  refine ⟨24673681146936859698280357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131592966116996585057495237 24673681146936859698280357)
  ·
    refine ⟨4626315215050661193427567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24673681146936859698280357 4626315215050661193427567)
    ·
      refine ⟨6939472822575991790141351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626315215050661193427567 6939472822575991790141351)
      ·
        refine ⟨10409209233863987685212027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6939472822575991790141351 10409209233863987685212027)
        ·
          refine ⟨15613813850795981527818041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10409209233863987685212027 15613813850795981527818041)
          ·
            refine ⟨11710360388096986145863531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15613813850795981527818041 11710360388096986145863531)
            ·
              refine ⟨17565540582145479218795297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11710360388096986145863531 17565540582145479218795297)
              ·
                refine ⟨13174155436609109414096473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17565540582145479218795297 13174155436609109414096473)
                ·
                  refine ⟨9880616577456832060572355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13174155436609109414096473 9880616577456832060572355)
                  ·
                    refine ⟨14820924866185248090858533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9880616577456832060572355 14820924866185248090858533)
                    ·
                      refine ⟨2778923412409734017035975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14820924866185248090858533 2778923412409734017035975)
                      ·
                        rfl

theorem cell23_5411934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5411934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411934 prefixEnd_5411934 := by exact prefixLift 5411934
  have htrace : WordTrace (prefixWord ++ tailWord_5411934) baseStart_5411934 baseEnd_5411934 := by
    simpa [prefixWord, tailWord_5411934, baseEnd_5411934] using wordTrace_append hprefix tailTrace_5411934
  have hstable : (prefixWord ++ tailWord_5411934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411934).length < 2 ^ (prefixWord ++ tailWord_5411934).sum := by decide
  have hdescent : baseEnd_5411934 < baseStart_5411934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411944 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 3, 4]
def baseStart_5411944 : Nat := 118140960795 + 5411944 * 2 ^ 59
def prefixEnd_5411944 : Nat := 4983230072969 + 3 ^ 40 * 5411944 * 2
def baseEnd_5411944 : Nat := 926309515738759659303643

theorem tailTrace_5411944 : CollatzResearch.WordTrace tailWord_5411944 prefixEnd_5411944 926309515738759659303643 := by
  unfold tailWord_5411944
  simp only [CollatzResearch.WordTrace]
  refine ⟨98694906952729324647053443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131593209270305766196071257 98694906952729324647053443)
  ·
    refine ⟨148042360429093986970580165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98694906952729324647053443 148042360429093986970580165)
    ·
      refine ⟨27757942580455122556983781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148042360429093986970580165 27757942580455122556983781)
      ·
        refine ⟨5204614233835335479434459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27757942580455122556983781 5204614233835335479434459)
        ·
          refine ⟨7806921350753003219151689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204614233835335479434459 7806921350753003219151689)
          ·
            refine ⟨5855191013064752414363767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7806921350753003219151689 5855191013064752414363767)
            ·
              refine ⟨8782786519597128621545651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5855191013064752414363767 8782786519597128621545651)
              ·
                refine ⟨13174179779395692932318477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8782786519597128621545651 13174179779395692932318477)
                ·
                  refine ⟨4940317417273384849619429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13174179779395692932318477 4940317417273384849619429)
                  ·
                    refine ⟨926309515738759659303643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4940317417273384849619429 926309515738759659303643)
                    ·
                      rfl

theorem cell23_5411944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_5411944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411944 prefixEnd_5411944 := by exact prefixLift 5411944
  have htrace : WordTrace (prefixWord ++ tailWord_5411944) baseStart_5411944 baseEnd_5411944 := by
    simpa [prefixWord, tailWord_5411944, baseEnd_5411944] using wordTrace_append hprefix tailTrace_5411944
  have hstable : (prefixWord ++ tailWord_5411944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411944).length < 2 ^ (prefixWord ++ tailWord_5411944).sum := by decide
  have hdescent : baseEnd_5411944 < baseStart_5411944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411957 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 6]
def baseStart_5411957 : Nat := 118140960795 + 5411957 * 2 ^ 59
def prefixEnd_5411957 : Nat := 4983230072969 + 3 ^ 40 * 5411957 * 2
def baseEnd_5411957 : Nat := 308770580273865269672041

theorem tailTrace_5411957 : CollatzResearch.WordTrace tailWord_5411957 prefixEnd_5411957 308770580273865269672041 := by
  unfold tailWord_5411957
  simp only [CollatzResearch.WordTrace]
  refine ⟨197390288054411552514330125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131593525369607701676220083 197390288054411552514330125)
  ·
    refine ⟨74021358020404332192873797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197390288054411552514330125 74021358020404332192873797)
    ·
      refine ⟨13879004628825812286163837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74021358020404332192873797 13879004628825812286163837)
      ·
        refine ⟨5204626735809679607311439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13879004628825812286163837 5204626735809679607311439)
        ·
          refine ⟨7806940103714519410967159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204626735809679607311439 7806940103714519410967159)
          ·
            refine ⟨11710410155571779116450739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806940103714519410967159 11710410155571779116450739)
            ·
              refine ⟨17565615233357668674676109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11710410155571779116450739 17565615233357668674676109)
              ·
                refine ⟨6587105712509125753003541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17565615233357668674676109 6587105712509125753003541)
                ·
                  refine ⟨308770580273865269672041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6587105712509125753003541 308770580273865269672041)
                  ·
                    rfl

theorem cell23_5411957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_5411957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411957 prefixEnd_5411957 := by exact prefixLift 5411957
  have htrace : WordTrace (prefixWord ++ tailWord_5411957) baseStart_5411957 baseEnd_5411957 := by
    simpa [prefixWord, tailWord_5411957, baseEnd_5411957] using wordTrace_append hprefix tailTrace_5411957
  have hstable : (prefixWord ++ tailWord_5411957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411957).length < 2 ^ (prefixWord ++ tailWord_5411957).sum := by decide
  have hdescent : baseEnd_5411957 < baseStart_5411957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5411977 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 2, 3, 2]
def baseStart_5411977 : Nat := 118140960795 + 5411977 * 2 ^ 59
def prefixEnd_5411977 : Nat := 4983230072969 + 3 ^ 40 * 5411977 * 2
def baseEnd_5411977 : Nat := 2778945492077877348798277

theorem tailTrace_5411977 : CollatzResearch.WordTrace tailWord_5411977 prefixEnd_5411977 2778945492077877348798277 := by
  unfold tailWord_5411977
  simp only [CollatzResearch.WordTrace]
  refine ⟨197391017514339095930058185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131594011676226063953372123 197391017514339095930058185)
  ·
    refine ⟨148043263135754321947543639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197391017514339095930058185 148043263135754321947543639)
    ·
      refine ⟨222064894703631482921315459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148043263135754321947543639 222064894703631482921315459)
      ·
        refine ⟨333097342055447224381973189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222064894703631482921315459 333097342055447224381973189)
        ·
          refine ⟨62455751635396354571619973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333097342055447224381973189 62455751635396354571619973)
          ·
            refine ⟨11710453431636816482178745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62455751635396354571619973 11710453431636816482178745)
            ·
              refine ⟨8782840073727612361634059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11710453431636816482178745 8782840073727612361634059)
              ·
                refine ⟨13174260110591418542451089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8782840073727612361634059 13174260110591418542451089)
                ·
                  refine ⟨9880695082943563906838317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13174260110591418542451089 9880695082943563906838317)
                  ·
                    refine ⟨3705260656103836465064369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9880695082943563906838317 3705260656103836465064369)
                    ·
                      refine ⟨2778945492077877348798277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705260656103836465064369 2778945492077877348798277)
                      ·
                        rfl

theorem cell23_5411977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3, 2].length) (baseStart_5411977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5411977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5411977 prefixEnd_5411977 := by exact prefixLift 5411977
  have htrace : WordTrace (prefixWord ++ tailWord_5411977) baseStart_5411977 baseEnd_5411977 := by
    simpa [prefixWord, tailWord_5411977, baseEnd_5411977] using wordTrace_append hprefix tailTrace_5411977
  have hstable : (prefixWord ++ tailWord_5411977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5411977).length < 2 ^ (prefixWord ++ tailWord_5411977).sum := by decide
  have hdescent : baseEnd_5411977 < baseStart_5411977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5411977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412017 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 2, 4]
def baseStart_5412017 : Nat := 118140960795 + 5412017 * 2 ^ 59
def prefixEnd_5412017 : Nat := 4983230072969 + 3 ^ 40 * 5412017 * 2
def baseEnd_5412017 : Nat := 926322010434685730766031

theorem tailTrace_5412017 : CollatzResearch.WordTrace tailWord_5412017 prefixEnd_5412017 926322010434685730766031 := by
  unfold tailWord_5412017
  simp only [CollatzResearch.WordTrace]
  refine ⟨197392476434194182761514305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131594984289462788507676203 197392476434194182761514305)
  ·
    refine ⟨148044357325645637071135729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197392476434194182761514305 148044357325645637071135729)
    ·
      refine ⟨111033267994234227803351797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148044357325645637071135729 111033267994234227803351797)
      ·
        refine ⟨10409368874459458856564231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111033267994234227803351797 10409368874459458856564231)
        ·
          refine ⟨15614053311689188284846347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10409368874459458856564231 15614053311689188284846347)
          ·
            refine ⟨23421079967533782427269521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15614053311689188284846347 23421079967533782427269521)
            ·
              refine ⟨17565809975650336820452141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23421079967533782427269521 17565809975650336820452141)
              ·
                refine ⟨6587178740868876307669553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17565809975650336820452141 6587178740868876307669553)
                ·
                  refine ⟨4940384055651657230752165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6587178740868876307669553 4940384055651657230752165)
                  ·
                    refine ⟨926322010434685730766031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4940384055651657230752165 926322010434685730766031)
                    ·
                      rfl

theorem cell23_5412017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_5412017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412017 prefixEnd_5412017 := by exact prefixLift 5412017
  have htrace : WordTrace (prefixWord ++ tailWord_5412017) baseStart_5412017 baseEnd_5412017 := by
    simpa [prefixWord, tailWord_5412017, baseEnd_5412017] using wordTrace_append hprefix tailTrace_5412017
  have hstable : (prefixWord ++ tailWord_5412017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412017).length < 2 ^ (prefixWord ++ tailWord_5412017).sum := by decide
  have hdescent : baseEnd_5412017 < baseStart_5412017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412040 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_5412040 : Nat := 118140960795 + 5412040 * 2 ^ 59
def prefixEnd_5412040 : Nat := 4983230072969 + 3 ^ 40 * 5412040 * 2
def baseEnd_5412040 : Nat := 2778977841359110602310487

theorem tailTrace_5412040 : CollatzResearch.WordTrace tailWord_5412040 prefixEnd_5412040 2778977841359110602310487 := by
  unfold tailWord_5412040
  simp only [CollatzResearch.WordTrace]
  refine ⟨98696657656555428844800787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131595543542073905126401049 98696657656555428844800787)
  ·
    refine ⟨148044986484833143267201181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98696657656555428844800787 148044986484833143267201181)
    ·
      refine ⟨55516869931812428725200443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148044986484833143267201181 55516869931812428725200443)
      ·
        refine ⟨83275304897718643087800665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55516869931812428725200443 83275304897718643087800665)
        ·
          refine ⟨62456478673288982315850499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83275304897718643087800665 62456478673288982315850499)
          ·
            refine ⟨93684718009933473473775749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62456478673288982315850499 93684718009933473473775749)
            ·
              refine ⟨17565884626862526276332953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93684718009933473473775749 17565884626862526276332953)
              ·
                refine ⟨13174413470146894707249715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17565884626862526276332953 13174413470146894707249715)
                ·
                  refine ⟨19761620205220342060874573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13174413470146894707249715 19761620205220342060874573)
                  ·
                    refine ⟨7410607576957628272827965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19761620205220342060874573 7410607576957628272827965)
                    ·
                      refine ⟨2778977841359110602310487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7410607576957628272827965 2778977841359110602310487)
                      ·
                        rfl

theorem cell23_5412040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_5412040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412040 prefixEnd_5412040 := by exact prefixLift 5412040
  have htrace : WordTrace (prefixWord ++ tailWord_5412040) baseStart_5412040 baseEnd_5412040 := by
    simpa [prefixWord, tailWord_5412040, baseEnd_5412040] using wordTrace_append hprefix tailTrace_5412040
  have hstable : (prefixWord ++ tailWord_5412040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412040).length < 2 ^ (prefixWord ++ tailWord_5412040).sum := by decide
  have hdescent : baseEnd_5412040 < baseStart_5412040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412063 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_5412063 : Nat := 118140960795 + 5412063 * 2 ^ 59
def prefixEnd_5412063 : Nat := 4983230072969 + 3 ^ 40 * 5412063 * 2
def baseEnd_5412063 : Nat := 2778989651414164012322881

theorem tailTrace_5412063 : CollatzResearch.WordTrace tailWord_5412063 prefixEnd_5412063 2778989651414164012322881 := by
  unfold tailWord_5412063
  simp only [CollatzResearch.WordTrace]
  refine ⟨197394154192027532617688843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131596102794685021745125895 197394154192027532617688843)
  ·
    refine ⟨296091231288041298926533265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197394154192027532617688843 296091231288041298926533265)
    ·
      refine ⟨222068423466030974194899949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296091231288041298926533265 222068423466030974194899949)
      ·
        refine ⟨83275658799761615323087481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222068423466030974194899949 83275658799761615323087481)
        ·
          refine ⟨62456744099821211492315611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83275658799761615323087481 62456744099821211492315611)
          ·
            refine ⟨93685116149731817238473417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62456744099821211492315611 93685116149731817238473417)
            ·
              refine ⟨70263837112298862928855063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93685116149731817238473417 70263837112298862928855063)
              ·
                refine ⟨105395755668448294393282595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70263837112298862928855063 105395755668448294393282595)
                ·
                  refine ⟨158093633502672441589923893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105395755668448294393282595 158093633502672441589923893)
                  ·
                    refine ⟨14821278140875541399055365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 158093633502672441589923893 14821278140875541399055365)
                    ·
                      refine ⟨2778989651414164012322881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14821278140875541399055365 2778989651414164012322881)
                      ·
                        rfl

theorem cell23_5412063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_5412063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412063 prefixEnd_5412063 := by exact prefixLift 5412063
  have htrace : WordTrace (prefixWord ++ tailWord_5412063) baseStart_5412063 baseEnd_5412063 := by
    simpa [prefixWord, tailWord_5412063, baseEnd_5412063] using wordTrace_append hprefix tailTrace_5412063
  have hstable : (prefixWord ++ tailWord_5412063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412063).length < 2 ^ (prefixWord ++ tailWord_5412063).sum := by decide
  have hdescent : baseEnd_5412063 < baseStart_5412063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412100 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5412100 : Nat := 118140960795 + 5412100 * 2 ^ 59
def prefixEnd_5412100 : Nat := 4983230072969 + 3 ^ 40 * 5412100 * 2
def baseEnd_5412100 : Nat := 2779008650198380367560211

theorem tailTrace_5412100 : CollatzResearch.WordTrace tailWord_5412100 prefixEnd_5412100 2779008650198380367560211 := by
  unfold tailWord_5412100
  simp only [CollatzResearch.WordTrace]
  refine ⟨98697751846446743968392877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131597002461928991957857169 98697751846446743968392877)
  ·
    refine ⟨37011656942417528988147329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98697751846446743968392877 37011656942417528988147329)
    ·
      refine ⟨27758742706813146741110497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37011656942417528988147329 27758742706813146741110497)
      ·
        refine ⟨20819057030109860055832873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27758742706813146741110497 20819057030109860055832873)
        ·
          refine ⟨15614292772582395041874655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20819057030109860055832873 15614292772582395041874655)
          ·
            refine ⟨23421439158873592562811983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15614292772582395041874655 23421439158873592562811983)
            ·
              refine ⟨35132158738310388844217975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23421439158873592562811983 35132158738310388844217975)
              ·
                refine ⟨52698238107465583266326963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35132158738310388844217975 52698238107465583266326963)
                ·
                  refine ⟨79047357161198374899490445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52698238107465583266326963 79047357161198374899490445)
                  ·
                    refine ⟨29642758935449390587308917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79047357161198374899490445 29642758935449390587308917)
                    ·
                      refine ⟨2779008650198380367560211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29642758935449390587308917 2779008650198380367560211)
                      ·
                        rfl

theorem cell23_5412100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5412100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412100 prefixEnd_5412100 := by exact prefixLift 5412100
  have htrace : WordTrace (prefixWord ++ tailWord_5412100) baseStart_5412100 baseEnd_5412100 := by
    simpa [prefixWord, tailWord_5412100, baseEnd_5412100] using wordTrace_append hprefix tailTrace_5412100
  have hstable : (prefixWord ++ tailWord_5412100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412100).length < 2 ^ (prefixWord ++ tailWord_5412100).sum := by decide
  have hdescent : baseEnd_5412100 < baseStart_5412100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412113 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_5412113 : Nat := 118140960795 + 5412113 * 2 ^ 59
def prefixEnd_5412113 : Nat := 4983230072969 + 3 ^ 40 * 5412113 * 2
def baseEnd_5412113 : Nat := 2779015325446888816697651

theorem tailTrace_5412113 : CollatzResearch.WordTrace tailWord_5412113 prefixEnd_5412113 2779015325446888816697651 := by
  unfold tailWord_5412113
  simp only [CollatzResearch.WordTrace]
  refine ⟨197395977841846391157008993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131597318561230927438005995 197395977841846391157008993)
  ·
    refine ⟨148046983381384793367756745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197395977841846391157008993 148046983381384793367756745)
    ·
      refine ⟨111035237536038595025817559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148046983381384793367756745 111035237536038595025817559)
      ·
        refine ⟨166552856304057892538726339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111035237536038595025817559 166552856304057892538726339)
        ·
          refine ⟨249829284456086838808089509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166552856304057892538726339 249829284456086838808089509)
          ·
            refine ⟨46842990835516282276516783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249829284456086838808089509 46842990835516282276516783)
            ·
              refine ⟨70264486253274423414775175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46842990835516282276516783 70264486253274423414775175)
              ·
                refine ⟨105396729379911635122162763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70264486253274423414775175 105396729379911635122162763)
                ·
                  refine ⟨158095094069867452683244145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105396729379911635122162763 158095094069867452683244145)
                  ·
                    refine ⟨118571320552400589512433109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158095094069867452683244145 118571320552400589512433109)
                    ·
                      refine ⟨2779015325446888816697651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118571320552400589512433109 2779015325446888816697651)
                      ·
                        rfl

theorem cell23_5412113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_5412113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412113 prefixEnd_5412113 := by exact prefixLift 5412113
  have htrace : WordTrace (prefixWord ++ tailWord_5412113) baseStart_5412113 baseEnd_5412113 := by
    simpa [prefixWord, tailWord_5412113, baseEnd_5412113] using wordTrace_append hprefix tailTrace_5412113
  have hstable : (prefixWord ++ tailWord_5412113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412113).length < 2 ^ (prefixWord ++ tailWord_5412113).sum := by decide
  have hdescent : baseEnd_5412113 < baseStart_5412113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412120 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 7]
def baseStart_5412120 : Nat := 118140960795 + 5412120 * 2 ^ 59
def prefixEnd_5412120 : Nat := 4983230072969 + 3 ^ 40 * 5412120 * 2
def baseEnd_5412120 : Nat := 308779879979052254367791

theorem tailTrace_5412120 : CollatzResearch.WordTrace tailWord_5412120 prefixEnd_5412120 308779879979052254367791 := by
  unfold tailWord_5412120
  simp only [CollatzResearch.WordTrace]
  refine ⟨98698116576410515676256907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131597488768547354235009209 98698116576410515676256907)
  ·
    refine ⟨148047174864615773514385361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98698116576410515676256907 148047174864615773514385361)
    ·
      refine ⟨111035381148461830135789021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148047174864615773514385361 111035381148461830135789021)
      ·
        refine ⟨41638267930673186300920883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111035381148461830135789021 41638267930673186300920883)
        ·
          refine ⟨62457401896009779451381325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41638267930673186300920883 62457401896009779451381325)
          ·
            refine ⟨23421525711003667294267997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62457401896009779451381325 23421525711003667294267997)
            ·
              refine ⟨8783072141626375235350499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23421525711003667294267997 8783072141626375235350499)
              ·
                refine ⟨13174608212439562853025749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783072141626375235350499 13174608212439562853025749)
                ·
                  refine ⟨308779879979052254367791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13174608212439562853025749 308779879979052254367791)
                  ·
                    rfl

theorem cell23_5412120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 7].length) (baseStart_5412120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412120 prefixEnd_5412120 := by exact prefixLift 5412120
  have htrace : WordTrace (prefixWord ++ tailWord_5412120) baseStart_5412120 baseEnd_5412120 := by
    simpa [prefixWord, tailWord_5412120, baseEnd_5412120] using wordTrace_append hprefix tailTrace_5412120
  have hstable : (prefixWord ++ tailWord_5412120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412120).length < 2 ^ (prefixWord ++ tailWord_5412120).sum := by decide
  have hdescent : baseEnd_5412120 < baseStart_5412120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412131 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 2, 2, 2]
def baseStart_5412131 : Nat := 118140960795 + 5412131 * 2 ^ 59
def prefixEnd_5412131 : Nat := 4983230072969 + 3 ^ 40 * 5412131 * 2
def baseEnd_5412131 : Nat := 2779024568098669746272569

theorem tailTrace_5412131 : CollatzResearch.WordTrace tailWord_5412131 prefixEnd_5412131 2779024568098669746272569 := by
  unfold tailWord_5412131
  simp only [CollatzResearch.WordTrace]
  refine ⟨197396634355781180231164247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131597756237187453487442831 197396634355781180231164247)
  ·
    refine ⟨296094951533671770346746371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197396634355781180231164247 296094951533671770346746371)
    ·
      refine ⟨444142427300507655520119557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296094951533671770346746371 444142427300507655520119557)
      ·
        refine ⟨83276705118845185410022417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 444142427300507655520119557 83276705118845185410022417)
        ·
          refine ⟨62457528839133889057516813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83276705118845185410022417 62457528839133889057516813)
          ·
            refine ⟨23421573314675208396568805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62457528839133889057516813 23421573314675208396568805)
            ·
              refine ⟨4391544996501601574356651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23421573314675208396568805 4391544996501601574356651)
              ·
                refine ⟨6587317494752402361534977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391544996501601574356651 6587317494752402361534977)
                ·
                  refine ⟨4940488121064301771151233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6587317494752402361534977 4940488121064301771151233)
                  ·
                    refine ⟨3705366090798226328363425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4940488121064301771151233 3705366090798226328363425)
                    ·
                      refine ⟨2779024568098669746272569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705366090798226328363425 2779024568098669746272569)
                      ·
                        rfl

theorem cell23_5412131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_5412131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412131 prefixEnd_5412131 := by exact prefixLift 5412131
  have htrace : WordTrace (prefixWord ++ tailWord_5412131) baseStart_5412131 baseEnd_5412131 := by
    simpa [prefixWord, tailWord_5412131, baseEnd_5412131] using wordTrace_append hprefix tailTrace_5412131
  have hstable : (prefixWord ++ tailWord_5412131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412131).length < 2 ^ (prefixWord ++ tailWord_5412131).sum := by decide
  have hdescent : baseEnd_5412131 < baseStart_5412131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412143 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_5412143 : Nat := 118140960795 + 5412143 * 2 ^ 59
def prefixEnd_5412143 : Nat := 4983230072969 + 3 ^ 40 * 5412143 * 2
def baseEnd_5412143 : Nat := 2779030729866523699322513

theorem tailTrace_5412143 : CollatzResearch.WordTrace tailWord_5412143 prefixEnd_5412143 2779030729866523699322513 := by
  unfold tailWord_5412143
  simp only [CollatzResearch.WordTrace]
  refine ⟨197397072031737706280601083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131598048021158470853734055 197397072031737706280601083)
  ·
    refine ⟨296095608047606559420901625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197397072031737706280601083 296095608047606559420901625)
    ·
      refine ⟨222071706035704919565676219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296095608047606559420901625 222071706035704919565676219)
      ·
        refine ⟨333107559053557379348514329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222071706035704919565676219 333107559053557379348514329)
        ·
          refine ⟨249830669290168034511385747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333107559053557379348514329 249830669290168034511385747)
          ·
            refine ⟨374746003935252051767078621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249830669290168034511385747 374746003935252051767078621)
            ·
              refine ⟨140529751475719519412654483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374746003935252051767078621 140529751475719519412654483)
              ·
                refine ⟨210794627213579279118981725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140529751475719519412654483 210794627213579279118981725)
                ·
                  refine ⟨79047985205092229669618147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210794627213579279118981725 79047985205092229669618147)
                  ·
                    refine ⟨118571977807638344504427221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79047985205092229669618147 118571977807638344504427221)
                    ·
                      refine ⟨2779030729866523699322513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118571977807638344504427221 2779030729866523699322513)
                      ·
                        rfl

theorem cell23_5412143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_5412143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412143 prefixEnd_5412143 := by exact prefixLift 5412143
  have htrace : WordTrace (prefixWord ++ tailWord_5412143) baseStart_5412143 baseEnd_5412143 := by
    simpa [prefixWord, tailWord_5412143, baseEnd_5412143] using wordTrace_append hprefix tailTrace_5412143
  have hstable : (prefixWord ++ tailWord_5412143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412143).length < 2 ^ (prefixWord ++ tailWord_5412143).sum := by decide
  have hdescent : baseEnd_5412143 < baseStart_5412143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412197 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_5412197 : Nat := 118140960795 + 5412197 * 2 ^ 59
def prefixEnd_5412197 : Nat := 4983230072969 + 3 ^ 40 * 5412197 * 2
def baseEnd_5412197 : Nat := 926352819273955496015755

theorem tailTrace_5412197 : CollatzResearch.WordTrace tailWord_5412197 prefixEnd_5412197 926352819273955496015755 := by
  unfold tailWord_5412197
  simp only [CollatzResearch.WordTrace]
  refine ⟨197399041573542073503066845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131599361049028049002044563 197399041573542073503066845)
  ·
    refine ⟨74024640590078277563650067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197399041573542073503066845 74024640590078277563650067)
    ·
      refine ⟨111036960885117416345475101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74024640590078277563650067 111036960885117416345475101)
      ·
        refine ⟨41638860331919031129553163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111036960885117416345475101 41638860331919031129553163)
        ·
          refine ⟨62458290497878546694329745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41638860331919031129553163 62458290497878546694329745)
          ·
            refine ⟨46843717873408910020747309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62458290497878546694329745 46843717873408910020747309)
            ·
              refine ⟨17566394202528341257780241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46843717873408910020747309 17566394202528341257780241)
              ·
                refine ⟨13174795651896255943335181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17566394202528341257780241 13174795651896255943335181)
                ·
                  refine ⟨4940548369461095978750693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13174795651896255943335181 4940548369461095978750693)
                  ·
                    refine ⟨926352819273955496015755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4940548369461095978750693 926352819273955496015755)
                    ·
                      rfl

theorem cell23_5412197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_5412197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412197 prefixEnd_5412197 := by exact prefixLift 5412197
  have htrace : WordTrace (prefixWord ++ tailWord_5412197) baseStart_5412197 baseEnd_5412197 := by
    simpa [prefixWord, tailWord_5412197, baseEnd_5412197] using wordTrace_append hprefix tailTrace_5412197
  have hstable : (prefixWord ++ tailWord_5412197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412197).length < 2 ^ (prefixWord ++ tailWord_5412197).sum := by decide
  have hdescent : baseEnd_5412197 < baseStart_5412197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412204 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_5412204 : Nat := 118140960795 + 5412204 * 2 ^ 59
def prefixEnd_5412204 : Nat := 4983230072969 + 3 ^ 40 * 5412204 * 2
def baseEnd_5412204 : Nat := 2779062052186447960659733

theorem tailTrace_5412204 : CollatzResearch.WordTrace tailWord_5412204 prefixEnd_5412204 2779062052186447960659733 := by
  unfold tailWord_5412204
  simp only [CollatzResearch.WordTrace]
  refine ⟨98699648442258356849285833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131599531256344475799047777 98699648442258356849285833)
  ·
    refine ⟨74024736331693767636964375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98699648442258356849285833 74024736331693767636964375)
    ·
      refine ⟨111037104497540651455446563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74024736331693767636964375 111037104497540651455446563)
      ·
        refine ⟨166555656746310977183169845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111037104497540651455446563 166555656746310977183169845)
        ·
          refine ⟨15614592819966654110922173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166555656746310977183169845 15614592819966654110922173)
          ·
            refine ⟨5855472307487495291595815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15614592819966654110922173 5855472307487495291595815)
            ·
              refine ⟨8783208461231242937393723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5855472307487495291595815 8783208461231242937393723)
              ·
                refine ⟨13174812691846864406090585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783208461231242937393723 13174812691846864406090585)
                ·
                  refine ⟨9881109518885148304567939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13174812691846864406090585 9881109518885148304567939)
                  ·
                    refine ⟨14821664278327722456851909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9881109518885148304567939 14821664278327722456851909)
                    ·
                      refine ⟨2779062052186447960659733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14821664278327722456851909 2779062052186447960659733)
                      ·
                        rfl

theorem cell23_5412204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_5412204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412204 prefixEnd_5412204 := by exact prefixLift 5412204
  have htrace : WordTrace (prefixWord ++ tailWord_5412204) baseStart_5412204 baseEnd_5412204 := by
    simpa [prefixWord, tailWord_5412204, baseEnd_5412204] using wordTrace_append hprefix tailTrace_5412204
  have hstable : (prefixWord ++ tailWord_5412204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412204).length < 2 ^ (prefixWord ++ tailWord_5412204).sum := by decide
  have hdescent : baseEnd_5412204 < baseStart_5412204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412210 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_5412210 : Nat := 118140960795 + 5412210 * 2 ^ 59
def prefixEnd_5412210 : Nat := 4983230072969 + 3 ^ 40 * 5412210 * 2
def baseEnd_5412210 : Nat := 308785014785597215242745

theorem tailTrace_5412210 : CollatzResearch.WordTrace tailWord_5412210 prefixEnd_5412210 308785014785597215242745 := by
  unfold tailWord_5412210
  simp only [CollatzResearch.WordTrace]
  refine ⟨49349878930623744180822521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131599677148329984482193389 49349878930623744180822521)
  ·
    refine ⟨37012409197967808135616891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49349878930623744180822521 37012409197967808135616891)
    ·
      refine ⟨55518613796951712203425337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37012409197967808135616891 55518613796951712203425337)
      ·
        refine ⟨41638960347713784152569003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55518613796951712203425337 41638960347713784152569003)
        ·
          refine ⟨62458440521570676228853505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41638960347713784152569003 62458440521570676228853505)
          ·
            refine ⟨46843830391178007171640129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62458440521570676228853505 46843830391178007171640129)
            ·
              refine ⟨35132872793383505378730097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46843830391178007171640129 35132872793383505378730097)
              ·
                refine ⟨26349654595037629034047573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35132872793383505378730097 26349654595037629034047573)
                ·
                  refine ⟨308785014785597215242745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26349654595037629034047573 308785014785597215242745)
                  ·
                    rfl

theorem cell23_5412210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_5412210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412210 prefixEnd_5412210 := by exact prefixLift 5412210
  have htrace : WordTrace (prefixWord ++ tailWord_5412210) baseStart_5412210 baseEnd_5412210 := by
    simpa [prefixWord, tailWord_5412210, baseEnd_5412210] using wordTrace_append hprefix tailTrace_5412210
  have hstable : (prefixWord ++ tailWord_5412210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412210).length < 2 ^ (prefixWord ++ tailWord_5412210).sum := by decide
  have hdescent : baseEnd_5412210 < baseStart_5412210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412227 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 6]
def baseStart_5412227 : Nat := 118140960795 + 5412227 * 2 ^ 59
def prefixEnd_5412227 : Nat := 4983230072969 + 3 ^ 40 * 5412227 * 2
def baseEnd_5412227 : Nat := 308785984693500152296903

theorem tailTrace_5412227 : CollatzResearch.WordTrace tailWord_5412227 prefixEnd_5412227 308785984693500152296903 := by
  unfold tailWord_5412227
  simp only [CollatzResearch.WordTrace]
  refine ⟨197400135763433388626658935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131600090508955592417772623 197400135763433388626658935)
  ·
    refine ⟨296100203645150082939988403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197400135763433388626658935 296100203645150082939988403)
    ·
      refine ⟨444150305467725124409982605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296100203645150082939988403 444150305467725124409982605)
      ·
        refine ⟨166556364550396921653743477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444150305467725124409982605 166556364550396921653743477)
        ·
          refine ⟨15614659176599711405038451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166556364550396921653743477 15614659176599711405038451)
          ·
            refine ⟨23421988764899567107557677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15614659176599711405038451 23421988764899567107557677)
            ·
              refine ⟨8783245786837337665334129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23421988764899567107557677 8783245786837337665334129)
              ·
                refine ⟨6587434340128003249000597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8783245786837337665334129 6587434340128003249000597)
                ·
                  refine ⟨308785984693500152296903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6587434340128003249000597 308785984693500152296903)
                  ·
                    rfl

theorem cell23_5412227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 6].length) (baseStart_5412227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412227 prefixEnd_5412227 := by exact prefixLift 5412227
  have htrace : WordTrace (prefixWord ++ tailWord_5412227) baseStart_5412227 baseEnd_5412227 := by
    simpa [prefixWord, tailWord_5412227, baseEnd_5412227] using wordTrace_append hprefix tailTrace_5412227
  have hstable : (prefixWord ++ tailWord_5412227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412227).length < 2 ^ (prefixWord ++ tailWord_5412227).sum := by decide
  have hdescent : baseEnd_5412227 < baseStart_5412227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412281 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5412281 : Nat := 118140960795 + 5412281 * 2 ^ 59
def prefixEnd_5412281 : Nat := 4983230072969 + 3 ^ 40 * 5412281 * 2
def baseEnd_5412281 : Nat := 2779101590196844159396879

theorem tailTrace_5412281 : CollatzResearch.WordTrace tailWord_5412281 prefixEnd_5412281 2779101590196844159396879 := by
  unfold tailWord_5412281
  simp only [CollatzResearch.WordTrace]
  refine ⟨197402105305237755849124697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131601403536825170566083131 197402105305237755849124697)
  ·
    refine ⟨148051578978928316886843523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197402105305237755849124697 148051578978928316886843523)
    ·
      refine ⟨222077368468392475330265285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148051578978928316886843523 222077368468392475330265285)
      ·
        refine ⟨41639506587823589124424741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222077368468392475330265285 41639506587823589124424741)
        ·
          refine ⟨7807407485216922960829639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41639506587823589124424741 7807407485216922960829639)
          ·
            refine ⟨11711111227825384441244459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807407485216922960829639 11711111227825384441244459)
            ·
              refine ⟨17566666841738076661866689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711111227825384441244459 17566666841738076661866689)
              ·
                refine ⟨13175000131303557496400017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17566666841738076661866689 13175000131303557496400017)
                ·
                  refine ⟨9881250098477668122300013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13175000131303557496400017 9881250098477668122300013)
                  ·
                    refine ⟨3705468786929125545862505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9881250098477668122300013 3705468786929125545862505)
                    ·
                      refine ⟨2779101590196844159396879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705468786929125545862505 2779101590196844159396879)
                      ·
                        rfl

theorem cell23_5412281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5412281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412281 prefixEnd_5412281 := by exact prefixLift 5412281
  have htrace : WordTrace (prefixWord ++ tailWord_5412281) baseStart_5412281 baseEnd_5412281 := by
    simpa [prefixWord, tailWord_5412281, baseEnd_5412281] using wordTrace_append hprefix tailTrace_5412281
  have hstable : (prefixWord ++ tailWord_5412281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412281).length < 2 ^ (prefixWord ++ tailWord_5412281).sum := by decide
  have hdescent : baseEnd_5412281 < baseStart_5412281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412297 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_5412297 : Nat := 118140960795 + 5412297 * 2 ^ 59
def prefixEnd_5412297 : Nat := 4983230072969 + 3 ^ 40 * 5412297 * 2
def baseEnd_5412297 : Nat := 2779109805887316096796805

theorem tailTrace_5412297 : CollatzResearch.WordTrace tailWord_5412297 prefixEnd_5412297 2779109805887316096796805 := by
  unfold tailWord_5412297
  simp only [CollatzResearch.WordTrace]
  refine ⟨197402688873179790581707145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131601792582119860387804763 197402688873179790581707145)
  ·
    refine ⟨148052016654884842936280359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197402688873179790581707145 148052016654884842936280359)
    ·
      refine ⟨222078024982327264404420539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148052016654884842936280359 222078024982327264404420539)
      ·
        refine ⟨333117037473490896606630809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222078024982327264404420539 333117037473490896606630809)
        ·
          refine ⟨249837778105118172454973107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333117037473490896606630809 249837778105118172454973107)
          ·
            refine ⟨374756667157677258682459661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249837778105118172454973107 374756667157677258682459661)
            ·
              refine ⟨140533750184128972005922373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374756667157677258682459661 140533750184128972005922373)
              ·
                refine ⟨26350078159524182251110445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140533750184128972005922373 26350078159524182251110445)
                ·
                  refine ⟨9881279309821568344166417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26350078159524182251110445 9881279309821568344166417)
                  ·
                    refine ⟨7410959482366176258124813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9881279309821568344166417 7410959482366176258124813)
                    ·
                      refine ⟨2779109805887316096796805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7410959482366176258124813 2779109805887316096796805)
                      ·
                        rfl

theorem cell23_5412297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_5412297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412297 prefixEnd_5412297 := by exact prefixLift 5412297
  have htrace : WordTrace (prefixWord ++ tailWord_5412297) baseStart_5412297 baseEnd_5412297 := by
    simpa [prefixWord, tailWord_5412297, baseEnd_5412297] using wordTrace_append hprefix tailTrace_5412297
  have hstable : (prefixWord ++ tailWord_5412297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412297).length < 2 ^ (prefixWord ++ tailWord_5412297).sum := by decide
  have hdescent : baseEnd_5412297 < baseStart_5412297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412308 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_5412308 : Nat := 118140960795 + 5412308 * 2 ^ 59
def prefixEnd_5412308 : Nat := 4983230072969 + 3 ^ 40 * 5412308 * 2
def baseEnd_5412308 : Nat := 926371818058171851253085

theorem tailTrace_5412308 : CollatzResearch.WordTrace tailWord_5412308 prefixEnd_5412308 926371818058171851253085 := by
  unfold tailWord_5412308
  simp only [CollatzResearch.WordTrace]
  refine ⟨98701545038069969730178789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131602060050759959640238385 98701545038069969730178789)
  ·
    refine ⟨18506539694638119324408523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98701545038069969730178789 18506539694638119324408523)
    ·
      refine ⟨27759809541957178986612785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18506539694638119324408523 27759809541957178986612785)
      ·
        refine ⟨20819857156467884239959589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27759809541957178986612785 20819857156467884239959589)
        ·
          refine ⟨3903723216837728294992423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20819857156467884239959589 3903723216837728294992423)
          ·
            refine ⟨5855584825256592442488635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903723216837728294992423 5855584825256592442488635)
            ·
              refine ⟨8783377237884888663732953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5855584825256592442488635 8783377237884888663732953)
              ·
                refine ⟨6587532928413666497799715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8783377237884888663732953 6587532928413666497799715)
                ·
                  refine ⟨9881299392620499746699573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587532928413666497799715 9881299392620499746699573)
                  ·
                    refine ⟨926371818058171851253085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9881299392620499746699573 926371818058171851253085)
                    ·
                      rfl

theorem cell23_5412308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_5412308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412308 prefixEnd_5412308 := by exact prefixLift 5412308
  have htrace : WordTrace (prefixWord ++ tailWord_5412308) baseStart_5412308 baseEnd_5412308 := by
    simpa [prefixWord, tailWord_5412308, baseEnd_5412308] using wordTrace_append hprefix tailTrace_5412308
  have hstable : (prefixWord ++ tailWord_5412308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412308).length < 2 ^ (prefixWord ++ tailWord_5412308).sum := by decide
  have hdescent : baseEnd_5412308 < baseStart_5412308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412314 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_5412314 : Nat := 118140960795 + 5412314 * 2 ^ 59
def prefixEnd_5412314 : Nat := 4983230072969 + 3 ^ 40 * 5412314 * 2
def baseEnd_5412314 : Nat := 2779118535058442530284227

theorem tailTrace_5412314 : CollatzResearch.WordTrace tailWord_5412314 prefixEnd_5412314 2779118535058442530284227 := by
  unfold tailWord_5412314
  simp only [CollatzResearch.WordTrace]
  refine ⟨49350827228529550621268999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131602205942745468323383997 49350827228529550621268999)
  ·
    refine ⟨74026240842794325931903499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49350827228529550621268999 74026240842794325931903499)
    ·
      refine ⟨111039361264191488897855249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74026240842794325931903499 111039361264191488897855249)
      ·
        refine ⟨83279520948143616673391437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111039361264191488897855249 83279520948143616673391437)
        ·
          refine ⟨31229820355553856252521789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83279520948143616673391437 31229820355553856252521789)
          ·
            refine ⟨11711182633332696094695671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31229820355553856252521789 11711182633332696094695671)
            ·
              refine ⟨17566773949999044142043507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711182633332696094695671 17566773949999044142043507)
              ·
                refine ⟨26350160924998566213065261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17566773949999044142043507 26350160924998566213065261)
                ·
                  refine ⟨9881310346874462329899473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26350160924998566213065261 9881310346874462329899473)
                  ·
                    refine ⟨7410982760155846747424605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9881310346874462329899473 7410982760155846747424605)
                    ·
                      refine ⟨2779118535058442530284227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7410982760155846747424605 2779118535058442530284227)
                      ·
                        rfl

theorem cell23_5412314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_5412314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412314 prefixEnd_5412314 := by exact prefixLift 5412314
  have htrace : WordTrace (prefixWord ++ tailWord_5412314) baseStart_5412314 baseEnd_5412314 := by
    simpa [prefixWord, tailWord_5412314, baseEnd_5412314] using wordTrace_append hprefix tailTrace_5412314
  have hstable : (prefixWord ++ tailWord_5412314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412314).length < 2 ^ (prefixWord ++ tailWord_5412314).sum := by decide
  have hdescent : baseEnd_5412314 < baseStart_5412314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412317 : List Nat := [1, 4, 3, 1, 1, 2, 2, 9]
def baseStart_5412317 : Nat := 118140960795 + 5412317 * 2 ^ 59
def prefixEnd_5412317 : Nat := 4983230072969 + 3 ^ 40 * 5412317 * 2
def baseEnd_5412317 : Nat := 102930373166681704390619

theorem tailTrace_5412317 : CollatzResearch.WordTrace tailWord_5412317 prefixEnd_5412317 102930373166681704390619 := by
  unfold tailWord_5412317
  simp only [CollatzResearch.WordTrace]
  refine ⟨197403418333107333997435205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131602278888738222664956803 197403418333107333997435205)
  ·
    refine ⟨37013140937457625124519101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197403418333107333997435205 37013140937457625124519101)
    ·
      refine ⟨13879927851546609421694663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37013140937457625124519101 13879927851546609421694663)
      ·
        refine ⟨20819891777319914132541995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13879927851546609421694663 20819891777319914132541995)
        ·
          refine ⟨31229837665979871198812993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20819891777319914132541995 31229837665979871198812993)
          ·
            refine ⟨23422378249484903399109745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31229837665979871198812993 23422378249484903399109745)
            ·
              refine ⟨17566783687113677549332309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23422378249484903399109745 17566783687113677549332309)
              ·
                refine ⟨102930373166681704390619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17566783687113677549332309 102930373166681704390619)
                ·
                  rfl

theorem cell23_5412317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 9].length) (baseStart_5412317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412317 prefixEnd_5412317 := by exact prefixLift 5412317
  have htrace : WordTrace (prefixWord ++ tailWord_5412317) baseStart_5412317 baseEnd_5412317 := by
    simpa [prefixWord, tailWord_5412317, baseEnd_5412317] using wordTrace_append hprefix tailTrace_5412317
  have hstable : (prefixWord ++ tailWord_5412317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412317).length < 2 ^ (prefixWord ++ tailWord_5412317).sum := by decide
  have hdescent : baseEnd_5412317 < baseStart_5412317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412328 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_5412328 : Nat := 118140960795 + 5412328 * 2 ^ 59
def prefixEnd_5412328 : Nat := 4983230072969 + 3 ^ 40 * 5412328 * 2
def baseEnd_5412328 : Nat := 2779125723787605475509163

theorem tailTrace_5412328 : CollatzResearch.WordTrace tailWord_5412328 prefixEnd_5412328 2779125723787605475509163 := by
  unfold tailWord_5412328
  simp only [CollatzResearch.WordTrace]
  refine ⟨98701909768033741438042819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131602546357378321917390425 98701909768033741438042819)
  ·
    refine ⟨148052864652050612157064229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98701909768033741438042819 148052864652050612157064229)
    ·
      refine ⟨27759912122259489779449543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148052864652050612157064229 27759912122259489779449543)
      ·
        refine ⟨41639868183389234669174315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27759912122259489779449543 41639868183389234669174315)
        ·
          refine ⟨62459802275083852003761473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41639868183389234669174315 62459802275083852003761473)
          ·
            refine ⟨46844851706312889002821105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62459802275083852003761473 46844851706312889002821105)
            ·
              refine ⟨35133638779734666752115829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46844851706312889002821105 35133638779734666752115829)
              ·
                refine ⟨3293778635600125008010859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35133638779734666752115829 3293778635600125008010859)
                ·
                  refine ⟨4940667953400187512016289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293778635600125008010859 4940667953400187512016289)
                  ·
                    refine ⟨3705500965050140634012217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4940667953400187512016289 3705500965050140634012217)
                    ·
                      refine ⟨2779125723787605475509163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705500965050140634012217 2779125723787605475509163)
                      ·
                        rfl

theorem cell23_5412328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_5412328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412328 prefixEnd_5412328 := by exact prefixLift 5412328
  have htrace : WordTrace (prefixWord ++ tailWord_5412328) baseStart_5412328 baseEnd_5412328 := by
    simpa [prefixWord, tailWord_5412328, baseEnd_5412328] using wordTrace_append hprefix tailTrace_5412328
  have hstable : (prefixWord ++ tailWord_5412328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412328).length < 2 ^ (prefixWord ++ tailWord_5412328).sum := by decide
  have hdescent : baseEnd_5412328 < baseStart_5412328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412382 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5412382 : Nat := 118140960795 + 5412382 * 2 ^ 59
def prefixEnd_5412382 : Nat := 4983230072969 + 3 ^ 40 * 5412382 * 2
def baseEnd_5412382 : Nat := 2779153451742948264233915

theorem tailTrace_5412382 : CollatzResearch.WordTrace tailWord_5412382 prefixEnd_5412382 2779153451742948264233915 := by
  unfold tailWord_5412382
  simp only [CollatzResearch.WordTrace]
  refine ⟨24675723634733981262318925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131603859385247900065700933 24675723634733981262318925)
  ·
    refine ⟨9253396363025242973369597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24675723634733981262318925 9253396363025242973369597)
    ·
      refine ⟨3470023636134466115013599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9253396363025242973369597 3470023636134466115013599)
      ·
        refine ⟨5205035454201699172520399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3470023636134466115013599 5205035454201699172520399)
        ·
          refine ⟨7807553181302548758780599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205035454201699172520399 7807553181302548758780599)
          ·
            refine ⟨11711329771953823138170899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807553181302548758780599 11711329771953823138170899)
            ·
              refine ⟨17566994657930734707256349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711329771953823138170899 17566994657930734707256349)
              ·
                refine ⟨6587622996724025515221131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17566994657930734707256349 6587622996724025515221131)
                ·
                  refine ⟨9881434495086038272831697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587622996724025515221131 9881434495086038272831697)
                  ·
                    refine ⟨7411075871314528704623773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9881434495086038272831697 7411075871314528704623773)
                    ·
                      refine ⟨2779153451742948264233915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7411075871314528704623773 2779153451742948264233915)
                      ·
                        rfl

theorem cell23_5412382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5412382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412382 prefixEnd_5412382 := by exact prefixLift 5412382
  have htrace : WordTrace (prefixWord ++ tailWord_5412382) baseStart_5412382 baseEnd_5412382 := by
    simpa [prefixWord, tailWord_5412382, baseEnd_5412382] using wordTrace_append hprefix tailTrace_5412382
  have hstable : (prefixWord ++ tailWord_5412382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412382).length < 2 ^ (prefixWord ++ tailWord_5412382).sum := by decide
  have hdescent : baseEnd_5412382 < baseStart_5412382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412407 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 7]
def baseStart_5412407 : Nat := 118140960795 + 5412407 * 2 ^ 59
def prefixEnd_5412407 : Nat := 4983230072969 + 3 ^ 40 * 5412407 * 2
def baseEnd_5412407 : Nat := 308796254306590074046811

theorem tailTrace_5412407 : CollatzResearch.WordTrace tailWord_5412407 prefixEnd_5412407 308796254306590074046811 := by
  unfold tailWord_5412407
  simp only [CollatzResearch.WordTrace]
  refine ⟨197406700902781279368211475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131604467268520852912140983 197406700902781279368211475)
  ·
    refine ⟨296110051354171919052317213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197406700902781279368211475 296110051354171919052317213)
    ·
      refine ⟨111041269257814469644618955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296110051354171919052317213 111041269257814469644618955)
      ·
        refine ⟨166561903886721704466928433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111041269257814469644618955 166561903886721704466928433)
        ·
          refine ⟨124921427915041278350196325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166561903886721704466928433 124921427915041278350196325)
          ·
            refine ⟨23422767734070239690661811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124921427915041278350196325 23422767734070239690661811)
            ·
              refine ⟨35134151601105359535992717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23422767734070239690661811 35134151601105359535992717)
              ·
                refine ⟨13175306850414509825997269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35134151601105359535992717 13175306850414509825997269)
                ·
                  refine ⟨308796254306590074046811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13175306850414509825997269 308796254306590074046811)
                  ·
                    rfl

theorem cell23_5412407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 7].length) (baseStart_5412407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412407 prefixEnd_5412407 := by exact prefixLift 5412407
  have htrace : WordTrace (prefixWord ++ tailWord_5412407) baseStart_5412407 baseEnd_5412407 := by
    simpa [prefixWord, tailWord_5412407, baseEnd_5412407] using wordTrace_append hprefix tailTrace_5412407
  have hstable : (prefixWord ++ tailWord_5412407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412407).length < 2 ^ (prefixWord ++ tailWord_5412407).sum := by decide
  have hdescent : baseEnd_5412407 < baseStart_5412407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412422 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5412422 : Nat := 118140960795 + 5412422 * 2 ^ 59
def prefixEnd_5412422 : Nat := 4983230072969 + 3 ^ 40 * 5412422 * 2
def baseEnd_5412422 : Nat := 2779173990969128107733731

theorem tailTrace_5412422 : CollatzResearch.WordTrace tailWord_5412422 prefixEnd_5412422 2779173990969128107733731 := by
  unfold tailWord_5412422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168976499928966779062735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131604831998484624620005013 6168976499928966779062735)
  ·
    refine ⟨9253464749893450168594103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6168976499928966779062735 9253464749893450168594103)
    ·
      refine ⟨13880197124840175252891155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253464749893450168594103 13880197124840175252891155)
      ·
        refine ⟨20820295687260262879336733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13880197124840175252891155 20820295687260262879336733)
        ·
          refine ⟨7807610882722598579751275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20820295687260262879336733 7807610882722598579751275)
          ·
            refine ⟨11711416324083897869626913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807610882722598579751275 11711416324083897869626913)
            ·
              refine ⟨8783562243062923402220185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11711416324083897869626913 8783562243062923402220185)
              ·
                refine ⟨6587671682297192551665139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8783562243062923402220185 6587671682297192551665139)
                ·
                  refine ⟨9881507523445788827497709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587671682297192551665139 9881507523445788827497709)
                  ·
                    refine ⟨3705565321292170810311641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9881507523445788827497709 3705565321292170810311641)
                    ·
                      refine ⟨2779173990969128107733731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705565321292170810311641 2779173990969128107733731)
                      ·
                        rfl

theorem cell23_5412422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5412422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412422 prefixEnd_5412422 := by exact prefixLift 5412422
  have htrace : WordTrace (prefixWord ++ tailWord_5412422) baseStart_5412422 baseEnd_5412422 := by
    simpa [prefixWord, tailWord_5412422, baseEnd_5412422] using wordTrace_append hprefix tailTrace_5412422
  have hstable : (prefixWord ++ tailWord_5412422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412422).length < 2 ^ (prefixWord ++ tailWord_5412422).sum := by decide
  have hdescent : baseEnd_5412422 < baseStart_5412422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412458 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_5412458 : Nat := 118140960795 + 5412458 * 2 ^ 59
def prefixEnd_5412458 : Nat := 4983230072969 + 3 ^ 40 * 5412458 * 2
def baseEnd_5412458 : Nat := 308799164030298885209285

theorem tailTrace_5412458 : CollatzResearch.WordTrace tailWord_5412458 prefixEnd_5412458 308799164030298885209285 := by
  unfold tailWord_5412458
  simp only [CollatzResearch.WordTrace]
  refine ⟨49352140256399128769579507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131605707350397676718878685 49352140256399128769579507)
  ·
    refine ⟨74028210384598693154369261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49352140256399128769579507 74028210384598693154369261)
    ·
      refine ⟨27760578894224509932888473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74028210384598693154369261 27760578894224509932888473)
      ·
        refine ⟨20820434170668382449666355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27760578894224509932888473 20820434170668382449666355)
        ·
          refine ⟨31230651256002573674499533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20820434170668382449666355 31230651256002573674499533)
          ·
            refine ⟨11711494221000965127937325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31230651256002573674499533 11711494221000965127937325)
            ·
              refine ⟨4391810332875361922976497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11711494221000965127937325 4391810332875361922976497)
              ·
                refine ⟨3293857749656521442232373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391810332875361922976497 3293857749656521442232373)
                ·
                  refine ⟨308799164030298885209285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3293857749656521442232373 308799164030298885209285)
                  ·
                    rfl

theorem cell23_5412458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_5412458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412458 prefixEnd_5412458 := by exact prefixLift 5412458
  have htrace : WordTrace (prefixWord ++ tailWord_5412458) baseStart_5412458 baseEnd_5412458 := by
    simpa [prefixWord, tailWord_5412458, baseEnd_5412458] using wordTrace_append hprefix tailTrace_5412458
  have hstable : (prefixWord ++ tailWord_5412458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412458).length < 2 ^ (prefixWord ++ tailWord_5412458).sum := by decide
  have hdescent : baseEnd_5412458 < baseStart_5412458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412464 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_5412464 : Nat := 118140960795 + 5412464 * 2 ^ 59
def prefixEnd_5412464 : Nat := 4983230072969 + 3 ^ 40 * 5412464 * 2
def baseEnd_5412464 : Nat := 2779195557156616943408537

theorem tailTrace_5412464 : CollatzResearch.WordTrace tailWord_5412464 prefixEnd_5412464 2779195557156616943408537 := by
  unfold tailWord_5412464
  simp only [CollatzResearch.WordTrace]
  refine ⟨98704389931787389051518223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131605853242383185402024297 98704389931787389051518223)
  ·
    refine ⟨148056584897681083577277335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98704389931787389051518223 148056584897681083577277335)
    ·
      refine ⟨222084877346521625365916003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148056584897681083577277335 222084877346521625365916003)
      ·
        refine ⟨333127316019782438048874005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222084877346521625365916003 333127316019782438048874005)
        ·
          refine ⟨15615342938427301783540969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 333127316019782438048874005 15615342938427301783540969)
          ·
            refine ⟨11711507203820476337655727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15615342938427301783540969 11711507203820476337655727)
            ·
              refine ⟨17567260805730714506483591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711507203820476337655727 17567260805730714506483591)
              ·
                refine ⟨26350891208596071759725387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17567260805730714506483591 26350891208596071759725387)
                ·
                  refine ⟨39526336812894107639588081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26350891208596071759725387 39526336812894107639588081)
                  ·
                    refine ⟨29644752609670580729691061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39526336812894107639588081 29644752609670580729691061)
                    ·
                      refine ⟨2779195557156616943408537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29644752609670580729691061 2779195557156616943408537)
                      ·
                        rfl

theorem cell23_5412464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_5412464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412464 prefixEnd_5412464 := by exact prefixLift 5412464
  have htrace : WordTrace (prefixWord ++ tailWord_5412464) baseStart_5412464 baseEnd_5412464 := by
    simpa [prefixWord, tailWord_5412464, baseEnd_5412464] using wordTrace_append hprefix tailTrace_5412464
  have hstable : (prefixWord ++ tailWord_5412464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412464).length < 2 ^ (prefixWord ++ tailWord_5412464).sum := by decide
  have hdescent : baseEnd_5412464 < baseStart_5412464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412488 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 2, 5]
def baseStart_5412488 : Nat := 118140960795 + 5412488 * 2 ^ 59
def prefixEnd_5412488 : Nat := 4983230072969 + 3 ^ 40 * 5412488 * 2
def baseEnd_5412488 : Nat := 926402626897441616502809

theorem tailTrace_5412488 : CollatzResearch.WordTrace tailWord_5412488 prefixEnd_5412488 926402626897441616502809 := by
  unfold tailWord_5412488
  simp only [CollatzResearch.WordTrace]
  refine ⟨98704827607743915100955059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131606436810325220134606745 98704827607743915100955059)
  ·
    refine ⟨148057241411615872651432589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98704827607743915100955059 148057241411615872651432589)
    ·
      refine ⟨55521465529355952244287221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148057241411615872651432589 55521465529355952244287221)
      ·
        refine ⟨5205137393377120522901927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55521465529355952244287221 5205137393377120522901927)
        ·
          refine ⟨7807706090065680784352891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205137393377120522901927 7807706090065680784352891)
          ·
            refine ⟨11711559135098521176529337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807706090065680784352891 11711559135098521176529337)
            ·
              refine ⟨8783669351323890882397003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11711559135098521176529337 8783669351323890882397003)
              ·
                refine ⟨13175504026985836323595505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783669351323890882397003 13175504026985836323595505)
                ·
                  refine ⟨9881628020239377242696629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13175504026985836323595505 9881628020239377242696629)
                  ·
                    refine ⟨926402626897441616502809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9881628020239377242696629 926402626897441616502809)
                    ·
                      rfl

theorem cell23_5412488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_5412488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412488 prefixEnd_5412488 := by exact prefixLift 5412488
  have htrace : WordTrace (prefixWord ++ tailWord_5412488) baseStart_5412488 baseEnd_5412488 := by
    simpa [prefixWord, tailWord_5412488, baseEnd_5412488] using wordTrace_append hprefix tailTrace_5412488
  have hstable : (prefixWord ++ tailWord_5412488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412488).length < 2 ^ (prefixWord ++ tailWord_5412488).sum := by decide
  have hdescent : baseEnd_5412488 < baseStart_5412488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412497 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 8]
def baseStart_5412497 : Nat := 118140960795 + 5412497 * 2 ^ 59
def prefixEnd_5412497 : Nat := 4983230072969 + 3 ^ 40 * 5412497 * 2
def baseEnd_5412497 : Nat := 308801389113135034921765

theorem tailTrace_5412497 : CollatzResearch.WordTrace tailWord_5412497 prefixEnd_5412497 308801389113135034921765 := by
  unfold tailWord_5412497
  simp only [CollatzResearch.WordTrace]
  refine ⟨197409983472455224738987745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131606655648303483159325163 197409983472455224738987745)
  ·
    refine ⟨148057487604341418554240809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197409983472455224738987745 148057487604341418554240809)
    ·
      refine ⟨111043115703256063915680607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148057487604341418554240809 111043115703256063915680607)
      ·
        refine ⟨166564673554884095873520911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111043115703256063915680607 166564673554884095873520911)
        ·
          refine ⟨249847010332326143810281367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166564673554884095873520911 249847010332326143810281367)
          ·
            refine ⟨374770515498489215715422051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249847010332326143810281367 374770515498489215715422051)
            ·
              refine ⟨562155773247733823573133077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374770515498489215715422051 562155773247733823573133077)
              ·
                refine ⟨26351051870987522979990613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 562155773247733823573133077 26351051870987522979990613)
                ·
                  refine ⟨308801389113135034921765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26351051870987522979990613 308801389113135034921765)
                  ·
                    rfl

theorem cell23_5412497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_5412497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412497 prefixEnd_5412497 := by exact prefixLift 5412497
  have htrace : WordTrace (prefixWord ++ tailWord_5412497) baseStart_5412497 baseEnd_5412497 := by
    simpa [prefixWord, tailWord_5412497, baseEnd_5412497] using wordTrace_append hprefix tailTrace_5412497
  have hstable : (prefixWord ++ tailWord_5412497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412497).length < 2 ^ (prefixWord ++ tailWord_5412497).sum := by decide
  have hdescent : baseEnd_5412497 < baseStart_5412497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412544 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_5412544 : Nat := 118140960795 + 5412544 * 2 ^ 59
def prefixEnd_5412544 : Nat := 4983230072969 + 3 ^ 40 * 5412544 * 2
def baseEnd_5412544 : Nat := 926412211869658876802723

theorem tailTrace_5412544 : CollatzResearch.WordTrace tailWord_5412544 prefixEnd_5412544 926412211869658876802723 := by
  unfold tailWord_5412544
  simp only [CollatzResearch.WordTrace]
  refine ⟨98705848851642475882974343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131607798468856634510632457 98705848851642475882974343)
  ·
    refine ⟨148058773277463713824461515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98705848851642475882974343 148058773277463713824461515)
    ·
      refine ⟨222088159916195570736692273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148058773277463713824461515 222088159916195570736692273)
      ·
        refine ⟨166566119937146678052519205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222088159916195570736692273 166566119937146678052519205)
        ·
          refine ⟨31231147488215002134847351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166566119937146678052519205 31231147488215002134847351)
          ·
            refine ⟨46846721232322503202271027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31231147488215002134847351 46846721232322503202271027)
            ·
              refine ⟨70270081848483754803406541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46846721232322503202271027 70270081848483754803406541)
              ·
                refine ⟨26351280693181408051277453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70270081848483754803406541 26351280693181408051277453)
                ·
                  refine ⟨9881730259943028019229045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26351280693181408051277453 9881730259943028019229045)
                  ·
                    refine ⟨926412211869658876802723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9881730259943028019229045 926412211869658876802723)
                    ·
                      rfl

theorem cell23_5412544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_5412544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412544 prefixEnd_5412544 := by exact prefixLift 5412544
  have htrace : WordTrace (prefixWord ++ tailWord_5412544) baseStart_5412544 baseEnd_5412544 := by
    simpa [prefixWord, tailWord_5412544, baseEnd_5412544] using wordTrace_append hprefix tailTrace_5412544
  have hstable : (prefixWord ++ tailWord_5412544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412544).length < 2 ^ (prefixWord ++ tailWord_5412544).sum := by decide
  have hdescent : baseEnd_5412544 < baseStart_5412544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412551 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_5412551 : Nat := 118140960795 + 5412551 * 2 ^ 59
def prefixEnd_5412551 : Nat := 4983230072969 + 3 ^ 40 * 5412551 * 2
def baseEnd_5412551 : Nat := 2779240229973558103020637

theorem tailTrace_5412551 : CollatzResearch.WordTrace tailWord_5412551 prefixEnd_5412551 2779240229973558103020637 := by
  unfold tailWord_5412551
  simp only [CollatzResearch.WordTrace]
  refine ⟨197411953014259591961453507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131607968676173061307635671 197411953014259591961453507)
  ·
    refine ⟨296117929521389387942180261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197411953014259591961453507 296117929521389387942180261)
    ·
      refine ⟨55522111785260510239158799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296117929521389387942180261 55522111785260510239158799)
      ·
        refine ⟨83283167677890765358738199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55522111785260510239158799 83283167677890765358738199)
        ·
          refine ⟨124924751516836148038107299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83283167677890765358738199 124924751516836148038107299)
          ·
            refine ⟨187387127275254222057160949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124924751516836148038107299 187387127275254222057160949)
            ·
              refine ⟨17567543182055083317858839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187387127275254222057160949 17567543182055083317858839)
              ·
                refine ⟨26351314773082624976788259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17567543182055083317858839 26351314773082624976788259)
                ·
                  refine ⟨39526972159623937465182389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26351314773082624976788259 39526972159623937465182389)
                  ·
                    refine ⟨3705653639964744137360849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39526972159623937465182389 3705653639964744137360849)
                    ·
                      refine ⟨2779240229973558103020637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705653639964744137360849 2779240229973558103020637)
                      ·
                        rfl

theorem cell23_5412551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_5412551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412551 prefixEnd_5412551 := by exact prefixLift 5412551
  have htrace : WordTrace (prefixWord ++ tailWord_5412551) baseStart_5412551 baseEnd_5412551 := by
    simpa [prefixWord, tailWord_5412551, baseEnd_5412551] using wordTrace_append hprefix tailTrace_5412551
  have hstable : (prefixWord ++ tailWord_5412551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412551).length < 2 ^ (prefixWord ++ tailWord_5412551).sum := by decide
  have hdescent : baseEnd_5412551 < baseStart_5412551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412561 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 1, 5]
def baseStart_5412561 : Nat := 118140960795 + 5412561 * 2 ^ 59
def prefixEnd_5412561 : Nat := 4983230072969 + 3 ^ 40 * 5412561 * 2
def baseEnd_5412561 : Nat := 926415121593367687965197

theorem tailTrace_5412561 : CollatzResearch.WordTrace tailWord_5412561 prefixEnd_5412561 926415121593367687965197 := by
  unfold tailWord_5412561
  simp only [CollatzResearch.WordTrace]
  refine ⟨197412317744223363669317537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131608211829482242446211691 197412317744223363669317537)
  ·
    refine ⟨148059238308167522751988153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197412317744223363669317537 148059238308167522751988153)
    ·
      refine ⟨111044428731125642063991115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148059238308167522751988153 111044428731125642063991115)
      ·
        refine ⟨166566643096688463095986673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111044428731125642063991115 166566643096688463095986673)
        ·
          refine ⟨124924982322516347321990005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166566643096688463095986673 124924982322516347321990005)
          ·
            refine ⟨11711717092735907561436563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124924982322516347321990005 11711717092735907561436563)
            ·
              refine ⟨17567575639103861342154845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711717092735907561436563 17567575639103861342154845)
              ·
                refine ⟨6587840864663948003308067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17567575639103861342154845 6587840864663948003308067)
                ·
                  refine ⟨9881761296995922004962101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587840864663948003308067 9881761296995922004962101)
                  ·
                    refine ⟨926415121593367687965197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9881761296995922004962101 926415121593367687965197)
                    ·
                      rfl

theorem cell23_5412561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_5412561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412561 prefixEnd_5412561 := by exact prefixLift 5412561
  have htrace : WordTrace (prefixWord ++ tailWord_5412561) baseStart_5412561 baseEnd_5412561 := by
    simpa [prefixWord, tailWord_5412561, baseEnd_5412561] using wordTrace_append hprefix tailTrace_5412561
  have hstable : (prefixWord ++ tailWord_5412561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412561).length < 2 ^ (prefixWord ++ tailWord_5412561).sum := by decide
  have hdescent : baseEnd_5412561 < baseStart_5412561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412598 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5412598 : Nat := 118140960795 + 5412598 * 2 ^ 59
def prefixEnd_5412598 : Nat := 4983230072969 + 3 ^ 40 * 5412598 * 2
def baseEnd_5412598 : Nat := 2779264363564319419132921

theorem tailTrace_5412598 : CollatzResearch.WordTrace tailWord_5412598 prefixEnd_5412598 2779264363564319419132921 := by
  unfold tailWord_5412598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338354202818082436775903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131609111496726212658942965 12338354202818082436775903)
  ·
    refine ⟨18507531304227123655163855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12338354202818082436775903 18507531304227123655163855)
    ·
      refine ⟨27761296956340685482745783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18507531304227123655163855 27761296956340685482745783)
      ·
        refine ⟨41641945434511028224118675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27761296956340685482745783 41641945434511028224118675)
        ·
          refine ⟨62462918151766542336178013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41641945434511028224118675 62462918151766542336178013)
          ·
            refine ⟨23423594306912453376066755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62462918151766542336178013 23423594306912453376066755)
            ·
              refine ⟨35135391460368680064100133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23423594306912453376066755 35135391460368680064100133)
              ·
                refine ⟨6587885898819127512018775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35135391460368680064100133 6587885898819127512018775)
                ·
                  refine ⟨9881828848228691268028163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587885898819127512018775 9881828848228691268028163)
                  ·
                    refine ⟨14822743272343036902042245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9881828848228691268028163 14822743272343036902042245)
                    ·
                      refine ⟨2779264363564319419132921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14822743272343036902042245 2779264363564319419132921)
                      ·
                        rfl

theorem cell23_5412598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5412598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412598 prefixEnd_5412598 := by exact prefixLift 5412598
  have htrace : WordTrace (prefixWord ++ tailWord_5412598) baseStart_5412598 baseEnd_5412598 := by
    simpa [prefixWord, tailWord_5412598, baseEnd_5412598] using wordTrace_append hprefix tailTrace_5412598
  have hstable : (prefixWord ++ tailWord_5412598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412598).length < 2 ^ (prefixWord ++ tailWord_5412598).sum := by decide
  have hdescent : baseEnd_5412598 < baseStart_5412598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412604 : List Nat := [2, 2, 2, 1, 3, 1, 3, 9]
def baseStart_5412604 : Nat := 118140960795 + 5412604 * 2 ^ 59
def prefixEnd_5412604 : Nat := 4983230072969 + 3 ^ 40 * 5412604 * 2
def baseEnd_5412604 : Nat := 102935831275860977616959

theorem tailTrace_5412604 : CollatzResearch.WordTrace tailWord_5412604 prefixEnd_5412604 102935831275860977616959 := by
  unfold tailWord_5412604
  simp only [CollatzResearch.WordTrace]
  refine ⟨98706943041533791006566433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131609257388711721342088577 98706943041533791006566433)
  ·
    refine ⟨74030207281150343254924825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98706943041533791006566433 74030207281150343254924825)
    ·
      refine ⟨55522655460862757441193619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74030207281150343254924825 55522655460862757441193619)
      ·
        refine ⟨83283983191294136161790429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55522655460862757441193619 83283983191294136161790429)
        ·
          refine ⟨31231493696735301060671411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83283983191294136161790429 31231493696735301060671411)
          ·
            refine ⟨46847240545102951591007117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31231493696735301060671411 46847240545102951591007117)
            ·
              refine ⟨17567715204413606846627669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46847240545102951591007117 17567715204413606846627669)
              ·
                refine ⟨102935831275860977616959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17567715204413606846627669 102935831275860977616959)
                ·
                  rfl

theorem cell23_5412604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 9].length) (baseStart_5412604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412604 prefixEnd_5412604 := by exact prefixLift 5412604
  have htrace : WordTrace (prefixWord ++ tailWord_5412604) baseStart_5412604 baseEnd_5412604 := by
    simpa [prefixWord, tailWord_5412604, baseEnd_5412604] using wordTrace_append hprefix tailTrace_5412604
  have hstable : (prefixWord ++ tailWord_5412604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412604).length < 2 ^ (prefixWord ++ tailWord_5412604).sum := by decide
  have hdescent : baseEnd_5412604 < baseStart_5412604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412618 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_5412618 : Nat := 118140960795 + 5412618 * 2 ^ 59
def prefixEnd_5412618 : Nat := 4983230072969 + 3 ^ 40 * 5412618 * 2
def baseEnd_5412618 : Nat := 2779274633177409340882829

theorem tailTrace_5412618 : CollatzResearch.WordTrace tailWord_5412618 prefixEnd_5412618 2779274633177409340882829 := by
  unfold tailWord_5412618
  simp only [CollatzResearch.WordTrace]
  refine ⟨49353599176254215601035627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131609597803344574936095005 49353599176254215601035627)
  ·
    refine ⟨74030398764381323401553441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49353599176254215601035627 74030398764381323401553441)
    ·
      refine ⟨55522799073285992551165081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74030398764381323401553441 55522799073285992551165081)
      ·
        refine ⟨41642099304964494413373811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55522799073285992551165081 41642099304964494413373811)
        ·
          refine ⟨62463148957446741620060717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41642099304964494413373811 62463148957446741620060717)
          ·
            refine ⟨23423680859042528107522769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62463148957446741620060717 23423680859042528107522769)
            ·
              refine ⟨17567760644281896080642077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23423680859042528107522769 17567760644281896080642077)
              ·
                refine ⟨6587910241605711030240779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17567760644281896080642077 6587910241605711030240779)
                ·
                  refine ⟨9881865362408566545361169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587910241605711030240779 9881865362408566545361169)
                  ·
                    refine ⟨7411399021806424909020877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9881865362408566545361169 7411399021806424909020877)
                    ·
                      refine ⟨2779274633177409340882829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7411399021806424909020877 2779274633177409340882829)
                      ·
                        rfl

theorem cell23_5412618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_5412618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412618 prefixEnd_5412618 := by exact prefixLift 5412618
  have htrace : WordTrace (prefixWord ++ tailWord_5412618) baseStart_5412618 baseEnd_5412618 := by
    simpa [prefixWord, tailWord_5412618, baseEnd_5412618] using wordTrace_append hprefix tailTrace_5412618
  have hstable : (prefixWord ++ tailWord_5412618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412618).length < 2 ^ (prefixWord ++ tailWord_5412618).sum := by decide
  have hdescent : baseEnd_5412618 < baseStart_5412618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412665 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5412665 : Nat := 118140960795 + 5412665 * 2 ^ 59
def prefixEnd_5412665 : Nat := 4983230072969 + 3 ^ 40 * 5412665 * 2
def baseEnd_5412665 : Nat := 2779298766768170656995113

theorem tailTrace_5412665 : CollatzResearch.WordTrace tailWord_5412665 prefixEnd_5412665 2779298766768170656995113 := by
  unfold tailWord_5412665
  simp only [CollatzResearch.WordTrace]
  refine ⟨197416110935846589431103449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131610740623897726287402299 197416110935846589431103449)
  ·
    refine ⟨148062083201884942073327587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197416110935846589431103449 148062083201884942073327587)
    ·
      refine ⟨222093124802827413109991381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148062083201884942073327587 222093124802827413109991381)
      ·
        refine ⟨5205307612566267494765423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 222093124802827413109991381 5205307612566267494765423)
        ·
          refine ⟨7807961418849401242148135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205307612566267494765423 7807961418849401242148135)
          ·
            refine ⟨11711942128274101863222203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807961418849401242148135 11711942128274101863222203)
            ·
              refine ⟨17567913192411152794833305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711942128274101863222203 17567913192411152794833305)
              ·
                refine ⟨13175934894308364596124979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17567913192411152794833305 13175934894308364596124979)
                ·
                  refine ⟨19763902341462546894187469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13175934894308364596124979 19763902341462546894187469)
                  ·
                    refine ⟨7411463378048455085320301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19763902341462546894187469 7411463378048455085320301)
                    ·
                      refine ⟨2779298766768170656995113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7411463378048455085320301 2779298766768170656995113)
                      ·
                        rfl

theorem cell23_5412665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5412665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412665 prefixEnd_5412665 := by exact prefixLift 5412665
  have htrace : WordTrace (prefixWord ++ tailWord_5412665) baseStart_5412665 baseEnd_5412665 := by
    simpa [prefixWord, tailWord_5412665, baseEnd_5412665] using wordTrace_append hprefix tailTrace_5412665
  have hstable : (prefixWord ++ tailWord_5412665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412665).length < 2 ^ (prefixWord ++ tailWord_5412665).sum := by decide
  have hdescent : baseEnd_5412665 < baseStart_5412665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412705 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_5412705 : Nat := 118140960795 + 5412705 * 2 ^ 59
def prefixEnd_5412705 : Nat := 4983230072969 + 3 ^ 40 * 5412705 * 2
def baseEnd_5412705 : Nat := 2779319305994350500494929

theorem tailTrace_5412705 : CollatzResearch.WordTrace tailWord_5412705 prefixEnd_5412705 2779319305994350500494929 := by
  unfold tailWord_5412705
  simp only [CollatzResearch.WordTrace]
  refine ⟨197417569855701676262559569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131611713237134450841706379 197417569855701676262559569)
  ·
    refine ⟨148063177391776257196919677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197417569855701676262559569 148063177391776257196919677)
    ·
      refine ⟨55523691521916096448844879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148063177391776257196919677 55523691521916096448844879)
      ·
        refine ⟨83285537282874144673267319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55523691521916096448844879 83285537282874144673267319)
        ·
          refine ⟨124928305924311217009900979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83285537282874144673267319 124928305924311217009900979)
          ·
            refine ⟨187392458886466825514851469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124928305924311217009900979 187392458886466825514851469)
            ·
              refine ⟨70272172082425059568069301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187392458886466825514851469 70272172082425059568069301)
              ·
                refine ⟨6588016132727349334506497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70272172082425059568069301 6588016132727349334506497)
                ·
                  refine ⟨4941012099545512000879873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6588016132727349334506497 4941012099545512000879873)
                  ·
                    refine ⟨3705759074659134000659905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4941012099545512000879873 3705759074659134000659905)
                    ·
                      refine ⟨2779319305994350500494929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705759074659134000659905 2779319305994350500494929)
                      ·
                        rfl

theorem cell23_5412705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_5412705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412705 prefixEnd_5412705 := by exact prefixLift 5412705
  have htrace : WordTrace (prefixWord ++ tailWord_5412705) baseStart_5412705 baseEnd_5412705 := by
    simpa [prefixWord, tailWord_5412705, baseEnd_5412705] using wordTrace_append hprefix tailTrace_5412705
  have hstable : (prefixWord ++ tailWord_5412705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412705).length < 2 ^ (prefixWord ++ tailWord_5412705).sum := by decide
  have hdescent : baseEnd_5412705 < baseStart_5412705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412711 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 7]
def baseStart_5412711 : Nat := 118140960795 + 5412711 * 2 ^ 59
def prefixEnd_5412711 : Nat := 4983230072969 + 3 ^ 40 * 5412711 * 2
def baseEnd_5412711 : Nat := 308813598542030830779989

theorem tailTrace_5412711 : CollatzResearch.WordTrace tailWord_5412711 prefixEnd_5412711 308813598542030830779989 := by
  unfold tailWord_5412711
  simp only [CollatzResearch.WordTrace]
  refine ⟨197417788693679939287277987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131611859129119959524851991 197417788693679939287277987)
  ·
    refine ⟨296126683040519908930916981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197417788693679939287277987 296126683040519908930916981)
    ·
      refine ⟨27761876535048741462273467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296126683040519908930916981 27761876535048741462273467)
      ·
        refine ⟨41642814802573112193410201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27761876535048741462273467 41642814802573112193410201)
        ·
          refine ⟨31232111101929834145057651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41642814802573112193410201 31232111101929834145057651)
          ·
            refine ⟨46848166652894751217586477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31232111101929834145057651 46848166652894751217586477)
            ·
              refine ⟨17568062494835531706594929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46848166652894751217586477 17568062494835531706594929)
              ·
                refine ⟨13176046871126648779946197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17568062494835531706594929 13176046871126648779946197)
                ·
                  refine ⟨308813598542030830779989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13176046871126648779946197 308813598542030830779989)
                  ·
                    rfl

theorem cell23_5412711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 7].length) (baseStart_5412711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412711 prefixEnd_5412711 := by exact prefixLift 5412711
  have htrace : WordTrace (prefixWord ++ tailWord_5412711) baseStart_5412711 baseEnd_5412711 := by
    simpa [prefixWord, tailWord_5412711, baseEnd_5412711] using wordTrace_append hprefix tailTrace_5412711
  have hstable : (prefixWord ++ tailWord_5412711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412711).length < 2 ^ (prefixWord ++ tailWord_5412711).sum := by decide
  have hdescent : baseEnd_5412711 < baseStart_5412711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412721 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_5412721 : Nat := 118140960795 + 5412721 * 2 ^ 59
def prefixEnd_5412721 : Nat := 4983230072969 + 3 ^ 40 * 5412721 * 2
def baseEnd_5412721 : Nat := 2779327521684822437894855

theorem tailTrace_5412721 : CollatzResearch.WordTrace tailWord_5412721 prefixEnd_5412721 2779327521684822437894855 := by
  unfold tailWord_5412721
  simp only [CollatzResearch.WordTrace]
  refine ⟨197418153423643710995142017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131612102282429140663428011 197418153423643710995142017)
  ·
    refine ⟨148063615067732783246356513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197418153423643710995142017 148063615067732783246356513)
    ·
      refine ⟨111047711300799587434767385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148063615067732783246356513 111047711300799587434767385)
      ·
        refine ⟨83285783475599690576075539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111047711300799587434767385 83285783475599690576075539)
        ·
          refine ⟨124928675213399535864113309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83285783475599690576075539 124928675213399535864113309)
          ·
            refine ⟨46848253205024825949042491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124928675213399535864113309 46848253205024825949042491)
            ·
              refine ⟨70272379807537238923563737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46848253205024825949042491 70272379807537238923563737)
              ·
                refine ⟨52704284855652929192672803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70272379807537238923563737 52704284855652929192672803)
                ·
                  refine ⟨79056427283479393789009205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52704284855652929192672803 79056427283479393789009205)
                  ·
                    refine ⟨7411540057826193167719613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79056427283479393789009205 7411540057826193167719613)
                    ·
                      refine ⟨2779327521684822437894855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7411540057826193167719613 2779327521684822437894855)
                      ·
                        rfl

theorem cell23_5412721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_5412721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412721 prefixEnd_5412721 := by exact prefixLift 5412721
  have htrace : WordTrace (prefixWord ++ tailWord_5412721) baseStart_5412721 baseEnd_5412721 := by
    simpa [prefixWord, tailWord_5412721, baseEnd_5412721] using wordTrace_append hprefix tailTrace_5412721
  have hstable : (prefixWord ++ tailWord_5412721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412721).length < 2 ^ (prefixWord ++ tailWord_5412721).sum := by decide
  have hdescent : baseEnd_5412721 < baseStart_5412721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412726 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5412726 : Nat := 118140960795 + 5412726 * 2 ^ 59
def prefixEnd_5412726 : Nat := 4983230072969 + 3 ^ 40 * 5412726 * 2
def baseEnd_5412726 : Nat := 2779330089088094918332333

theorem tailTrace_5412726 : CollatzResearch.WordTrace tailWord_5412726 prefixEnd_5412726 2779330089088094918332333 := by
  unfold tailWord_5412726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338645986789099803067127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131612223859083731232716021 12338645986789099803067127)
  ·
    refine ⟨18507968980183649704600691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12338645986789099803067127 18507968980183649704600691)
    ·
      refine ⟨27761953470275474556901037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18507968980183649704600691 27761953470275474556901037)
      ·
        refine ⟨10410732551353302958837889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27761953470275474556901037 10410732551353302958837889)
        ·
          refine ⟨7808049413514977219128417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10410732551353302958837889 7808049413514977219128417)
          ·
            refine ⟨5856037060136232914346313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7808049413514977219128417 5856037060136232914346313)
            ·
              refine ⟨4392027795102174685759735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5856037060136232914346313 4392027795102174685759735)
              ·
                refine ⟨6588041692653262028639603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392027795102174685759735 6588041692653262028639603)
                ·
                  refine ⟨9882062538979893042959405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6588041692653262028639603 9882062538979893042959405)
                  ·
                    refine ⟨3705773452117459891109777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9882062538979893042959405 3705773452117459891109777)
                    ·
                      refine ⟨2779330089088094918332333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705773452117459891109777 2779330089088094918332333)
                      ·
                        rfl

theorem cell23_5412726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5412726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412726 prefixEnd_5412726 := by exact prefixLift 5412726
  have htrace : WordTrace (prefixWord ++ tailWord_5412726) baseStart_5412726 baseEnd_5412726 := by
    simpa [prefixWord, tailWord_5412726, baseEnd_5412726] using wordTrace_append hprefix tailTrace_5412726
  have hstable : (prefixWord ++ tailWord_5412726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412726).length < 2 ^ (prefixWord ++ tailWord_5412726).sum := by decide
  have hdescent : baseEnd_5412726 < baseStart_5412726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412741 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_5412741 : Nat := 118140960795 + 5412741 * 2 ^ 59
def prefixEnd_5412741 : Nat := 4983230072969 + 3 ^ 40 * 5412741 * 2
def baseEnd_5412741 : Nat := 926445930432637453214921

theorem tailTrace_5412741 : CollatzResearch.WordTrace tailWord_5412741 prefixEnd_5412741 926445930432637453214921 := by
  unfold tailWord_5412741
  simp only [CollatzResearch.WordTrace]
  refine ⟨197418882883571254410870077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131612588589047502940580051 197418882883571254410870077)
  ·
    refine ⟨74032081081339220404076279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197418882883571254410870077 74032081081339220404076279)
    ·
      refine ⟨111048121622008830606114419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74032081081339220404076279 111048121622008830606114419)
      ·
        refine ⟨166572182433013245909171629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111048121622008830606114419 166572182433013245909171629)
        ·
          refine ⟨62464568412379967215939361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166572182433013245909171629 62464568412379967215939361)
          ·
            refine ⟨46848426309284975411954521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62464568412379967215939361 46848426309284975411954521)
            ·
              refine ⟨35136319731963731558965891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46848426309284975411954521 35136319731963731558965891)
              ·
                refine ⟨52704479597945597338448837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35136319731963731558965891 52704479597945597338448837)
                ·
                  refine ⟨9882089924614799500959157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52704479597945597338448837 9882089924614799500959157)
                  ·
                    refine ⟨926445930432637453214921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9882089924614799500959157 926445930432637453214921)
                    ·
                      rfl

theorem cell23_5412741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_5412741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412741 prefixEnd_5412741 := by exact prefixLift 5412741
  have htrace : WordTrace (prefixWord ++ tailWord_5412741) baseStart_5412741 baseEnd_5412741 := by
    simpa [prefixWord, tailWord_5412741, baseEnd_5412741] using wordTrace_append hprefix tailTrace_5412741
  have hstable : (prefixWord ++ tailWord_5412741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412741).length < 2 ^ (prefixWord ++ tailWord_5412741).sum := by decide
  have hdescent : baseEnd_5412741 < baseStart_5412741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412761 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_5412761 : Nat := 118140960795 + 5412761 * 2 ^ 59
def prefixEnd_5412761 : Nat := 4983230072969 + 3 ^ 40 * 5412761 * 2
def baseEnd_5412761 : Nat := 2779348060911002281394671

theorem tailTrace_5412761 : CollatzResearch.WordTrace tailWord_5412761 prefixEnd_5412761 2779348060911002281394671 := by
  unfold tailWord_5412761
  simp only [CollatzResearch.WordTrace]
  refine ⟨197419612343498797826598137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131613074895665865217732091 197419612343498797826598137)
  ·
    refine ⟨148064709257624098369948603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197419612343498797826598137 148064709257624098369948603)
    ·
      refine ⟨222097063886436147554922905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148064709257624098369948603 222097063886436147554922905)
      ·
        refine ⟨166572797914827110666192179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222097063886436147554922905 166572797914827110666192179)
        ·
          refine ⟨249859196872240665999288269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166572797914827110666192179 249859196872240665999288269)
          ·
            refine ⟨93697198827090249749733101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249859196872240665999288269 93697198827090249749733101)
            ·
              refine ⟨35136449560158843656149913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93697198827090249749733101 35136449560158843656149913)
              ·
                refine ⟨26352337170119132742112435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35136449560158843656149913 26352337170119132742112435)
                ·
                  refine ⟨39528505755178699113168653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26352337170119132742112435 39528505755178699113168653)
                  ·
                    refine ⟨14823189658192012167438245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39528505755178699113168653 14823189658192012167438245)
                    ·
                      refine ⟨2779348060911002281394671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14823189658192012167438245 2779348060911002281394671)
                      ·
                        rfl

theorem cell23_5412761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_5412761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412761 prefixEnd_5412761 := by exact prefixLift 5412761
  have htrace : WordTrace (prefixWord ++ tailWord_5412761) baseStart_5412761 baseEnd_5412761 := by
    simpa [prefixWord, tailWord_5412761, baseEnd_5412761] using wordTrace_append hprefix tailTrace_5412761
  have hstable : (prefixWord ++ tailWord_5412761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412761).length < 2 ^ (prefixWord ++ tailWord_5412761).sum := by decide
  have hdescent : baseEnd_5412761 < baseStart_5412761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412848 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 1, 5]
def baseStart_5412848 : Nat := 118140960795 + 5412848 * 2 ^ 59
def prefixEnd_5412848 : Nat := 4983230072969 + 3 ^ 40 * 5412848 * 2
def baseEnd_5412848 : Nat := 926464244575981147002257

theorem tailTrace_5412848 : CollatzResearch.WordTrace tailWord_5412848 prefixEnd_5412848 926464244575981147002257 := by
  unfold tailWord_5412848
  simp only [CollatzResearch.WordTrace]
  refine ⟨98711392747091805842507599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131615190329455741123343465 98711392747091805842507599)
  ·
    refine ⟨148067089120637708763761399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98711392747091805842507599 148067089120637708763761399)
    ·
      refine ⟨222100633680956563145642099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148067089120637708763761399 222100633680956563145642099)
      ·
        refine ⟨333150950521434844718463149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222100633680956563145642099 333150950521434844718463149)
        ·
          refine ⟨124931606445538066769423681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333150950521434844718463149 124931606445538066769423681)
          ·
            refine ⟨93698704834153550077067761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124931606445538066769423681 93698704834153550077067761)
            ·
              refine ⟨70274028625615162557800821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93698704834153550077067761 70274028625615162557800821)
              ·
                refine ⟨6588190183651421489793827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70274028625615162557800821 6588190183651421489793827)
                ·
                  refine ⟨9882285275477132234690741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6588190183651421489793827 9882285275477132234690741)
                  ·
                    refine ⟨926464244575981147002257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9882285275477132234690741 926464244575981147002257)
                    ·
                      rfl

theorem cell23_5412848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_5412848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412848 prefixEnd_5412848 := by exact prefixLift 5412848
  have htrace : WordTrace (prefixWord ++ tailWord_5412848) baseStart_5412848 baseEnd_5412848 := by
    simpa [prefixWord, tailWord_5412848, baseEnd_5412848] using wordTrace_append hprefix tailTrace_5412848
  have hstable : (prefixWord ++ tailWord_5412848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412848).length < 2 ^ (prefixWord ++ tailWord_5412848).sum := by decide
  have hdescent : baseEnd_5412848 < baseStart_5412848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412912 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 2, 4]
def baseStart_5412912 : Nat := 118140960795 + 5412912 * 2 ^ 59
def prefixEnd_5412912 : Nat := 4983230072969 + 3 ^ 40 * 5412912 * 2
def baseEnd_5412912 : Nat := 926475198829943730202159

theorem tailTrace_5412912 : CollatzResearch.WordTrace tailWord_5412912 prefixEnd_5412912 926475198829943730202159 := by
  unfold tailWord_5412912
  simp only [CollatzResearch.WordTrace]
  refine ⟨98712559882975875307672495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131616746510634500410229993 98712559882975875307672495)
  ·
    refine ⟨148068839824463812961508743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98712559882975875307672495 148068839824463812961508743)
    ·
      refine ⟨222103259736695719442263115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148068839824463812961508743 222103259736695719442263115)
      ·
        refine ⟨333154889605043579163394673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222103259736695719442263115 333154889605043579163394673)
        ·
          refine ⟨249866167203782684372546005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333154889605043579163394673 249866167203782684372546005)
          ·
            refine ⟨5856238293838656664981547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 249866167203782684372546005 5856238293838656664981547)
            ·
              refine ⟨8784357440757984997472321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856238293838656664981547 8784357440757984997472321)
              ·
                refine ⟨6588268080568488748104241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8784357440757984997472321 6588268080568488748104241)
                ·
                  refine ⟨4941201060426366561078181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6588268080568488748104241 4941201060426366561078181)
                  ·
                    refine ⟨926475198829943730202159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941201060426366561078181 926475198829943730202159)
                    ·
                      rfl

theorem cell23_5412912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_5412912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412912 prefixEnd_5412912 := by exact prefixLift 5412912
  have htrace : WordTrace (prefixWord ++ tailWord_5412912) baseStart_5412912 baseEnd_5412912 := by
    simpa [prefixWord, tailWord_5412912, baseEnd_5412912] using wordTrace_append hprefix tailTrace_5412912
  have hstable : (prefixWord ++ tailWord_5412912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412912).length < 2 ^ (prefixWord ++ tailWord_5412912).sum := by decide
  have hdescent : baseEnd_5412912 < baseStart_5412912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412919 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 1, 2, 2]
def baseStart_5412919 : Nat := 118140960795 + 5412919 * 2 ^ 59
def prefixEnd_5412919 : Nat := 4983230072969 + 3 ^ 40 * 5412919 * 2
def baseEnd_5412919 : Nat := 2779429190854412663218945

theorem tailTrace_5412919 : CollatzResearch.WordTrace tailWord_5412919 prefixEnd_5412919 2779429190854412663218945 := by
  unfold tailWord_5412919
  simp only [CollatzResearch.WordTrace]
  refine ⟨197425375076926390810849811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131616916717950927207233207 197425375076926390810849811)
  ·
    refine ⟨296138062615389586216274717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197425375076926390810849811 296138062615389586216274717)
    ·
      refine ⟨111051773480771094831103019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296138062615389586216274717 111051773480771094831103019)
      ·
        refine ⟨166577660221156642246654529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111051773480771094831103019 166577660221156642246654529)
        ·
          refine ⟨124933245165867481684990897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166577660221156642246654529 124933245165867481684990897)
          ·
            refine ⟨93699933874400611263743173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124933245165867481684990897 93699933874400611263743173)
            ·
              refine ⟨17568737601450114611951845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93699933874400611263743173 17568737601450114611951845)
              ·
                refine ⟨3294138300271896489740971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17568737601450114611951845 3294138300271896489740971)
                ·
                  refine ⟨4941207450407844734611457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294138300271896489740971 4941207450407844734611457)
                  ·
                    refine ⟨3705905587805883550958593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4941207450407844734611457 3705905587805883550958593)
                    ·
                      refine ⟨2779429190854412663218945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705905587805883550958593 2779429190854412663218945)
                      ·
                        rfl

theorem cell23_5412919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_5412919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412919 prefixEnd_5412919 := by exact prefixLift 5412919
  have htrace : WordTrace (prefixWord ++ tailWord_5412919) baseStart_5412919 baseEnd_5412919 := by
    simpa [prefixWord, tailWord_5412919, baseEnd_5412919] using wordTrace_append hprefix tailTrace_5412919
  have hstable : (prefixWord ++ tailWord_5412919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412919).length < 2 ^ (prefixWord ++ tailWord_5412919).sum := by decide
  have hdescent : baseEnd_5412919 < baseStart_5412919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412929 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5412929 : Nat := 118140960795 + 5412929 * 2 ^ 59
def prefixEnd_5412929 : Nat := 4983230072969 + 3 ^ 40 * 5412929 * 2
def baseEnd_5412929 : Nat := 926478108553652541364633

theorem tailTrace_5412929 : CollatzResearch.WordTrace tailWord_5412929 prefixEnd_5412929 926478108553652541364633 := by
  unfold tailWord_5412929
  simp only [CollatzResearch.WordTrace]
  refine ⟨197425739806890162518713841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131617159871260108345809227 197425739806890162518713841)
  ·
    refine ⟨148069304855167621889035381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197425739806890162518713841 148069304855167621889035381)
    ·
      refine ⟨13881497330171964552097067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148069304855167621889035381 13881497330171964552097067)
      ·
        refine ⟨20822245995257946828145601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13881497330171964552097067 20822245995257946828145601)
        ·
          refine ⟨15616684496443460121109201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20822245995257946828145601 15616684496443460121109201)
          ·
            refine ⟨11712513372332595090831901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15616684496443460121109201 11712513372332595090831901)
            ·
              refine ⟨4392192514624723159061963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11712513372332595090831901 4392192514624723159061963)
              ·
                refine ⟨6588288771937084738592945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392192514624723159061963 6588288771937084738592945)
                ·
                  refine ⟨4941216578952813553944709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6588288771937084738592945 4941216578952813553944709)
                  ·
                    refine ⟨926478108553652541364633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941216578952813553944709 926478108553652541364633)
                    ·
                      rfl

theorem cell23_5412929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5412929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5412929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5412929 prefixEnd_5412929 := by exact prefixLift 5412929
  have htrace : WordTrace (prefixWord ++ tailWord_5412929) baseStart_5412929 baseEnd_5412929 := by
    simpa [prefixWord, tailWord_5412929, baseEnd_5412929] using wordTrace_append hprefix tailTrace_5412929
  have hstable : (prefixWord ++ tailWord_5412929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412929).length < 2 ^ (prefixWord ++ tailWord_5412929).sum := by decide
  have hdescent : baseEnd_5412929 < baseStart_5412929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413026 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_5413026 : Nat := 118140960795 + 5413026 * 2 ^ 59
def prefixEnd_5413026 : Nat := 4983230072969 + 3 ^ 40 * 5413026 * 2
def baseEnd_5413026 : Nat := 2779484133284443744580953

theorem tailTrace_5413026 : CollatzResearch.WordTrace tailWord_5413026 prefixEnd_5413026 2779484133284443744580953 := by
  unfold tailWord_5413026
  simp only [CollatzResearch.WordTrace]
  refine ⟨49357319421884687021248733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131619518458359165389996621 49357319421884687021248733)
  ·
    refine ⟨18508994783206757632968275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49357319421884687021248733 18508994783206757632968275)
    ·
      refine ⟨27763492174810136449452413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18508994783206757632968275 27763492174810136449452413)
      ·
        refine ⟨10411309565553801168544655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27763492174810136449452413 10411309565553801168544655)
        ·
          refine ⟨15616964348330701752816983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10411309565553801168544655 15616964348330701752816983)
          ·
            refine ⟨23425446522496052629225475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15616964348330701752816983 23425446522496052629225475)
            ·
              refine ⟨35138169783744078943838213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23425446522496052629225475 35138169783744078943838213)
              ·
                refine ⟨6588406834452014801969665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35138169783744078943838213 6588406834452014801969665)
                ·
                  refine ⟨4941305125839011101477249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6588406834452014801969665 4941305125839011101477249)
                  ·
                    refine ⟨3705978844379258326107937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4941305125839011101477249 3705978844379258326107937)
                    ·
                      refine ⟨2779484133284443744580953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3705978844379258326107937 2779484133284443744580953)
                      ·
                        rfl

theorem cell23_5413026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_5413026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413026 prefixEnd_5413026 := by exact prefixLift 5413026
  have htrace : WordTrace (prefixWord ++ tailWord_5413026) baseStart_5413026 baseEnd_5413026 := by
    simpa [prefixWord, tailWord_5413026, baseEnd_5413026] using wordTrace_append hprefix tailTrace_5413026
  have hstable : (prefixWord ++ tailWord_5413026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413026).length < 2 ^ (prefixWord ++ tailWord_5413026).sum := by decide
  have hdescent : baseEnd_5413026 < baseStart_5413026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413065 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_5413065 : Nat := 118140960795 + 5413065 * 2 ^ 59
def prefixEnd_5413065 : Nat := 4983230072969 + 3 ^ 40 * 5413065 * 2
def baseEnd_5413065 : Nat := 2779504159029969091993273

theorem tailTrace_5413065 : CollatzResearch.WordTrace tailWord_5413065 prefixEnd_5413065 2779504159029969091993273 := by
  unfold tailWord_5413065
  simp only [CollatzResearch.WordTrace]
  refine ⟨197430700134397457745664649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131620466756264971830443099 197430700134397457745664649)
  ·
    refine ⟨148073025100798093309248487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197430700134397457745664649 148073025100798093309248487)
    ·
      refine ⟨222109537651197139963872731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148073025100798093309248487 222109537651197139963872731)
      ·
        refine ⟨333164306476795709945809097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222109537651197139963872731 333164306476795709945809097)
        ·
          refine ⟨249873229857596782459356823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333164306476795709945809097 249873229857596782459356823)
          ·
            refine ⟨374809844786395173689035235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249873229857596782459356823 374809844786395173689035235)
            ·
              refine ⟨562214767179592760533552853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374809844786395173689035235 562214767179592760533552853)
              ·
                refine ⟨13176908605771705325005145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 562214767179592760533552853 13176908605771705325005145)
                ·
                  refine ⟨9882681454328778993753859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13176908605771705325005145 9882681454328778993753859)
                  ·
                    refine ⟨14824022181493168490630789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9882681454328778993753859 14824022181493168490630789)
                    ·
                      refine ⟨2779504159029969091993273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14824022181493168490630789 2779504159029969091993273)
                      ·
                        rfl

theorem cell23_5413065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_5413065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413065 prefixEnd_5413065 := by exact prefixLift 5413065
  have htrace : WordTrace (prefixWord ++ tailWord_5413065) baseStart_5413065 baseEnd_5413065 := by
    simpa [prefixWord, tailWord_5413065, baseEnd_5413065] using wordTrace_append hprefix tailTrace_5413065
  have hstable : (prefixWord ++ tailWord_5413065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413065).length < 2 ^ (prefixWord ++ tailWord_5413065).sum := by decide
  have hdescent : baseEnd_5413065 < baseStart_5413065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413082 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2]
def baseStart_5413082 : Nat := 118140960795 + 5413082 * 2 ^ 59
def prefixEnd_5413082 : Nat := 4983230072969 + 3 ^ 40 * 5413082 * 2
def baseEnd_5413082 : Nat := 2779512888201095525480695

theorem tailTrace_5413082 : CollatzResearch.WordTrace tailWord_5413082 prefixEnd_5413082 2779512888201095525480695 := by
  unfold tailWord_5413082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49357830043833967412258375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131620880116890579766022333 49357830043833967412258375)
  ·
    refine ⟨74036745065750951118387563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49357830043833967412258375 74036745065750951118387563)
    ·
      refine ⟨111055117598626426677581345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74036745065750951118387563 111055117598626426677581345)
      ·
        refine ⟨83291338198969820008186009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111055117598626426677581345 83291338198969820008186009)
        ·
          refine ⟨62468503649227365006139507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83291338198969820008186009 62468503649227365006139507)
          ·
            refine ⟨93702755473841047509209261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62468503649227365006139507 93702755473841047509209261)
            ·
              refine ⟨35138533302690392815953473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93702755473841047509209261 35138533302690392815953473)
              ·
                refine ⟨26353899977017794611965105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35138533302690392815953473 26353899977017794611965105)
                ·
                  refine ⟨19765424982763345958973829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26353899977017794611965105 19765424982763345958973829)
                  ·
                    refine ⟨3706017184268127367307593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19765424982763345958973829 3706017184268127367307593)
                    ·
                      refine ⟨2779512888201095525480695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706017184268127367307593 2779512888201095525480695)
                      ·
                        rfl

theorem cell23_5413082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_5413082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413082 prefixEnd_5413082 := by exact prefixLift 5413082
  have htrace : WordTrace (prefixWord ++ tailWord_5413082) baseStart_5413082 baseEnd_5413082 := by
    simpa [prefixWord, tailWord_5413082, baseEnd_5413082] using wordTrace_append hprefix tailTrace_5413082
  have hstable : (prefixWord ++ tailWord_5413082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413082).length < 2 ^ (prefixWord ++ tailWord_5413082).sum := by decide
  have hdescent : baseEnd_5413082 < baseStart_5413082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413105 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 6]
def baseStart_5413105 : Nat := 118140960795 + 5413105 * 2 ^ 59
def prefixEnd_5413105 : Nat := 4983230072969 + 3 ^ 40 * 5413105 * 2
def baseEnd_5413105 : Nat := 308836077584016548388121

theorem tailTrace_5413105 : CollatzResearch.WordTrace tailWord_5413105 prefixEnd_5413105 308836077584016548388121 := by
  unfold tailWord_5413105
  simp only [CollatzResearch.WordTrace]
  refine ⟨197432159054252544577120769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131621439369501696384747179 197432159054252544577120769)
  ·
    refine ⟨148074119290689408432840577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197432159054252544577120769 148074119290689408432840577)
    ·
      refine ⟨111055589468017056324630433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148074119290689408432840577 111055589468017056324630433)
      ·
        refine ⟨83291692101012792243472825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111055589468017056324630433 83291692101012792243472825)
        ·
          refine ⟨62468769075759594182604619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83291692101012792243472825 62468769075759594182604619)
          ·
            refine ⟨93703153613639391273906929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62468769075759594182604619 93703153613639391273906929)
            ·
              refine ⟨70277365210229543455430197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93703153613639391273906929 70277365210229543455430197)
              ·
                refine ⟨6588502988459019698946581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70277365210229543455430197 6588502988459019698946581)
                ·
                  refine ⟨308836077584016548388121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6588502988459019698946581 308836077584016548388121)
                  ·
                    rfl

theorem cell23_5413105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 6].length) (baseStart_5413105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413105 prefixEnd_5413105 := by exact prefixLift 5413105
  have htrace : WordTrace (prefixWord ++ tailWord_5413105) baseStart_5413105 baseEnd_5413105 := by
    simpa [prefixWord, tailWord_5413105, baseEnd_5413105] using wordTrace_append hprefix tailTrace_5413105
  have hstable : (prefixWord ++ tailWord_5413105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413105).length < 2 ^ (prefixWord ++ tailWord_5413105).sum := by decide
  have hdescent : baseEnd_5413105 < baseStart_5413105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413122 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_5413122 : Nat := 118140960795 + 5413122 * 2 ^ 59
def prefixEnd_5413122 : Nat := 4983230072969 + 3 ^ 40 * 5413122 * 2
def baseEnd_5413122 : Nat := 308837047491919485442279

theorem tailTrace_5413122 : CollatzResearch.WordTrace tailWord_5413122 prefixEnd_5413122 308837047491919485442279 := by
  unfold tailWord_5413122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49358194773797739120122405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131621852730127304320326413 49358194773797739120122405)
  ·
    refine ⟨9254661520087076085022951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49358194773797739120122405 9254661520087076085022951)
    ·
      refine ⟨13881992280130614127534427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254661520087076085022951 13881992280130614127534427)
      ·
        refine ⟨20822988420195921191301641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13881992280130614127534427 20822988420195921191301641)
        ·
          refine ⟨15617241315146940893476231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20822988420195921191301641 15617241315146940893476231)
          ·
            refine ⟨23425861972720411340214347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15617241315146940893476231 23425861972720411340214347)
            ·
              refine ⟨35138792959080617010321521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23425861972720411340214347 35138792959080617010321521)
              ·
                refine ⟨26354094719310462757741141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35138792959080617010321521 26354094719310462757741141)
                ·
                  refine ⟨308837047491919485442279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26354094719310462757741141 308837047491919485442279)
                  ·
                    rfl

theorem cell23_5413122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_5413122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413122 prefixEnd_5413122 := by exact prefixLift 5413122
  have htrace : WordTrace (prefixWord ++ tailWord_5413122) baseStart_5413122 baseEnd_5413122 := by
    simpa [prefixWord, tailWord_5413122, baseEnd_5413122] using wordTrace_append hprefix tailTrace_5413122
  have hstable : (prefixWord ++ tailWord_5413122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413122).length < 2 ^ (prefixWord ++ tailWord_5413122).sum := by decide
  have hdescent : baseEnd_5413122 < baseStart_5413122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413175 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_5413175 : Nat := 118140960795 + 5413175 * 2 ^ 59
def prefixEnd_5413175 : Nat := 4983230072969 + 3 ^ 40 * 5413175 * 2
def baseEnd_5413175 : Nat := 2779560641901963661617767

theorem tailTrace_5413175 : CollatzResearch.WordTrace tailWord_5413175 prefixEnd_5413175 2779560641901963661617767 := by
  unfold tailWord_5413175
  simp only [CollatzResearch.WordTrace]
  refine ⟨197434712163998946532168979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131623141442665964354779319 197434712163998946532168979)
  ·
    refine ⟨296152068245998419798253469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197434712163998946532168979 296152068245998419798253469)
    ·
      refine ⟨111057025592249407424345051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296152068245998419798253469 111057025592249407424345051)
      ·
        refine ⟨166585538388374111136517577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111057025592249407424345051 166585538388374111136517577)
        ·
          refine ⟨124939153791280583352388183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166585538388374111136517577 124939153791280583352388183)
          ·
            refine ⟨187408730686920875028582275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124939153791280583352388183 187408730686920875028582275)
            ·
              refine ⟨281113096030381312542873413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187408730686920875028582275 281113096030381312542873413)
              ·
                refine ⟨52708705505696496101788765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281113096030381312542873413 52708705505696496101788765)
                ·
                  refine ⟨19765764564636186038170787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52708705505696496101788765 19765764564636186038170787)
                  ·
                    refine ⟨29648646846954279057256181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19765764564636186038170787 29648646846954279057256181)
                    ·
                      refine ⟨2779560641901963661617767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29648646846954279057256181 2779560641901963661617767)
                      ·
                        rfl

theorem cell23_5413175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_5413175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413175 prefixEnd_5413175 := by exact prefixLift 5413175
  have htrace : WordTrace (prefixWord ++ tailWord_5413175) baseStart_5413175 baseEnd_5413175 := by
    simpa [prefixWord, tailWord_5413175, baseEnd_5413175] using wordTrace_append hprefix tailTrace_5413175
  have hstable : (prefixWord ++ tailWord_5413175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413175).length < 2 ^ (prefixWord ++ tailWord_5413175).sum := by decide
  have hdescent : baseEnd_5413175 < baseStart_5413175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413182 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_5413182 : Nat := 118140960795 + 5413182 * 2 ^ 59
def prefixEnd_5413182 : Nat := 4983230072969 + 3 ^ 40 * 5413182 * 2
def baseEnd_5413182 : Nat := 926521412088848378076745

theorem tailTrace_5413182 : CollatzResearch.WordTrace tailWord_5413182 prefixEnd_5413182 926521412088848378076745 := by
  unfold tailWord_5413182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24679370934371698340959225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131623311649982391151782533 24679370934371698340959225)
  ·
    refine ⟨18509528200778773755719419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24679370934371698340959225 18509528200778773755719419)
    ·
      refine ⟨27764292301168160633579129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18509528200778773755719419 27764292301168160633579129)
      ·
        refine ⟨20823219225876120475184347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27764292301168160633579129 20823219225876120475184347)
        ·
          refine ⟨31234828838814180712776521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20823219225876120475184347 31234828838814180712776521)
          ·
            refine ⟨23426121629110635534582391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31234828838814180712776521 23426121629110635534582391)
            ·
              refine ⟨35139182443665953301873587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23426121629110635534582391 35139182443665953301873587)
              ·
                refine ⟨52708773665498929952810381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35139182443665953301873587 52708773665498929952810381)
                ·
                  refine ⟨19765790124562098732303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52708773665498929952810381 19765790124562098732303893)
                  ·
                    refine ⟨926521412088848378076745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19765790124562098732303893 926521412088848378076745)
                    ·
                      rfl

theorem cell23_5413182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_5413182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413182 prefixEnd_5413182 := by exact prefixLift 5413182
  have htrace : WordTrace (prefixWord ++ tailWord_5413182) baseStart_5413182 baseEnd_5413182 := by
    simpa [prefixWord, tailWord_5413182, baseEnd_5413182] using wordTrace_append hprefix tailTrace_5413182
  have hstable : (prefixWord ++ tailWord_5413182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413182).length < 2 ^ (prefixWord ++ tailWord_5413182).sum := by decide
  have hdescent : baseEnd_5413182 < baseStart_5413182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413192 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_5413192 : Nat := 118140960795 + 5413192 * 2 ^ 59
def prefixEnd_5413192 : Nat := 4983230072969 + 3 ^ 40 * 5413192 * 2
def baseEnd_5413192 : Nat := 2779569371073090095105189

theorem tailTrace_5413192 : CollatzResearch.WordTrace tailWord_5413192 prefixEnd_5413192 2779569371073090095105189 := by
  unfold tailWord_5413192
  simp only [CollatzResearch.WordTrace]
  refine ⟨98717666102468679217768915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131623554803291572290358553 98717666102468679217768915)
  ·
    refine ⟨148076499153703018826653373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98717666102468679217768915 148076499153703018826653373)
    ·
      refine ⟨55528687182638632059995015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148076499153703018826653373 55528687182638632059995015)
      ·
        refine ⟨83293030773957948089992523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55528687182638632059995015 83293030773957948089992523)
        ·
          refine ⟨124939546160936922134988785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83293030773957948089992523 124939546160936922134988785)
          ·
            refine ⟨93704659620702691601241589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124939546160936922134988785 93704659620702691601241589)
            ·
              refine ⟨8784811839440877337616399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93704659620702691601241589 8784811839440877337616399)
              ·
                refine ⟨13177217759161316006424599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8784811839440877337616399 13177217759161316006424599)
                ·
                  refine ⟨19765826638741974009636899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13177217759161316006424599 19765826638741974009636899)
                  ·
                    refine ⟨29648739958112961014455349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19765826638741974009636899 29648739958112961014455349)
                    ·
                      refine ⟨2779569371073090095105189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29648739958112961014455349 2779569371073090095105189)
                      ·
                        rfl

theorem cell23_5413192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_5413192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413192 prefixEnd_5413192 := by exact prefixLift 5413192
  have htrace : WordTrace (prefixWord ++ tailWord_5413192) baseStart_5413192 baseEnd_5413192 := by
    simpa [prefixWord, tailWord_5413192, baseEnd_5413192] using wordTrace_append hprefix tailTrace_5413192
  have hstable : (prefixWord ++ tailWord_5413192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413192).length < 2 ^ (prefixWord ++ tailWord_5413192).sum := by decide
  have hdescent : baseEnd_5413192 < baseStart_5413192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413215 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_5413215 : Nat := 118140960795 + 5413215 * 2 ^ 59
def prefixEnd_5413215 : Nat := 4983230072969 + 3 ^ 40 * 5413215 * 2
def baseEnd_5413215 : Nat := 2779581181128143505117583

theorem tailTrace_5413215 : CollatzResearch.WordTrace tailWord_5413215 prefixEnd_5413215 2779581181128143505117583 := by
  unfold tailWord_5413215
  simp only [CollatzResearch.WordTrace]
  refine ⟨197436171083854033363625099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131624114055902688909083399 197436171083854033363625099)
  ·
    refine ⟨296154256625781050045437649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197436171083854033363625099 296154256625781050045437649)
    ·
      refine ⟨222115692469335787534078237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296154256625781050045437649 222115692469335787534078237)
      ·
        refine ⟨83293384676000920325279339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222115692469335787534078237 83293384676000920325279339)
        ·
          refine ⟨124940077014001380487919009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83293384676000920325279339 124940077014001380487919009)
          ·
            refine ⟨93705057760501035365939257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124940077014001380487919009 93705057760501035365939257)
            ·
              refine ⟨70278793320375776524454443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93705057760501035365939257 70278793320375776524454443)
              ·
                refine ⟨105418189980563664786681665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70278793320375776524454443 105418189980563664786681665)
                ·
                  refine ⟨79063642485422748590011249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105418189980563664786681665 79063642485422748590011249)
                  ·
                    refine ⟨59297731864067061442508437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79063642485422748590011249 59297731864067061442508437)
                    ·
                      refine ⟨2779581181128143505117583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59297731864067061442508437 2779581181128143505117583)
                      ·
                        rfl

theorem cell23_5413215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_5413215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413215 prefixEnd_5413215 := by exact prefixLift 5413215
  have htrace : WordTrace (prefixWord ++ tailWord_5413215) baseStart_5413215 baseEnd_5413215 := by
    simpa [prefixWord, tailWord_5413215, baseEnd_5413215] using wordTrace_append hprefix tailTrace_5413215
  have hstable : (prefixWord ++ tailWord_5413215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413215).length < 2 ^ (prefixWord ++ tailWord_5413215).sum := by decide
  have hdescent : baseEnd_5413215 < baseStart_5413215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413225 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_5413225 : Nat := 118140960795 + 5413225 * 2 ^ 59
def prefixEnd_5413225 : Nat := 4983230072969 + 3 ^ 40 * 5413225 * 2
def baseEnd_5413225 : Nat := 926528771978229488664179

theorem tailTrace_5413225 : CollatzResearch.WordTrace tailWord_5413225 prefixEnd_5413225 926528771978229488664179 := by
  unfold tailWord_5413225
  simp only [CollatzResearch.WordTrace]
  refine ⟨197436535813817805071489129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131624357209211870047659419 197436535813817805071489129)
  ·
    refine ⟨148077401860363353803616847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197436535813817805071489129 148077401860363353803616847)
    ·
      refine ⟨222116102790545030705425271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148077401860363353803616847 222116102790545030705425271)
      ·
        refine ⟨333174154185817546058137907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222116102790545030705425271 333174154185817546058137907)
        ·
          refine ⟨499761231278726319087206861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333174154185817546058137907 499761231278726319087206861)
          ·
            refine ⟨187410461729522369657702573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499761231278726319087206861 187410461729522369657702573)
            ·
              refine ⟨70278923148570888621638465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187410461729522369657702573 70278923148570888621638465)
              ·
                refine ⟨52709192361428166466228849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70278923148570888621638465 52709192361428166466228849)
                ·
                  refine ⟨39531894271071124849671637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52709192361428166466228849 39531894271071124849671637)
                  ·
                    refine ⟨926528771978229488664179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39531894271071124849671637 926528771978229488664179)
                    ·
                      rfl

theorem cell23_5413225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_5413225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413225 prefixEnd_5413225 := by exact prefixLift 5413225
  have htrace : WordTrace (prefixWord ++ tailWord_5413225) baseStart_5413225 baseEnd_5413225 := by
    simpa [prefixWord, tailWord_5413225, baseEnd_5413225] using wordTrace_append hprefix tailTrace_5413225
  have hstable : (prefixWord ++ tailWord_5413225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413225).length < 2 ^ (prefixWord ++ tailWord_5413225).sum := by decide
  have hdescent : baseEnd_5413225 < baseStart_5413225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413235 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_5413235 : Nat := 118140960795 + 5413235 * 2 ^ 59
def prefixEnd_5413235 : Nat := 4983230072969 + 3 ^ 40 * 5413235 * 2
def baseEnd_5413235 : Nat := 2779591450741233426867491

theorem tailTrace_5413235 : CollatzResearch.WordTrace tailWord_5413235 prefixEnd_5413235 2779591450741233426867491 := by
  unfold tailWord_5413235
  simp only [CollatzResearch.WordTrace]
  refine ⟨197436900543781576779353159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131624600362521051186235439 197436900543781576779353159)
  ·
    refine ⟨296155350815672365169029739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197436900543781576779353159 296155350815672365169029739)
    ·
      refine ⟨444233026223508547753544609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296155350815672365169029739 444233026223508547753544609)
      ·
        refine ⟨333174769667631410815158457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444233026223508547753544609 333174769667631410815158457)
        ·
          refine ⟨249881077250723558111368843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333174769667631410815158457 249881077250723558111368843)
          ·
            refine ⟨374821615876085337167053265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249881077250723558111368843 374821615876085337167053265)
            ·
              refine ⟨281116211907064002875289949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374821615876085337167053265 281116211907064002875289949)
              ·
                refine ⟨105418579465149001078233731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281116211907064002875289949 105418579465149001078233731)
                ·
                  refine ⟨158127869197723501617350597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105418579465149001078233731 158127869197723501617350597)
                  ·
                    refine ⟨29648975474573156553253237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158127869197723501617350597 29648975474573156553253237)
                    ·
                      refine ⟨2779591450741233426867491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29648975474573156553253237 2779591450741233426867491)
                      ·
                        rfl

theorem cell23_5413235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_5413235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413235 prefixEnd_5413235 := by exact prefixLift 5413235
  have htrace : WordTrace (prefixWord ++ tailWord_5413235) baseStart_5413235 baseEnd_5413235 := by
    simpa [prefixWord, tailWord_5413235, baseEnd_5413235] using wordTrace_append hprefix tailTrace_5413235
  have hstable : (prefixWord ++ tailWord_5413235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413235).length < 2 ^ (prefixWord ++ tailWord_5413235).sum := by decide
  have hdescent : baseEnd_5413235 < baseStart_5413235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413250 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5413250 : Nat := 118140960795 + 5413250 * 2 ^ 59
def prefixEnd_5413250 : Nat := 4983230072969 + 3 ^ 40 * 5413250 * 2
def baseEnd_5413250 : Nat := 926533050983683622726641

theorem tailTrace_5413250 : CollatzResearch.WordTrace tailWord_5413250 prefixEnd_5413250 926533050983683622726641 := by
  unfold tailWord_5413250
  simp only [CollatzResearch.WordTrace]
  refine ⟨49359361909681808585287301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131624965092484822894099469 49359361909681808585287301)
  ·
    refine ⟨9254880358065339109741369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49359361909681808585287301 9254880358065339109741369)
    ·
      refine ⟨6941160268549004332306027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9254880358065339109741369 6941160268549004332306027)
      ·
        refine ⟨10411740402823506498459041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6941160268549004332306027 10411740402823506498459041)
        ·
          refine ⟨7808805302117629873844281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10411740402823506498459041 7808805302117629873844281)
          ·
            refine ⟨5856603976588222405383211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7808805302117629873844281 5856603976588222405383211)
            ·
              refine ⟨8784905964882333608074817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856603976588222405383211 8784905964882333608074817)
              ·
                refine ⟨6588679473661750206056113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8784905964882333608074817 6588679473661750206056113)
                ·
                  refine ⟨4941509605246312654542085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6588679473661750206056113 4941509605246312654542085)
                  ·
                    refine ⟨926533050983683622726641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941509605246312654542085 926533050983683622726641)
                    ·
                      rfl

theorem cell23_5413250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5413250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413250 prefixEnd_5413250 := by exact prefixLift 5413250
  have htrace : WordTrace (prefixWord ++ tailWord_5413250) baseStart_5413250 baseEnd_5413250 := by
    simpa [prefixWord, tailWord_5413250, baseEnd_5413250] using wordTrace_append hprefix tailTrace_5413250
  have hstable : (prefixWord ++ tailWord_5413250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413250).length < 2 ^ (prefixWord ++ tailWord_5413250).sum := by decide
  have hdescent : baseEnd_5413250 < baseStart_5413250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413319 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 7]
def baseStart_5413319 : Nat := 118140960795 + 5413319 * 2 ^ 59
def prefixEnd_5413319 : Nat := 4983230072969 + 3 ^ 40 * 5413319 * 2
def baseEnd_5413319 : Nat := 308848287012912344246345

theorem tailTrace_5413319 : CollatzResearch.WordTrace tailWord_5413319 prefixEnd_5413319 308848287012912344246345 := by
  unfold tailWord_5413319
  simp only [CollatzResearch.WordTrace]
  refine ⟨197439964275477259125411011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131626642850318172750274007 197439964275477259125411011)
  ·
    refine ⟨296159946413215888688116517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197439964275477259125411011 296159946413215888688116517)
    ·
      refine ⟨55529989952477979129021847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296159946413215888688116517 55529989952477979129021847)
      ·
        refine ⟨83294984928716968693532771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55529989952477979129021847 83294984928716968693532771)
        ·
          refine ⟨124942477393075453040299157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83294984928716968693532771 124942477393075453040299157)
          ·
            refine ⟨5856678627800411861264023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124942477393075453040299157 5856678627800411861264023)
            ·
              refine ⟨8785017941700617791896035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856678627800411861264023 8785017941700617791896035)
              ·
                refine ⟨13177526912550926687844053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8785017941700617791896035 13177526912550926687844053)
                ·
                  refine ⟨308848287012912344246345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13177526912550926687844053 308848287012912344246345)
                  ·
                    rfl

theorem cell23_5413319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 7].length) (baseStart_5413319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413319 prefixEnd_5413319 := by exact prefixLift 5413319
  have htrace : WordTrace (prefixWord ++ tailWord_5413319) baseStart_5413319 baseEnd_5413319 := by
    simpa [prefixWord, tailWord_5413319, baseEnd_5413319] using wordTrace_append hprefix tailTrace_5413319
  have hstable : (prefixWord ++ tailWord_5413319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413319).length < 2 ^ (prefixWord ++ tailWord_5413319).sum := by decide
  have hdescent : baseEnd_5413319 < baseStart_5413319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413369 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_5413369 : Nat := 118140960795 + 5413369 * 2 ^ 59
def prefixEnd_5413369 : Nat := 4983230072969 + 3 ^ 40 * 5413369 * 2
def baseEnd_5413369 : Nat := 2779660257148935902591875

theorem tailTrace_5413369 : CollatzResearch.WordTrace tailWord_5413369 prefixEnd_5413369 2779660257148935902591875 := by
  unfold tailWord_5413369
  simp only [CollatzResearch.WordTrace]
  refine ⟨197441787925296117664731161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131627858616864078443154107 197441787925296117664731161)
  ·
    refine ⟨148081340943972088248548371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197441787925296117664731161 148081340943972088248548371)
    ·
      refine ⟨222122011415958132372822557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148081340943972088248548371 222122011415958132372822557)
      ·
        refine ⟨83295754280984299639808459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222122011415958132372822557 83295754280984299639808459)
        ·
          refine ⟨124943631421476449459712689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83295754280984299639808459 124943631421476449459712689)
          ·
            refine ⟨93707723566107337094784517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124943631421476449459712689 93707723566107337094784517)
            ·
              refine ⟨17570198168645125705272097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93707723566107337094784517 17570198168645125705272097)
              ·
                refine ⟨13177648626483844278954073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17570198168645125705272097 13177648626483844278954073)
                ·
                  refine ⟨9883236469862883209215555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13177648626483844278954073 9883236469862883209215555)
                  ·
                    refine ⟨14824854704794324813823333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9883236469862883209215555 14824854704794324813823333)
                    ·
                      refine ⟨2779660257148935902591875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14824854704794324813823333 2779660257148935902591875)
                      ·
                        rfl

theorem cell23_5413369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_5413369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413369 prefixEnd_5413369 := by exact prefixLift 5413369
  have htrace : WordTrace (prefixWord ++ tailWord_5413369) baseStart_5413369 baseEnd_5413369 := by
    simpa [prefixWord, tailWord_5413369, baseEnd_5413369] using wordTrace_append hprefix tailTrace_5413369
  have hstable : (prefixWord ++ tailWord_5413369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413369).length < 2 ^ (prefixWord ++ tailWord_5413369).sum := by decide
  have hdescent : baseEnd_5413369 < baseStart_5413369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413372 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_5413372 : Nat := 118140960795 + 5413372 * 2 ^ 59
def prefixEnd_5413372 : Nat := 4983230072969 + 3 ^ 40 * 5413372 * 2
def baseEnd_5413372 : Nat := 2779661797590899390854361

theorem tailTrace_5413372 : CollatzResearch.WordTrace tailWord_5413372 prefixEnd_5413372 2779661797590899390854361 := by
  unfold tailWord_5413372
  simp only [CollatzResearch.WordTrace]
  refine ⟨98720948672142624588545185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131627931562856832784726913 98720948672142624588545185)
  ·
    refine ⟨74040711504106968441408889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98720948672142624588545185 74040711504106968441408889)
    ·
      refine ⟨55530533628080226331056667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74040711504106968441408889 55530533628080226331056667)
      ·
        refine ⟨83295800442120339496585001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55530533628080226331056667 83295800442120339496585001)
        ·
          refine ⟨62471850331590254622438751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83295800442120339496585001 62471850331590254622438751)
          ·
            refine ⟨93707775497385381933658127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62471850331590254622438751 93707775497385381933658127)
            ·
              refine ⟨140561663246078072900487191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93707775497385381933658127 140561663246078072900487191)
              ·
                refine ⟨210842494869117109350730787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140561663246078072900487191 210842494869117109350730787)
                ·
                  refine ⟨316263742303675664026096181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210842494869117109350730787 316263742303675664026096181)
                  ·
                    refine ⟨29649725840969593502446517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 316263742303675664026096181 29649725840969593502446517)
                    ·
                      refine ⟨2779661797590899390854361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29649725840969593502446517 2779661797590899390854361)
                      ·
                        rfl

theorem cell23_5413372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_5413372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413372 prefixEnd_5413372 := by exact prefixLift 5413372
  have htrace : WordTrace (prefixWord ++ tailWord_5413372) baseStart_5413372 baseEnd_5413372 := by
    simpa [prefixWord, tailWord_5413372, baseEnd_5413372] using wordTrace_append hprefix tailTrace_5413372
  have hstable : (prefixWord ++ tailWord_5413372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413372).length < 2 ^ (prefixWord ++ tailWord_5413372).sum := by decide
  have hdescent : baseEnd_5413372 < baseStart_5413372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413379 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 3, 4]
def baseStart_5413379 : Nat := 118140960795 + 5413379 * 2 ^ 59
def prefixEnd_5413379 : Nat := 4983230072969 + 3 ^ 40 * 5413379 * 2
def baseEnd_5413379 : Nat := 926555130651826954488943

theorem tailTrace_5413379 : CollatzResearch.WordTrace tailWord_5413379 prefixEnd_5413379 926555130651826954488943 := by
  unfold tailWord_5413379
  simp only [CollatzResearch.WordTrace]
  refine ⟨197442152655259889372595191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131628101770173259581730127 197442152655259889372595191)
  ·
    refine ⟨296163228982889834058892787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197442152655259889372595191 296163228982889834058892787)
    ·
      refine ⟨444244843474334751088339181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296163228982889834058892787 444244843474334751088339181)
      ·
        refine ⟨166591816302875531658127193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444244843474334751088339181 166591816302875531658127193)
        ·
          refine ⟨124943862227156648743595395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166591816302875531658127193 124943862227156648743595395)
          ·
            refine ⟨187415793340734973115393093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124943862227156648743595395 187415793340734973115393093)
            ·
              refine ⟨35140461251387807459136205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187415793340734973115393093 35140461251387807459136205)
              ·
                refine ⟨13177672969270427797176077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35140461251387807459136205 13177672969270427797176077)
                ·
                  refine ⟨4941627363476410423941029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13177672969270427797176077 4941627363476410423941029)
                  ·
                    refine ⟨926555130651826954488943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941627363476410423941029 926555130651826954488943)
                    ·
                      rfl

theorem cell23_5413379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 4].length) (baseStart_5413379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413379 prefixEnd_5413379 := by exact prefixLift 5413379
  have htrace : WordTrace (prefixWord ++ tailWord_5413379) baseStart_5413379 baseEnd_5413379 := by
    simpa [prefixWord, tailWord_5413379, baseEnd_5413379] using wordTrace_append hprefix tailTrace_5413379
  have hstable : (prefixWord ++ tailWord_5413379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413379).length < 2 ^ (prefixWord ++ tailWord_5413379).sum := by decide
  have hdescent : baseEnd_5413379 < baseStart_5413379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413386 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_5413386 : Nat := 118140960795 + 5413386 * 2 ^ 59
def prefixEnd_5413386 : Nat := 4983230072969 + 3 ^ 40 * 5413386 * 2
def baseEnd_5413386 : Nat := 2779668986320062336079297

theorem tailTrace_5413386 : CollatzResearch.WordTrace tailWord_5413386 prefixEnd_5413386 2779668986320062336079297 := by
  unfold tailWord_5413386
  simp only [CollatzResearch.WordTrace]
  refine ⟨49360601991558632392025003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131628271977489686378733341 49360601991558632392025003)
  ·
    refine ⟨74040902987337948588037505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49360601991558632392025003 74040902987337948588037505)
    ·
      refine ⟨55530677240503461441028129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74040902987337948588037505 55530677240503461441028129)
      ·
        refine ⟨41648007930377596080771097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55530677240503461441028129 41648007930377596080771097)
        ·
          refine ⟨31236005947783197060578323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41648007930377596080771097 31236005947783197060578323)
          ·
            refine ⟨46854008921674795590867485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31236005947783197060578323 46854008921674795590867485)
            ·
              refine ⟨17570253345628048346575307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46854008921674795590867485 17570253345628048346575307)
              ·
                refine ⟨26355380018442072519862961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17570253345628048346575307 26355380018442072519862961)
                ·
                  refine ⟨19766535013831554389897221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26355380018442072519862961 19766535013831554389897221)
                  ·
                    refine ⟨3706225315093416448105729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19766535013831554389897221 3706225315093416448105729)
                    ·
                      refine ⟨2779668986320062336079297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706225315093416448105729 2779668986320062336079297)
                      ·
                        rfl

theorem cell23_5413386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_5413386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413386 prefixEnd_5413386 := by exact prefixLift 5413386
  have htrace : WordTrace (prefixWord ++ tailWord_5413386) baseStart_5413386 baseEnd_5413386 := by
    simpa [prefixWord, tailWord_5413386, baseEnd_5413386] using wordTrace_append hprefix tailTrace_5413386
  have hstable : (prefixWord ++ tailWord_5413386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413386).length < 2 ^ (prefixWord ++ tailWord_5413386).sum := by decide
  have hdescent : baseEnd_5413386 < baseStart_5413386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413430 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5413430 : Nat := 118140960795 + 5413430 * 2 ^ 59
def prefixEnd_5413430 : Nat := 4983230072969 + 3 ^ 40 * 5413430 * 2
def baseEnd_5413430 : Nat := 926563859822953387976365

theorem tailTrace_5413430 : CollatzResearch.WordTrace tailWord_5413430 prefixEnd_5413430 926563859822953387976365 := by
  unfold tailWord_5413430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12340250798629695317668859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131629341852050083388467829 12340250798629695317668859)
  ·
    refine ⟨18510376197944542976503289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12340250798629695317668859 18510376197944542976503289)
    ·
      refine ⟨13882782148458407232377467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18510376197944542976503289 13882782148458407232377467)
      ·
        refine ⟨20824173222687610848566201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13882782148458407232377467 20824173222687610848566201)
        ·
          refine ⟨15618129917015708136424651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20824173222687610848566201 15618129917015708136424651)
          ·
            refine ⟨23427194875523562204636977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15618129917015708136424651 23427194875523562204636977)
            ·
              refine ⟨17570396156642671653477733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23427194875523562204636977 17570396156642671653477733)
              ·
                refine ⟨3294449279370500935027075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17570396156642671653477733 3294449279370500935027075)
                ·
                  refine ⟨4941673919055751402540613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294449279370500935027075 4941673919055751402540613)
                  ·
                    refine ⟨926563859822953387976365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941673919055751402540613 926563859822953387976365)
                    ·
                      rfl

theorem cell23_5413430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5413430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413430 prefixEnd_5413430 := by exact prefixLift 5413430
  have htrace : WordTrace (prefixWord ++ tailWord_5413430) baseStart_5413430 baseEnd_5413430 := by
    simpa [prefixWord, tailWord_5413430, baseEnd_5413430] using wordTrace_append hprefix tailTrace_5413430
  have hstable : (prefixWord ++ tailWord_5413430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413430).length < 2 ^ (prefixWord ++ tailWord_5413430).sum := by decide
  have hdescent : baseEnd_5413430 < baseStart_5413430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413476 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_5413476 : Nat := 118140960795 + 5413476 * 2 ^ 59
def prefixEnd_5413476 : Nat := 4983230072969 + 3 ^ 40 * 5413476 * 2
def baseEnd_5413476 : Nat := 2779715199578966983953883

theorem tailTrace_5413476 : CollatzResearch.WordTrace tailWord_5413476 prefixEnd_5413476 2779715199578966983953883 := by
  unfold tailWord_5413476
  simp only [CollatzResearch.WordTrace]
  refine ⟨98722845267954237469438141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131630460357272316625917521 98722845267954237469438141)
  ·
    refine ⟨37021066975482839051039303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98722845267954237469438141 37021066975482839051039303)
    ·
      refine ⟨55531600463224258576558955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37021066975482839051039303 55531600463224258576558955)
      ·
        refine ⟨83297400694836387864838433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55531600463224258576558955 83297400694836387864838433)
        ·
          refine ⟨62473050521127290898628825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83297400694836387864838433 62473050521127290898628825)
          ·
            refine ⟨46854787890845468173971619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62473050521127290898628825 46854787890845468173971619)
            ·
              refine ⟨70282181836268202260957429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46854787890845468173971619 70282181836268202260957429)
              ·
                refine ⟨6588954547150143961964759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70282181836268202260957429 6588954547150143961964759)
                ·
                  refine ⟨9883431820725215942947139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6588954547150143961964759 9883431820725215942947139)
                  ·
                    refine ⟨14825147731087823914420709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9883431820725215942947139 14825147731087823914420709)
                    ·
                      refine ⟨2779715199578966983953883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14825147731087823914420709 2779715199578966983953883)
                      ·
                        rfl

theorem cell23_5413476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_5413476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413476 prefixEnd_5413476 := by exact prefixLift 5413476
  have htrace : WordTrace (prefixWord ++ tailWord_5413476) baseStart_5413476 baseEnd_5413476 := by
    simpa [prefixWord, tailWord_5413476, baseEnd_5413476] using wordTrace_append hprefix tailTrace_5413476
  have hstable : (prefixWord ++ tailWord_5413476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413476).length < 2 ^ (prefixWord ++ tailWord_5413476).sum := by decide
  have hdescent : baseEnd_5413476 < baseStart_5413476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413480 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5413480 : Nat := 118140960795 + 5413480 * 2 ^ 59
def prefixEnd_5413480 : Nat := 4983230072969 + 3 ^ 40 * 5413480 * 2
def baseEnd_5413480 : Nat := 2779717253501584968303865

theorem tailTrace_5413480 : CollatzResearch.WordTrace tailWord_5413480 prefixEnd_5413480 2779717253501584968303865 := by
  unfold tailWord_5413480
  simp only [CollatzResearch.WordTrace]
  refine ⟨98722918213946991811010947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131630557618595989081347929 98722918213946991811010947)
  ·
    refine ⟨148084377320920487716516421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98722918213946991811010947 148084377320920487716516421)
    ·
      refine ⟨27765820747672591446846829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148084377320920487716516421 27765820747672591446846829)
      ·
        refine ⟨10412182780377221792567561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27765820747672591446846829 10412182780377221792567561)
        ·
          refine ⟨7809137085282916344425671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10412182780377221792567561 7809137085282916344425671)
          ·
            refine ⟨11713705627924374516638507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7809137085282916344425671 11713705627924374516638507)
            ·
              refine ⟨17570558441886561774957761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11713705627924374516638507 17570558441886561774957761)
              ·
                refine ⟨13177918831414921331218321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17570558441886561774957761 13177918831414921331218321)
                ·
                  refine ⟨9883439123561190998413741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13177918831414921331218321 9883439123561190998413741)
                  ·
                    refine ⟨3706289671335446624405153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9883439123561190998413741 3706289671335446624405153)
                    ·
                      refine ⟨2779717253501584968303865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706289671335446624405153 2779717253501584968303865)
                      ·
                        rfl

theorem cell23_5413480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5413480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413480 prefixEnd_5413480 := by exact prefixLift 5413480
  have htrace : WordTrace (prefixWord ++ tailWord_5413480) baseStart_5413480 baseEnd_5413480 := by
    simpa [prefixWord, tailWord_5413480, baseEnd_5413480] using wordTrace_append hprefix tailTrace_5413480
  have hstable : (prefixWord ++ tailWord_5413480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413480).length < 2 ^ (prefixWord ++ tailWord_5413480).sum := by decide
  have hdescent : baseEnd_5413480 < baseStart_5413480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413530 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5413530 : Nat := 118140960795 + 5413530 * 2 ^ 59
def prefixEnd_5413530 : Nat := 4983230072969 + 3 ^ 40 * 5413530 * 2
def baseEnd_5413530 : Nat := 2779742927534309772678635

theorem tailTrace_5413530 : CollatzResearch.WordTrace tailWord_5413530 prefixEnd_5413530 2779742927534309772678635 := by
  unfold tailWord_5413530
  simp only [CollatzResearch.WordTrace]
  refine ⟨49361915019428210540335511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131631773385141894774228029 49361915019428210540335511)
  ·
    refine ⟨74042872529142315810503267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49361915019428210540335511 74042872529142315810503267)
    ·
      refine ⟨111064308793713473715754901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74042872529142315810503267 111064308793713473715754901)
      ·
        refine ⟨5206139474705319080426011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111064308793713473715754901 5206139474705319080426011)
        ·
          refine ⟨7809209212057978620639017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5206139474705319080426011 7809209212057978620639017)
          ·
            refine ⟨5856906909043483965479263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7809209212057978620639017 5856906909043483965479263)
            ·
              refine ⟨8785360363565225948218895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856906909043483965479263 8785360363565225948218895)
              ·
                refine ⟨13178040545347838922328343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8785360363565225948218895 13178040545347838922328343)
                ·
                  refine ⟨19767060818021758383492515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13178040545347838922328343 19767060818021758383492515)
                  ·
                    refine ⟨29650591227032637575238773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19767060818021758383492515 29650591227032637575238773)
                    ·
                      refine ⟨2779742927534309772678635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29650591227032637575238773 2779742927534309772678635)
                      ·
                        rfl

theorem cell23_5413530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5413530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413530 prefixEnd_5413530 := by exact prefixLift 5413530
  have htrace : WordTrace (prefixWord ++ tailWord_5413530) baseStart_5413530 baseEnd_5413530 := by
    simpa [prefixWord, tailWord_5413530, baseEnd_5413530] using wordTrace_append hprefix tailTrace_5413530
  have hstable : (prefixWord ++ tailWord_5413530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413530).length < 2 ^ (prefixWord ++ tailWord_5413530).sum := by decide
  have hdescent : baseEnd_5413530 < baseStart_5413530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413566 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5413566 : Nat := 118140960795 + 5413566 * 2 ^ 59
def prefixEnd_5413566 : Nat := 4983230072969 + 3 ^ 40 * 5413566 * 2
def baseEnd_5413566 : Nat := 2779761412837871631828469

theorem tailTrace_5413566 : CollatzResearch.WordTrace tailWord_5413566 prefixEnd_5413566 2779761412837871631828469 := by
  unfold tailWord_5413566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24681121638197802538706569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131632648737054946873101701 24681121638197802538706569)
  ·
    refine ⟨18510841228648351904029927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24681121638197802538706569 18510841228648351904029927)
    ·
      refine ⟨27766261842972527856044891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18510841228648351904029927 27766261842972527856044891)
      ·
        refine ⟨41649392764458791784067337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27766261842972527856044891 41649392764458791784067337)
        ·
          refine ⟨31237044573344093838050503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41649392764458791784067337 31237044573344093838050503)
          ·
            refine ⟨46855566860016140757075755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31237044573344093838050503 46855566860016140757075755)
            ·
              refine ⟨70283350290024211135613633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46855566860016140757075755 70283350290024211135613633)
              ·
                refine ⟨52712512717518158351710225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70283350290024211135613633 52712512717518158351710225)
                ·
                  refine ⟨39534384538138618763782669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52712512717518158351710225 39534384538138618763782669)
                  ·
                    refine ⟨14825394201801982036418501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39534384538138618763782669 14825394201801982036418501)
                    ·
                      refine ⟨2779761412837871631828469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14825394201801982036418501 2779761412837871631828469)
                      ·
                        rfl

theorem cell23_5413566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5413566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413566 prefixEnd_5413566 := by exact prefixLift 5413566
  have htrace : WordTrace (prefixWord ++ tailWord_5413566) baseStart_5413566 baseEnd_5413566 := by
    simpa [prefixWord, tailWord_5413566, baseEnd_5413566] using wordTrace_append hprefix tailTrace_5413566
  have hstable : (prefixWord ++ tailWord_5413566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413566).length < 2 ^ (prefixWord ++ tailWord_5413566).sum := by decide
  have hdescent : baseEnd_5413566 < baseStart_5413566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413581 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5413581 : Nat := 118140960795 + 5413581 * 2 ^ 59
def prefixEnd_5413581 : Nat := 4983230072969 + 3 ^ 40 * 5413581 * 2
def baseEnd_5413581 : Nat := 2779769115047689073140901

theorem tailTrace_5413581 : CollatzResearch.WordTrace tailWord_5413581 prefixEnd_5413581 2779769115047689073140901 := by
  unfold tailWord_5413581
  simp only [CollatzResearch.WordTrace]
  refine ⟨197449520200528077871448597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131633013467018718580965731 197449520200528077871448597)
  ·
    refine ⟨9255446259399753650224153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197449520200528077871448597 9255446259399753650224153)
    ·
      refine ⟨6941584694549815237668115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9255446259399753650224153 6941584694549815237668115)
      ·
        refine ⟨10412377041824722856502173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6941584694549815237668115 10412377041824722856502173)
        ·
          refine ⟨3904641390684271071188315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10412377041824722856502173 3904641390684271071188315)
          ·
            refine ⟨5856962086026406606782473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904641390684271071188315 5856962086026406606782473)
            ·
              refine ⟨4392721564519804955086855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5856962086026406606782473 4392721564519804955086855)
              ·
                refine ⟨6589082346779707432630283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392721564519804955086855 6589082346779707432630283)
                ·
                  refine ⟨9883623520169561148945425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6589082346779707432630283 9883623520169561148945425)
                  ·
                    refine ⟨7412717640127170861709069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9883623520169561148945425 7412717640127170861709069)
                    ·
                      refine ⟨2779769115047689073140901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7412717640127170861709069 2779769115047689073140901)
                      ·
                        rfl

theorem cell23_5413581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5413581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413581 prefixEnd_5413581 := by exact prefixLift 5413581
  have htrace : WordTrace (prefixWord ++ tailWord_5413581) baseStart_5413581 baseEnd_5413581 := by
    simpa [prefixWord, tailWord_5413581, baseEnd_5413581] using wordTrace_append hprefix tailTrace_5413581
  have hstable : (prefixWord ++ tailWord_5413581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413581).length < 2 ^ (prefixWord ++ tailWord_5413581).sum := by decide
  have hdescent : baseEnd_5413581 < baseStart_5413581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413616 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_5413616 : Nat := 118140960795 + 5413616 * 2 ^ 59
def prefixEnd_5413616 : Nat := 4983230072969 + 3 ^ 40 * 5413616 * 2
def baseEnd_5413616 : Nat := 2779787086870596436203239

theorem tailTrace_5413616 : CollatzResearch.WordTrace tailWord_5413616 prefixEnd_5413616 2779787086870596436203239 := by
  unfold tailWord_5413616
  simp only [CollatzResearch.WordTrace]
  refine ⟨98725398377700639424486351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131633864503600852565981801 98725398377700639424486351)
  ·
    refine ⟨148088097566550959136729527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98725398377700639424486351 148088097566550959136729527)
    ·
      refine ⟨222132146349826438705094291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148088097566550959136729527 222132146349826438705094291)
      ·
        refine ⟨333198219524739658057641437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222132146349826438705094291 333198219524739658057641437)
        ·
          refine ⟨124949332321777371771615539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333198219524739658057641437 124949332321777371771615539)
          ·
            refine ⟨187423998482666057657423309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124949332321777371771615539 187423998482666057657423309)
            ·
              refine ⟨70283999430999771621533741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187423998482666057657423309 70283999430999771621533741)
              ·
                refine ⟨26356499786624914358075153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70283999430999771621533741 26356499786624914358075153)
                ·
                  refine ⟨19767374839968685768556365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26356499786624914358075153 19767374839968685768556365)
                  ·
                    refine ⟨7412765564988257163208637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19767374839968685768556365 7412765564988257163208637)
                    ·
                      refine ⟨2779787086870596436203239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7412765564988257163208637 2779787086870596436203239)
                      ·
                        rfl

theorem cell23_5413616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_5413616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413616 prefixEnd_5413616 := by exact prefixLift 5413616
  have htrace : WordTrace (prefixWord ++ tailWord_5413616) baseStart_5413616 baseEnd_5413616 := by
    simpa [prefixWord, tailWord_5413616, baseEnd_5413616] using wordTrace_append hprefix tailTrace_5413616
  have hstable : (prefixWord ++ tailWord_5413616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413616).length < 2 ^ (prefixWord ++ tailWord_5413616).sum := by decide
  have hdescent : baseEnd_5413616 < baseStart_5413616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413617 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 2, 2, 2]
def baseStart_5413617 : Nat := 118140960795 + 5413617 * 2 ^ 59
def prefixEnd_5413617 : Nat := 4983230072969 + 3 ^ 40 * 5413617 * 2
def baseEnd_5413617 : Nat := 2779787600351250932290735

theorem tailTrace_5413617 : CollatzResearch.WordTrace tailWord_5413617 prefixEnd_5413617 2779787600351250932290735 := by
  unfold tailWord_5413617
  simp only [CollatzResearch.WordTrace]
  refine ⟨197450833228397656019759105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131633888818931770679839403 197450833228397656019759105)
  ·
    refine ⟨148088124921298242014819329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197450833228397656019759105 148088124921298242014819329)
    ·
      refine ⟨111066093690973681511114497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148088124921298242014819329 111066093690973681511114497)
      ·
        refine ⟨83299570268230261133335873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111066093690973681511114497 83299570268230261133335873)
        ·
          refine ⟨62474677701172695850001905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83299570268230261133335873 62474677701172695850001905)
          ·
            refine ⟨46856008275879521887501429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62474677701172695850001905 46856008275879521887501429)
            ·
              refine ⟨4392750775863705176953259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46856008275879521887501429 4392750775863705176953259)
              ·
                refine ⟨6589126163795557765429889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392750775863705176953259 6589126163795557765429889)
                ·
                  refine ⟨4941844622846668324072417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6589126163795557765429889 4941844622846668324072417)
                  ·
                    refine ⟨3706383467135001243054313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4941844622846668324072417 3706383467135001243054313)
                    ·
                      refine ⟨2779787600351250932290735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706383467135001243054313 2779787600351250932290735)
                      ·
                        rfl

theorem cell23_5413617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_5413617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413617 prefixEnd_5413617 := by exact prefixLift 5413617
  have htrace : WordTrace (prefixWord ++ tailWord_5413617) baseStart_5413617 baseEnd_5413617 := by
    simpa [prefixWord, tailWord_5413617, baseEnd_5413617] using wordTrace_append hprefix tailTrace_5413617
  have hstable : (prefixWord ++ tailWord_5413617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413617).length < 2 ^ (prefixWord ++ tailWord_5413617).sum := by decide
  have hdescent : baseEnd_5413617 < baseStart_5413617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413621 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5413621 : Nat := 118140960795 + 5413621 * 2 ^ 59
def prefixEnd_5413621 : Nat := 4983230072969 + 3 ^ 40 * 5413621 * 2
def baseEnd_5413621 : Nat := 2779789654273868916640717

theorem tailTrace_5413621 : CollatzResearch.WordTrace tailWord_5413621 prefixEnd_5413621 2779789654273868916640717 := by
  unfold tailWord_5413621
  simp only [CollatzResearch.WordTrace]
  refine ⟨197450979120383164702904717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131633986080255443135269811 197450979120383164702904717)
  ·
    refine ⟨74044117170143686763589269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197450979120383164702904717 74044117170143686763589269)
    ·
      refine ⟨3470817992350485317043247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74044117170143686763589269 3470817992350485317043247)
      ·
        refine ⟨5206226988525727975564871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3470817992350485317043247 5206226988525727975564871)
        ·
          refine ⟨7809340482788591963347307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5206226988525727975564871 7809340482788591963347307)
          ·
            refine ⟨11714010724182887945020961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7809340482788591963347307 11714010724182887945020961)
            ·
              refine ⟨8785508043137165958765721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11714010724182887945020961 8785508043137165958765721)
              ·
                refine ⟨6589131032352874469074291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8785508043137165958765721 6589131032352874469074291)
                ·
                  refine ⟨9883696548529311703611437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6589131032352874469074291 9883696548529311703611437)
                  ·
                    refine ⟨3706386205698491888854289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9883696548529311703611437 3706386205698491888854289)
                    ·
                      refine ⟨2779789654273868916640717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706386205698491888854289 2779789654273868916640717)
                      ·
                        rfl

theorem cell23_5413621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5413621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413621 prefixEnd_5413621 := by exact prefixLift 5413621
  have htrace : WordTrace (prefixWord ++ tailWord_5413621) baseStart_5413621 baseEnd_5413621 := by
    simpa [prefixWord, tailWord_5413621, baseEnd_5413621] using wordTrace_append hprefix tailTrace_5413621
  have hstable : (prefixWord ++ tailWord_5413621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413621).length < 2 ^ (prefixWord ++ tailWord_5413621).sum := by decide
  have hdescent : baseEnd_5413621 < baseStart_5413621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413636 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_5413636 : Nat := 118140960795 + 5413636 * 2 ^ 59
def prefixEnd_5413636 : Nat := 4983230072969 + 3 ^ 40 * 5413636 * 2
def baseEnd_5413636 : Nat := 926599118827895452651049

theorem tailTrace_5413636 : CollatzResearch.WordTrace tailWord_5413636 prefixEnd_5413636 926599118827895452651049 := by
  unfold tailWord_5413636
  simp only [CollatzResearch.WordTrace]
  refine ⟨98725763107664411132350381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131634350810219214843133841 98725763107664411132350381)
  ·
    refine ⟨37022161165374154174631393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98725763107664411132350381 37022161165374154174631393)
    ·
      refine ⟨27766620874030615630973545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37022161165374154174631393 27766620874030615630973545)
      ·
        refine ⟨20824965655522961723230159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27766620874030615630973545 20824965655522961723230159)
        ·
          refine ⟨31237448483284442584845239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20824965655522961723230159 31237448483284442584845239)
          ·
            refine ⟨46856172724926663877267859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31237448483284442584845239 46856172724926663877267859)
            ·
              refine ⟨70284259087389995815901789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46856172724926663877267859 70284259087389995815901789)
              ·
                refine ⟨26356597157771248430963171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70284259087389995815901789 26356597157771248430963171)
                ·
                  refine ⟨39534895736656872646444757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26356597157771248430963171 39534895736656872646444757)
                  ·
                    refine ⟨926599118827895452651049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39534895736656872646444757 926599118827895452651049)
                    ·
                      rfl

theorem cell23_5413636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_5413636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413636 prefixEnd_5413636 := by exact prefixLift 5413636
  have htrace : WordTrace (prefixWord ++ tailWord_5413636) baseStart_5413636 baseEnd_5413636 := by
    simpa [prefixWord, tailWord_5413636, baseEnd_5413636] using wordTrace_append hprefix tailTrace_5413636
  have hstable : (prefixWord ++ tailWord_5413636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413636).length < 2 ^ (prefixWord ++ tailWord_5413636).sum := by decide
  have hdescent : baseEnd_5413636 < baseStart_5413636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413640 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 5]
def baseStart_5413640 : Nat := 118140960795 + 5413640 * 2 ^ 59
def prefixEnd_5413640 : Nat := 4983230072969 + 3 ^ 40 * 5413640 * 2
def baseEnd_5413640 : Nat := 308866601156256038033681

theorem tailTrace_5413640 : CollatzResearch.WordTrace tailWord_5413640 prefixEnd_5413640 308866601156256038033681 := by
  unfold tailWord_5413640
  simp only [CollatzResearch.WordTrace]
  refine ⟨98725836053657165473923187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131634448071542887298564249 98725836053657165473923187)
  ·
    refine ⟨148088754080485748210884781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98725836053657165473923187 148088754080485748210884781)
    ·
      refine ⟨55533282780182155579081793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148088754080485748210884781 55533282780182155579081793)
      ·
        refine ⟨41649962085136616684311345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55533282780182155579081793 41649962085136616684311345)
        ·
          refine ⟨31237471563852462513233509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41649962085136616684311345 31237471563852462513233509)
          ·
            refine ⟨5857025918222336721231283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31237471563852462513233509 5857025918222336721231283)
            ·
              refine ⟨8785538877333505081846925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5857025918222336721231283 8785538877333505081846925)
              ·
                refine ⟨3294577079000064405692597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8785538877333505081846925 3294577079000064405692597)
                ·
                  refine ⟨308866601156256038033681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3294577079000064405692597 308866601156256038033681)
                  ·
                    rfl

theorem cell23_5413640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 5].length) (baseStart_5413640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413640 prefixEnd_5413640 := by exact prefixLift 5413640
  have htrace : WordTrace (prefixWord ++ tailWord_5413640) baseStart_5413640 baseEnd_5413640 := by
    simpa [prefixWord, tailWord_5413640, baseEnd_5413640] using wordTrace_append hprefix tailTrace_5413640
  have hstable : (prefixWord ++ tailWord_5413640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413640).length < 2 ^ (prefixWord ++ tailWord_5413640).sum := by decide
  have hdescent : baseEnd_5413640 < baseStart_5413640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413646 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5413646 : Nat := 118140960795 + 5413646 * 2 ^ 59
def prefixEnd_5413646 : Nat := 4983230072969 + 3 ^ 40 * 5413646 * 2
def baseEnd_5413646 : Nat := 2779802491290231318828101

theorem tailTrace_5413646 : CollatzResearch.WordTrace tailWord_5413646 prefixEnd_5413646 2779802491290231318828101 := by
  unfold tailWord_5413646
  simp only [CollatzResearch.WordTrace]
  refine ⟨24681486368161574246570599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131634593963528395981709861 24681486368161574246570599)
  ·
    refine ⟨37022229552242361369855899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24681486368161574246570599 37022229552242361369855899)
    ·
      refine ⟨55533344328363542054783849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37022229552242361369855899 55533344328363542054783849)
      ·
        refine ⟨41650008246272656541087887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55533344328363542054783849 41650008246272656541087887)
        ·
          refine ⟨62475012369408984811631831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41650008246272656541087887 62475012369408984811631831)
          ·
            refine ⟨93712518554113477217447747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62475012369408984811631831 93712518554113477217447747)
            ·
              refine ⟨140568777831170215826171621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93712518554113477217447747 140568777831170215826171621)
              ·
                refine ⟨26356645843344415467407179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140568777831170215826171621 26356645843344415467407179)
                ·
                  refine ⟨39534968765016623201110769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26356645843344415467407179 39534968765016623201110769)
                  ·
                    refine ⟨29651226573762467400833077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39534968765016623201110769 29651226573762467400833077)
                    ·
                      refine ⟨2779802491290231318828101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29651226573762467400833077 2779802491290231318828101)
                      ·
                        rfl

theorem cell23_5413646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5413646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413646 prefixEnd_5413646 := by exact prefixLift 5413646
  have htrace : WordTrace (prefixWord ++ tailWord_5413646) baseStart_5413646 baseEnd_5413646 := by
    simpa [prefixWord, tailWord_5413646, baseEnd_5413646] using wordTrace_append hprefix tailTrace_5413646
  have hstable : (prefixWord ++ tailWord_5413646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413646).length < 2 ^ (prefixWord ++ tailWord_5413646).sum := by decide
  have hdescent : baseEnd_5413646 < baseStart_5413646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413690 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_5413690 : Nat := 118140960795 + 5413690 * 2 ^ 59
def prefixEnd_5413690 : Nat := 4983230072969 + 3 ^ 40 * 5413690 * 2
def baseEnd_5413690 : Nat := 2779825084439029146677899

theorem tailTrace_5413690 : CollatzResearch.WordTrace tailWord_5413690 prefixEnd_5413690 2779825084439029146677899 := by
  unfold tailWord_5413690
  simp only [CollatzResearch.WordTrace]
  refine ⟨49363373939283297371791631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131635663838088792991444349 49363373939283297371791631)
  ·
    refine ⟨74045060908924946057687447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49363373939283297371791631 74045060908924946057687447)
    ·
      refine ⟨111067591363387419086531171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74045060908924946057687447 111067591363387419086531171)
      ·
        refine ⟨166601387045081128629796757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111067591363387419086531171 166601387045081128629796757)
        ·
          refine ⟨7809440017738177904521723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166601387045081128629796757 7809440017738177904521723)
          ·
            refine ⟨11714160026607266856782585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7809440017738177904521723 11714160026607266856782585)
            ·
              refine ⟨8785620019955450142586939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11714160026607266856782585 8785620019955450142586939)
              ·
                refine ⟨13178430029933175213880409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8785620019955450142586939 13178430029933175213880409)
                ·
                  refine ⟨9883822522449881410410307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13178430029933175213880409 9883822522449881410410307)
                  ·
                    refine ⟨14825733783674822115615461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9883822522449881410410307 14825733783674822115615461)
                    ·
                      refine ⟨2779825084439029146677899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14825733783674822115615461 2779825084439029146677899)
                      ·
                        rfl

theorem cell23_5413690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_5413690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413690 prefixEnd_5413690 := by exact prefixLift 5413690
  have htrace : WordTrace (prefixWord ++ tailWord_5413690) baseStart_5413690 baseEnd_5413690 := by
    simpa [prefixWord, tailWord_5413690, baseEnd_5413690] using wordTrace_append hprefix tailTrace_5413690
  have hstable : (prefixWord ++ tailWord_5413690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413690).length < 2 ^ (prefixWord ++ tailWord_5413690).sum := by decide
  have hdescent : baseEnd_5413690 < baseStart_5413690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413740 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_5413740 : Nat := 118140960795 + 5413740 * 2 ^ 59
def prefixEnd_5413740 : Nat := 4983230072969 + 3 ^ 40 * 5413740 * 2
def baseEnd_5413740 : Nat := 2779850758471753951052669

theorem tailTrace_5413740 : CollatzResearch.WordTrace tailWord_5413740 prefixEnd_5413740 2779850758471753951052669 := by
  unfold tailWord_5413740
  simp only [CollatzResearch.WordTrace]
  refine ⟨98727659703476024013243337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131636879604634698684324449 98727659703476024013243337)
  ·
    refine ⟨74045744777607018009932503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98727659703476024013243337 74045744777607018009932503)
    ·
      refine ⟨111068617166410527014898755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74045744777607018009932503 111068617166410527014898755)
      ·
        refine ⟨166602925749615790522348133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111068617166410527014898755 166602925749615790522348133)
        ·
          refine ⟨31238048578052960722940275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166602925749615790522348133 31238048578052960722940275)
          ·
            refine ⟨46857072867079441084410413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31238048578052960722940275 46857072867079441084410413)
            ·
              refine ⟨17571402325154790406653905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46857072867079441084410413 17571402325154790406653905)
              ·
                refine ⟨13178551743866092804990429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17571402325154790406653905 13178551743866092804990429)
                ·
                  refine ⟨4941956903949784801871411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13178551743866092804990429 4941956903949784801871411)
                  ·
                    refine ⟨7412935355924677202807117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4941956903949784801871411 7412935355924677202807117)
                    ·
                      refine ⟨2779850758471753951052669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7412935355924677202807117 2779850758471753951052669)
                      ·
                        rfl

theorem cell23_5413740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_5413740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413740 prefixEnd_5413740 := by exact prefixLift 5413740
  have htrace : WordTrace (prefixWord ++ tailWord_5413740) baseStart_5413740 baseEnd_5413740 := by
    simpa [prefixWord, tailWord_5413740, baseEnd_5413740] using wordTrace_append hprefix tailTrace_5413740
  have hstable : (prefixWord ++ tailWord_5413740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413740).length < 2 ^ (prefixWord ++ tailWord_5413740).sum := by decide
  have hdescent : baseEnd_5413740 < baseStart_5413740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413757 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_5413757 : Nat := 118140960795 + 5413757 * 2 ^ 59
def prefixEnd_5413757 : Nat := 4983230072969 + 3 ^ 40 * 5413757 * 2
def baseEnd_5413757 : Nat := 2779859487642880384540091

theorem tailTrace_5413757 : CollatzResearch.WordTrace tailWord_5413757 prefixEnd_5413757 2779859487642880384540091 := by
  unfold tailWord_5413757
  simp only [CollatzResearch.WordTrace]
  refine ⟨197455939447890459929855525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131637292965260306619903683 197455939447890459929855525)
  ·
    refine ⟨37022988646479461236847911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197455939447890459929855525 37022988646479461236847911)
    ·
      refine ⟨55534482969719191855271867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37022988646479461236847911 55534482969719191855271867)
      ·
        refine ⟨83301724454578787782907801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55534482969719191855271867 83301724454578787782907801)
        ·
          refine ⟨62476293340934090837180851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83301724454578787782907801 62476293340934090837180851)
          ·
            refine ⟨93714440011401136255771277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62476293340934090837180851 93714440011401136255771277)
            ·
              refine ⟨35142915004275426095914229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93714440011401136255771277 35142915004275426095914229)
              ·
                refine ⟨3294648281650821196491959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35142915004275426095914229 3294648281650821196491959)
                ·
                  refine ⟨4941972422476231794737939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294648281650821196491959 4941972422476231794737939)
                  ·
                    refine ⟨7412958633714347692106909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4941972422476231794737939 7412958633714347692106909)
                    ·
                      refine ⟨2779859487642880384540091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7412958633714347692106909 2779859487642880384540091)
                      ·
                        rfl

theorem cell23_5413757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_5413757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413757 prefixEnd_5413757 := by exact prefixLift 5413757
  have htrace : WordTrace (prefixWord ++ tailWord_5413757) baseStart_5413757 baseEnd_5413757 := by
    simpa [prefixWord, tailWord_5413757, baseEnd_5413757] using wordTrace_append hprefix tailTrace_5413757
  have hstable : (prefixWord ++ tailWord_5413757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413757).length < 2 ^ (prefixWord ++ tailWord_5413757).sum := by decide
  have hdescent : baseEnd_5413757 < baseStart_5413757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413783 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5413783 : Nat := 118140960795 + 5413783 * 2 ^ 59
def prefixEnd_5413783 : Nat := 4983230072969 + 3 ^ 40 * 5413783 * 2
def baseEnd_5413783 : Nat := 2779872838139897282814971

theorem tailTrace_5413783 : CollatzResearch.WordTrace tailWord_5413783 prefixEnd_5413783 2779872838139897282814971 := by
  unfold tailWord_5413783
  simp only [CollatzResearch.WordTrace]
  refine ⟨197456887745796266370302003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131637925163864177580201335 197456887745796266370302003)
  ·
    refine ⟨296185331618694399555453005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197456887745796266370302003 296185331618694399555453005)
    ·
      refine ⟨111069499357010399833294877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296185331618694399555453005 111069499357010399833294877)
      ·
        refine ⟨41651062258878899937485579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111069499357010399833294877 41651062258878899937485579)
        ·
          refine ⟨62476593388318349906228369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41651062258878899937485579 62476593388318349906228369)
          ·
            refine ⟨46857445041238762429671277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62476593388318349906228369 46857445041238762429671277)
            ·
              refine ⟨17571541890464535911126729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46857445041238762429671277 17571541890464535911126729)
              ·
                refine ⟨13178656417848401933345047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17571541890464535911126729 13178656417848401933345047)
                ·
                  refine ⟨19767984626772602900017571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13178656417848401933345047 19767984626772602900017571)
                  ·
                    refine ⟨29651976940158904350026357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19767984626772602900017571 29651976940158904350026357)
                    ·
                      refine ⟨2779872838139897282814971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29651976940158904350026357 2779872838139897282814971)
                      ·
                        rfl

theorem cell23_5413783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5413783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413783 prefixEnd_5413783 := by exact prefixLift 5413783
  have htrace : WordTrace (prefixWord ++ tailWord_5413783) baseStart_5413783 baseEnd_5413783 := by
    simpa [prefixWord, tailWord_5413783, baseEnd_5413783] using wordTrace_append hprefix tailTrace_5413783
  have hstable : (prefixWord ++ tailWord_5413783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413783).length < 2 ^ (prefixWord ++ tailWord_5413783).sum := by decide
  have hdescent : baseEnd_5413783 < baseStart_5413783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413840 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 3, 3, 2]
def baseStart_5413840 : Nat := 118140960795 + 5413840 * 2 ^ 59
def prefixEnd_5413840 : Nat := 4983230072969 + 3 ^ 40 * 5413840 * 2
def baseEnd_5413840 : Nat := 2779902106537203559802209

theorem tailTrace_5413840 : CollatzResearch.WordTrace tailWord_5413840 prefixEnd_5413840 2779902106537203559802209 := by
  unfold tailWord_5413840
  simp only [CollatzResearch.WordTrace]
  refine ⟨98729483353294882552563487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131639311137726510070084649 98729483353294882552563487)
  ·
    refine ⟨148094225029942323828845231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98729483353294882552563487 148094225029942323828845231)
    ·
      refine ⟨222141337544913485743267847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148094225029942323828845231 222141337544913485743267847)
      ·
        refine ⟨333212006317370228614901771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222141337544913485743267847 333212006317370228614901771)
        ·
          refine ⟨499818009476055342922352657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333212006317370228614901771 499818009476055342922352657)
          ·
            refine ⟨374863507107041507191764493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499818009476055342922352657 374863507107041507191764493)
            ·
              refine ⟨140573815165140565196911685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374863507107041507191764493 140573815165140565196911685)
              ·
                refine ⟨26357590343463855974420941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140573815165140565196911685 26357590343463855974420941)
                ·
                  refine ⟨9884096378798945990407853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26357590343463855974420941 9884096378798945990407853)
                  ·
                    refine ⟨3706536142049604746402945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9884096378798945990407853 3706536142049604746402945)
                    ·
                      refine ⟨2779902106537203559802209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706536142049604746402945 2779902106537203559802209)
                      ·
                        rfl

theorem cell23_5413840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 3, 2].length) (baseStart_5413840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413840 prefixEnd_5413840 := by exact prefixLift 5413840
  have htrace : WordTrace (prefixWord ++ tailWord_5413840) baseStart_5413840 baseEnd_5413840 := by
    simpa [prefixWord, tailWord_5413840, baseEnd_5413840] using wordTrace_append hprefix tailTrace_5413840
  have hstable : (prefixWord ++ tailWord_5413840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413840).length < 2 ^ (prefixWord ++ tailWord_5413840).sum := by decide
  have hdescent : baseEnd_5413840 < baseStart_5413840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413883 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4]
def baseStart_5413883 : Nat := 118140960795 + 5413883 * 2 ^ 59
def prefixEnd_5413883 : Nat := 4983230072969 + 3 ^ 40 * 5413883 * 2
def baseEnd_5413883 : Nat := 2779924186205346891564511

theorem tailTrace_5413883 : CollatzResearch.WordTrace tailWord_5413883 prefixEnd_5413883 2779924186205346891564511 := by
  unfold tailWord_5413883
  simp only [CollatzResearch.WordTrace]
  refine ⟨197460535045433983448942303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131640356696955988965961535 197460535045433983448942303)
  ·
    refine ⟨296190802568150975173413455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197460535045433983448942303 296190802568150975173413455)
    ·
      refine ⟨444286203852226462760120183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296190802568150975173413455 444286203852226462760120183)
      ·
        refine ⟨666429305778339694140180275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444286203852226462760120183 666429305778339694140180275)
        ·
          refine ⟨999643958667509541210270413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666429305778339694140180275 999643958667509541210270413)
          ·
            refine ⟨374866484500316077953851405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 999643958667509541210270413 374866484500316077953851405)
            ·
              refine ⟨140574931687618529232694277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374866484500316077953851405 140574931687618529232694277)
              ·
                refine ⟨26357799691428474231130177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140574931687618529232694277 26357799691428474231130177)
                ·
                  refine ⟨19768349768571355673347633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26357799691428474231130177 19768349768571355673347633)
                  ·
                    refine ⟨14826262326428516755010725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19768349768571355673347633 14826262326428516755010725)
                    ·
                      refine ⟨2779924186205346891564511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14826262326428516755010725 2779924186205346891564511)
                      ·
                        rfl

theorem cell23_5413883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_5413883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413883 prefixEnd_5413883 := by exact prefixLift 5413883
  have htrace : WordTrace (prefixWord ++ tailWord_5413883) baseStart_5413883 baseEnd_5413883 := by
    simpa [prefixWord, tailWord_5413883, baseEnd_5413883] using wordTrace_append hprefix tailTrace_5413883
  have hstable : (prefixWord ++ tailWord_5413883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413883).length < 2 ^ (prefixWord ++ tailWord_5413883).sum := by decide
  have hdescent : baseEnd_5413883 < baseStart_5413883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413893 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 7]
def baseStart_5413893 : Nat := 118140960795 + 5413893 * 2 ^ 59
def prefixEnd_5413893 : Nat := 4983230072969 + 3 ^ 40 * 5413893 * 2
def baseEnd_5413893 : Nat := 308881035667987983604385

theorem tailTrace_5413893 : CollatzResearch.WordTrace tailWord_5413893 prefixEnd_5413893 308881035667987983604385 := by
  unfold tailWord_5413893
  simp only [CollatzResearch.WordTrace]
  refine ⟨197460899775397755156806333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131640599850265170104537555 197460899775397755156806333)
  ·
    refine ⟨74047837415774158183802375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197460899775397755156806333 74047837415774158183802375)
    ·
      refine ⟨111071756123661237275703563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74047837415774158183802375 111071756123661237275703563)
      ·
        refine ⟨166607634185491855913555345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111071756123661237275703563 166607634185491855913555345)
        ·
          refine ⟨124955725639118891935166509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166607634185491855913555345 124955725639118891935166509)
          ·
            refine ⟨46858397114669584475687441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124955725639118891935166509 46858397114669584475687441)
            ·
              refine ⟨35143797836002188356765581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46858397114669584475687441 35143797836002188356765581)
              ·
                refine ⟨13178924188500820633787093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35143797836002188356765581 13178924188500820633787093)
                ·
                  refine ⟨308881035667987983604385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13178924188500820633787093 308881035667987983604385)
                  ·
                    rfl

theorem cell23_5413893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_5413893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413893 prefixEnd_5413893 := by exact prefixLift 5413893
  have htrace : WordTrace (prefixWord ++ tailWord_5413893) baseStart_5413893 baseEnd_5413893 := by
    simpa [prefixWord, tailWord_5413893, baseEnd_5413893] using wordTrace_append hprefix tailTrace_5413893
  have hstable : (prefixWord ++ tailWord_5413893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413893).length < 2 ^ (prefixWord ++ tailWord_5413893).sum := by decide
  have hdescent : baseEnd_5413893 < baseStart_5413893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413900 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_5413900 : Nat := 118140960795 + 5413900 * 2 ^ 59
def prefixEnd_5413900 : Nat := 4983230072969 + 3 ^ 40 * 5413900 * 2
def baseEnd_5413900 : Nat := 2779932915376473325051933

theorem tailTrace_5413900 : CollatzResearch.WordTrace tailWord_5413900 prefixEnd_5413900 2779932915376473325051933 := by
  unfold tailWord_5413900
  simp only [CollatzResearch.WordTrace]
  refine ⟨98730577543186197676155577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131640770057581596901540769 98730577543186197676155577)
  ·
    refine ⟨74047933157389648257116683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98730577543186197676155577 74047933157389648257116683)
    ·
      refine ⟨111071899736084472385675025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74047933157389648257116683 111071899736084472385675025)
      ·
        refine ⟨83303924802063354289256269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111071899736084472385675025 83303924802063354289256269)
        ·
          refine ⟨31238971800773757858471101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83303924802063354289256269 31238971800773757858471101)
          ·
            refine ⟨11714614425290159196926663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31238971800773757858471101 11714614425290159196926663)
            ·
              refine ⟨17571921637935238795389995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11714614425290159196926663 17571921637935238795389995)
              ·
                refine ⟨26357882456902858193084993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17571921637935238795389995 26357882456902858193084993)
                ·
                  refine ⟨19768411842677143644813745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26357882456902858193084993 19768411842677143644813745)
                  ·
                    refine ⟨14826308882007857733610309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19768411842677143644813745 14826308882007857733610309)
                    ·
                      refine ⟨2779932915376473325051933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14826308882007857733610309 2779932915376473325051933)
                      ·
                        rfl

theorem cell23_5413900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_5413900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413900 prefixEnd_5413900 := by exact prefixLift 5413900
  have htrace : WordTrace (prefixWord ++ tailWord_5413900) baseStart_5413900 baseEnd_5413900 := by
    simpa [prefixWord, tailWord_5413900, baseEnd_5413900] using wordTrace_append hprefix tailTrace_5413900
  have hstable : (prefixWord ++ tailWord_5413900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413900).length < 2 ^ (prefixWord ++ tailWord_5413900).sum := by decide
  have hdescent : baseEnd_5413900 < baseStart_5413900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413983 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 10]
def baseStart_5413983 : Nat := 118140960795 + 5413983 * 2 ^ 59
def prefixEnd_5413983 : Nat := 4983230072969 + 3 ^ 40 * 5413983 * 2
def baseEnd_5413983 : Nat := 308886170474532944479339

theorem tailTrace_5413983 : CollatzResearch.WordTrace tailWord_5413983 prefixEnd_5413983 308886170474532944479339 := by
  unfold tailWord_5413983
  simp only [CollatzResearch.WordTrace]
  refine ⟨197464182345071700527582603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131642788230047800351721735 197464182345071700527582603)
  ·
    refine ⟨296196273517607550791373905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197464182345071700527582603 296196273517607550791373905)
    ·
      refine ⟨222147205138205663093530429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296196273517607550791373905 222147205138205663093530429)
      ·
        refine ⟨83305201926827123660073911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222147205138205663093530429 83305201926827123660073911)
        ·
          refine ⟨124957802890240685490110867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83305201926827123660073911 124957802890240685490110867)
          ·
            refine ⟨187436704335361028235166301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124957802890240685490110867 187436704335361028235166301)
            ·
              refine ⟨70288764125760385588187363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187436704335361028235166301 70288764125760385588187363)
              ·
                refine ⟨105433146188640578382281045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70288764125760385588187363 105433146188640578382281045)
                ·
                  refine ⟨308886170474532944479339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105433146188640578382281045 308886170474532944479339)
                  ·
                    rfl

theorem cell23_5413983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 10].length) (baseStart_5413983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413983 prefixEnd_5413983 := by exact prefixLift 5413983
  have htrace : WordTrace (prefixWord ++ tailWord_5413983) baseStart_5413983 baseEnd_5413983 := by
    simpa [prefixWord, tailWord_5413983, baseEnd_5413983] using wordTrace_append hprefix tailTrace_5413983
  have hstable : (prefixWord ++ tailWord_5413983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413983).length < 2 ^ (prefixWord ++ tailWord_5413983).sum := by decide
  have hdescent : baseEnd_5413983 < baseStart_5413983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5413997 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_5413997 : Nat := 118140960795 + 5413997 * 2 ^ 59
def prefixEnd_5413997 : Nat := 4983230072969 + 3 ^ 40 * 5413997 * 2
def baseEnd_5413997 : Nat := 2779982722999959445538987

theorem tailTrace_5413997 : CollatzResearch.WordTrace tailWord_5413997 prefixEnd_5413997 2779982722999959445538987 := by
  unfold tailWord_5413997
  simp only [CollatzResearch.WordTrace]
  refine ⟨197464692967020980918592245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131643128644680653945728163 197464692967020980918592245)
  ·
    refine ⟨18512314965658216961118023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197464692967020980918592245 18512314965658216961118023)
    ·
      refine ⟨27768472448487325441677035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18512314965658216961118023 27768472448487325441677035)
      ·
        refine ⟨41652708672730988162515553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27768472448487325441677035 41652708672730988162515553)
        ·
          refine ⟨31239531504548241121886665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41652708672730988162515553 31239531504548241121886665)
          ·
            refine ⟨23429648628411180841414999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31239531504548241121886665 23429648628411180841414999)
            ·
              refine ⟨35144472942616771262122499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23429648628411180841414999 35144472942616771262122499)
              ·
                refine ⟨52716709413925156893183749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35144472942616771262122499 52716709413925156893183749)
                ·
                  refine ⟨9884383015110966917471953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52716709413925156893183749 9884383015110966917471953)
                  ·
                    refine ⟨7413287261333225188103965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9884383015110966917471953 7413287261333225188103965)
                    ·
                      refine ⟨2779982722999959445538987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7413287261333225188103965 2779982722999959445538987)
                      ·
                        rfl

theorem cell23_5413997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_5413997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5413997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5413997 prefixEnd_5413997 := by exact prefixLift 5413997
  have htrace : WordTrace (prefixWord ++ tailWord_5413997) baseStart_5413997 baseEnd_5413997 := by
    simpa [prefixWord, tailWord_5413997, baseEnd_5413997] using wordTrace_append hprefix tailTrace_5413997
  have hstable : (prefixWord ++ tailWord_5413997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5413997).length < 2 ^ (prefixWord ++ tailWord_5413997).sum := by decide
  have hdescent : baseEnd_5413997 < baseStart_5413997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5413997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414000 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 6]
def baseStart_5414000 : Nat := 118140960795 + 5414000 * 2 ^ 59
def prefixEnd_5414000 : Nat := 4983230072969 + 3 ^ 40 * 5414000 * 2
def baseEnd_5414000 : Nat := 308887140382435881533497

theorem tailTrace_5414000 : CollatzResearch.WordTrace tailWord_5414000 prefixEnd_5414000 308887140382435881533497 := by
  unfold tailWord_5414000
  simp only [CollatzResearch.WordTrace]
  refine ⟨98732401193005056215475727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131643201590673408287300969 98732401193005056215475727)
  ·
    refine ⟨148098601789507584323213591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98732401193005056215475727 148098601789507584323213591)
    ·
      refine ⟨222147902684261376484820387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148098601789507584323213591 222147902684261376484820387)
      ·
        refine ⟨333221854026392064727230581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222147902684261376484820387 333221854026392064727230581)
        ·
          refine ⟨31239548814974256068177867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 333221854026392064727230581 31239548814974256068177867)
          ·
            refine ⟨46859323222461384102266801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31239548814974256068177867 46859323222461384102266801)
            ·
              refine ⟨35144492416846038076700101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46859323222461384102266801 35144492416846038076700101)
              ·
                refine ⟨6589592328158632139381269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35144492416846038076700101 6589592328158632139381269)
                ·
                  refine ⟨308887140382435881533497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6589592328158632139381269 308887140382435881533497)
                  ·
                    rfl

theorem cell23_5414000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_5414000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414000 prefixEnd_5414000 := by exact prefixLift 5414000
  have htrace : WordTrace (prefixWord ++ tailWord_5414000) baseStart_5414000 baseEnd_5414000 := by
    simpa [prefixWord, tailWord_5414000, baseEnd_5414000] using wordTrace_append hprefix tailTrace_5414000
  have hstable : (prefixWord ++ tailWord_5414000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414000).length < 2 ^ (prefixWord ++ tailWord_5414000).sum := by decide
  have hdescent : baseEnd_5414000 < baseStart_5414000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414017 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 6]
def baseStart_5414017 : Nat := 118140960795 + 5414017 * 2 ^ 59
def prefixEnd_5414017 : Nat := 4983230072969 + 3 ^ 40 * 5414017 * 2
def baseEnd_5414017 : Nat := 308888110290338818587655

theorem tailTrace_5414017 : CollatzResearch.WordTrace tailWord_5414017 prefixEnd_5414017 308888110290338818587655 := by
  unfold tailWord_5414017
  simp only [CollatzResearch.WordTrace]
  refine ⟨197465422426948524334320305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131643614951299016222880203 197465422426948524334320305)
  ·
    refine ⟨148099066820211393250740229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197465422426948524334320305 148099066820211393250740229)
    ·
      refine ⟨27768575028789636234513793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148099066820211393250740229 27768575028789636234513793)
      ·
        refine ⟨20826431271592227175885345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27768575028789636234513793 20826431271592227175885345)
        ·
          refine ⟨15619823453694170381914009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20826431271592227175885345 15619823453694170381914009)
          ·
            refine ⟨11714867590270627786435507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15619823453694170381914009 11714867590270627786435507)
            ·
              refine ⟨17572301385405941679653261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11714867590270627786435507 17572301385405941679653261)
              ·
                refine ⟨6589613019527228129869973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17572301385405941679653261 6589613019527228129869973)
                ·
                  refine ⟨308888110290338818587655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6589613019527228129869973 308888110290338818587655)
                  ·
                    rfl

theorem cell23_5414017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 6].length) (baseStart_5414017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414017 prefixEnd_5414017 := by exact prefixLift 5414017
  have htrace : WordTrace (prefixWord ++ tailWord_5414017) baseStart_5414017 baseEnd_5414017 := by
    simpa [prefixWord, tailWord_5414017, baseEnd_5414017] using wordTrace_append hprefix tailTrace_5414017
  have hstable : (prefixWord ++ tailWord_5414017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414017).length < 2 ^ (prefixWord ++ tailWord_5414017).sum := by decide
  have hdescent : baseEnd_5414017 < baseStart_5414017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414027 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 3]
def baseStart_5414027 : Nat := 118140960795 + 5414027 * 2 ^ 59
def prefixEnd_5414027 : Nat := 4983230072969 + 3 ^ 40 * 5414027 * 2
def baseEnd_5414027 : Nat := 2779998127419594328163849

theorem tailTrace_5414027 : CollatzResearch.WordTrace tailWord_5414027 prefixEnd_5414027 2779998127419594328163849 := by
  unfold tailWord_5414027
  simp only [CollatzResearch.WordTrace]
  refine ⟨197465787156912296042184335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131643858104608197361456223 197465787156912296042184335)
  ·
    refine ⟨296198680735368444063276503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197465787156912296042184335 296198680735368444063276503)
    ·
      refine ⟨444298021103052666094914755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296198680735368444063276503 444298021103052666094914755)
      ·
        refine ⟨666447031654578999142372133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444298021103052666094914755 666447031654578999142372133)
        ·
          refine ⟨124958818435233562339194775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 666447031654578999142372133 124958818435233562339194775)
          ·
            refine ⟨187438227652850343508792163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124958818435233562339194775 187438227652850343508792163)
            ·
              refine ⟨281157341479275515263188245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187438227652850343508792163 281157341479275515263188245)
              ·
                refine ⟨13179250381841039777961949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281157341479275515263188245 13179250381841039777961949)
                ·
                  refine ⟨4942218893190389916735731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13179250381841039777961949 4942218893190389916735731)
                  ·
                    refine ⟨7413328339785584875103597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4942218893190389916735731 7413328339785584875103597)
                    ·
                      refine ⟨2779998127419594328163849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7413328339785584875103597 2779998127419594328163849)
                      ·
                        rfl

theorem cell23_5414027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 3].length) (baseStart_5414027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414027 prefixEnd_5414027 := by exact prefixLift 5414027
  have htrace : WordTrace (prefixWord ++ tailWord_5414027) baseStart_5414027 baseEnd_5414027 := by
    simpa [prefixWord, tailWord_5414027, baseEnd_5414027] using wordTrace_append hprefix tailTrace_5414027
  have hstable : (prefixWord ++ tailWord_5414027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414027).length < 2 ^ (prefixWord ++ tailWord_5414027).sum := by decide
  have hdescent : baseEnd_5414027 < baseStart_5414027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414101 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5414101 : Nat := 118140960795 + 5414101 * 2 ^ 59
def prefixEnd_5414101 : Nat := 4983230072969 + 3 ^ 40 * 5414101 * 2
def baseEnd_5414101 : Nat := 2780036124988027038638509

theorem tailTrace_5414101 : CollatzResearch.WordTrace tailWord_5414101 prefixEnd_5414101 2780036124988027038638509 := by
  unfold tailWord_5414101
  simp only [CollatzResearch.WordTrace]
  refine ⟨197468486158644206680378157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131645657439096137786918771 197468486158644206680378157)
  ·
    refine ⟨74050682309491577505141809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197468486158644206680378157 74050682309491577505141809)
    ·
      refine ⟨55538011732118683128856357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74050682309491577505141809 55538011732118683128856357)
      ·
        refine ⟨10413377199772253086660567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55538011732118683128856357 10413377199772253086660567)
        ·
          refine ⟨15620065799658379629990851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10413377199772253086660567 15620065799658379629990851)
          ·
            refine ⟨23430098699487569444986277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15620065799658379629990851 23430098699487569444986277)
            ·
              refine ⟨4393143506153919270934927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23430098699487569444986277 4393143506153919270934927)
              ·
                refine ⟨6589715259230878906402391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393143506153919270934927 6589715259230878906402391)
                ·
                  refine ⟨9884572888846318359603587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6589715259230878906402391 9884572888846318359603587)
                  ·
                    refine ⟨14826859333269477539405381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9884572888846318359603587 14826859333269477539405381)
                    ·
                      refine ⟨2780036124988027038638509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14826859333269477539405381 2780036124988027038638509)
                      ·
                        rfl

theorem cell23_5414101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5414101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414101 prefixEnd_5414101 := by exact prefixLift 5414101
  have htrace : WordTrace (prefixWord ++ tailWord_5414101) baseStart_5414101 baseEnd_5414101 := by
    simpa [prefixWord, tailWord_5414101, baseEnd_5414101] using wordTrace_append hprefix tailTrace_5414101
  have hstable : (prefixWord ++ tailWord_5414101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414101).length < 2 ^ (prefixWord ++ tailWord_5414101).sum := by decide
  have hdescent : baseEnd_5414101 < baseStart_5414101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414152 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_5414152 : Nat := 118140960795 + 5414152 * 2 ^ 59
def prefixEnd_5414152 : Nat := 4983230072969 + 3 ^ 40 * 5414152 * 2
def baseEnd_5414152 : Nat := 2780062312501406339100775

theorem tailTrace_5414152 : CollatzResearch.WordTrace tailWord_5414152 prefixEnd_5414152 2780062312501406339100775 := by
  unfold tailWord_5414152
  simp only [CollatzResearch.WordTrace]
  refine ⟨98735173140729721195242355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131646897520972961593656473 98735173140729721195242355)
  ·
    refine ⟨148102759711094581792863533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98735173140729721195242355 148102759711094581792863533)
    ·
      refine ⟨55538534891660468172323825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148102759711094581792863533 55538534891660468172323825)
      ·
        refine ⟨41653901168745351129242869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55538534891660468172323825 41653901168745351129242869)
        ·
          refine ⟨3905053234569876668366519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41653901168745351129242869 3905053234569876668366519)
          ·
            refine ⟨5857579851854815002549779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905053234569876668366519 5857579851854815002549779)
            ·
              refine ⟨8786369777782222503824669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5857579851854815002549779 8786369777782222503824669)
              ·
                refine ⟨3294888666668333438934251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8786369777782222503824669 3294888666668333438934251)
                ·
                  refine ⟨4942333000002500158401377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294888666668333438934251 4942333000002500158401377)
                  ·
                    refine ⟨3706749750001875118801033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4942333000002500158401377 3706749750001875118801033)
                    ·
                      refine ⟨2780062312501406339100775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706749750001875118801033 2780062312501406339100775)
                      ·
                        rfl

theorem cell23_5414152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_5414152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414152 prefixEnd_5414152 := by exact prefixLift 5414152
  have htrace : WordTrace (prefixWord ++ tailWord_5414152) baseStart_5414152 baseEnd_5414152 := by
    simpa [prefixWord, tailWord_5414152, baseEnd_5414152] using wordTrace_append hprefix tailTrace_5414152
  have hstable : (prefixWord ++ tailWord_5414152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414152).length < 2 ^ (prefixWord ++ tailWord_5414152).sum := by decide
  have hdescent : baseEnd_5414152 < baseStart_5414152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414177 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_5414177 : Nat := 118140960795 + 5414177 * 2 ^ 59
def prefixEnd_5414177 : Nat := 4983230072969 + 3 ^ 40 * 5414177 * 2
def baseEnd_5414177 : Nat := 2780075149517768741288159

theorem tailTrace_5414177 : CollatzResearch.WordTrace tailWord_5414177 prefixEnd_5414177 2780075149517768741288159 := by
  unfold tailWord_5414177
  simp only [CollatzResearch.WordTrace]
  refine ⟨197471258106368871660144785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131647505404245914440096523 197471258106368871660144785)
  ·
    refine ⟨148103443579776653745108589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197471258106368871660144785 148103443579776653745108589)
    ·
      refine ⟨55538791342416245154415721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148103443579776653745108589 55538791342416245154415721)
      ·
        refine ⟨41654093506812183865811791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55538791342416245154415721 41654093506812183865811791)
        ·
          refine ⟨62481140260218275798717687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41654093506812183865811791 62481140260218275798717687)
          ·
            refine ⟨93721710390327413698076531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62481140260218275798717687 93721710390327413698076531)
            ·
              refine ⟨140582565585491120547114797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93721710390327413698076531 140582565585491120547114797)
              ·
                refine ⟨52718462094559170205168049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140582565585491120547114797 52718462094559170205168049)
                ·
                  refine ⟨39538846570919377653876037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52718462094559170205168049 39538846570919377653876037)
                  ·
                    refine ⟨7413533732047383310101757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39538846570919377653876037 7413533732047383310101757)
                    ·
                      refine ⟨2780075149517768741288159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7413533732047383310101757 2780075149517768741288159)
                      ·
                        rfl

theorem cell23_5414177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_5414177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414177 prefixEnd_5414177 := by exact prefixLift 5414177
  have htrace : WordTrace (prefixWord ++ tailWord_5414177) baseStart_5414177 baseEnd_5414177 := by
    simpa [prefixWord, tailWord_5414177, baseEnd_5414177] using wordTrace_append hprefix tailTrace_5414177
  have hstable : (prefixWord ++ tailWord_5414177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414177).length < 2 ^ (prefixWord ++ tailWord_5414177).sum := by decide
  have hdescent : baseEnd_5414177 < baseStart_5414177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414227 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 2, 5]
def baseStart_5414227 : Nat := 118140960795 + 5414227 * 2 ^ 59
def prefixEnd_5414227 : Nat := 4983230072969 + 3 ^ 40 * 5414227 * 2
def baseEnd_5414227 : Nat := 926700274516831181887643

theorem tailTrace_5414227 : CollatzResearch.WordTrace tailWord_5414227 prefixEnd_5414227 926700274516831181887643 := by
  unfold tailWord_5414227
  simp only [CollatzResearch.WordTrace]
  refine ⟨197473081756187730199464935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131648721170791820132976623 197473081756187730199464935)
  ·
    refine ⟨296209622634281595299197403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197473081756187730199464935 296209622634281595299197403)
    ·
      refine ⟨444314433951422392948796105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296209622634281595299197403 444314433951422392948796105)
      ·
        refine ⟨333235825463566794711597079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444314433951422392948796105 333235825463566794711597079)
        ·
          refine ⟨499853738195350192067395619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333235825463566794711597079 499853738195350192067395619)
          ·
            refine ⟨749780607293025288101093429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499853738195350192067395619 749780607293025288101093429)
            ·
              refine ⟨70291931933721120759477509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 749780607293025288101093429 70291931933721120759477509)
              ·
                refine ⟨13179737237572710142402033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70291931933721120759477509 13179737237572710142402033)
                ·
                  refine ⟨9884802928179532606801525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13179737237572710142402033 9884802928179532606801525)
                  ·
                    refine ⟨926700274516831181887643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9884802928179532606801525 926700274516831181887643)
                    ·
                      rfl

theorem cell23_5414227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 5].length) (baseStart_5414227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414227 prefixEnd_5414227 := by exact prefixLift 5414227
  have htrace : WordTrace (prefixWord ++ tailWord_5414227) baseStart_5414227 baseEnd_5414227 := by
    simpa [prefixWord, tailWord_5414227, baseEnd_5414227] using wordTrace_append hprefix tailTrace_5414227
  have hstable : (prefixWord ++ tailWord_5414227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414227).length < 2 ^ (prefixWord ++ tailWord_5414227).sum := by decide
  have hdescent : baseEnd_5414227 < baseStart_5414227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414231 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 5]
def baseStart_5414231 : Nat := 118140960795 + 5414231 * 2 ^ 59
def prefixEnd_5414231 : Nat := 4983230072969 + 3 ^ 40 * 5414231 * 2
def baseEnd_5414231 : Nat := 308900319719234614445879

theorem tailTrace_5414231 : CollatzResearch.WordTrace tailWord_5414231 prefixEnd_5414231 308900319719234614445879 := by
  unfold tailWord_5414231
  simp only [CollatzResearch.WordTrace]
  refine ⟨197473227648173238882610547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131648818432115492588407031 197473227648173238882610547)
  ·
    refine ⟨296209841472259858323915821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197473227648173238882610547 296209841472259858323915821)
    ·
      refine ⟨111078690552097446871468433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296209841472259858323915821 111078690552097446871468433)
      ·
        refine ⟨83309017914073085153601325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111078690552097446871468433 83309017914073085153601325)
        ·
          refine ⟨31240881717777406932600497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83309017914073085153601325 31240881717777406932600497)
          ·
            refine ⟨23430661288333055199450373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31240881717777406932600497 23430661288333055199450373)
            ·
              refine ⟨4393248991562447849896945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23430661288333055199450373 4393248991562447849896945)
              ·
                refine ⟨3294936743671835887422709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4393248991562447849896945 3294936743671835887422709)
                ·
                  refine ⟨308900319719234614445879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3294936743671835887422709 308900319719234614445879)
                  ·
                    rfl

theorem cell23_5414231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 5].length) (baseStart_5414231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414231 prefixEnd_5414231 := by exact prefixLift 5414231
  have htrace : WordTrace (prefixWord ++ tailWord_5414231) baseStart_5414231 baseEnd_5414231 := by
    simpa [prefixWord, tailWord_5414231, baseEnd_5414231] using wordTrace_append hprefix tailTrace_5414231
  have hstable : (prefixWord ++ tailWord_5414231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414231).length < 2 ^ (prefixWord ++ tailWord_5414231).sum := by decide
  have hdescent : baseEnd_5414231 < baseStart_5414231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414234 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2]
def baseStart_5414234 : Nat := 118140960795 + 5414234 * 2 ^ 59
def prefixEnd_5414234 : Nat := 4983230072969 + 3 ^ 40 * 5414234 * 2
def baseEnd_5414234 : Nat := 2780104417915075018275397

theorem tailTrace_5414234 : CollatzResearch.WordTrace tailWord_5414234 prefixEnd_5414234 2780104417915075018275397 := by
  unfold tailWord_5414234
  simp only [CollatzResearch.WordTrace]
  refine ⟨49368334266790592598742439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131648891378108246929979837 49368334266790592598742439)
  ·
    refine ⟨74052501400185888898113659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49368334266790592598742439 74052501400185888898113659)
    ·
      refine ⟨111078752100278833347170489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74052501400185888898113659 111078752100278833347170489)
      ·
        refine ⟨83309064075209125010377867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111078752100278833347170489 83309064075209125010377867)
        ·
          refine ⟨124963596112813687515566801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83309064075209125010377867 124963596112813687515566801)
          ·
            refine ⟨93722697084610265636675101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124963596112813687515566801 93722697084610265636675101)
            ·
              refine ⟨35146011406728849613753163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93722697084610265636675101 35146011406728849613753163)
              ·
                refine ⟨52719017110093274420629745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35146011406728849613753163 52719017110093274420629745)
                ·
                  refine ⟨39539262832569955815472309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52719017110093274420629745 39539262832569955815472309)
                  ·
                    refine ⟨3706805890553433357700529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39539262832569955815472309 3706805890553433357700529)
                    ·
                      refine ⟨2780104417915075018275397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3706805890553433357700529 2780104417915075018275397)
                      ·
                        rfl

theorem cell23_5414234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_5414234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414234 prefixEnd_5414234 := by exact prefixLift 5414234
  have htrace : WordTrace (prefixWord ++ tailWord_5414234) baseStart_5414234 baseEnd_5414234 := by
    simpa [prefixWord, tailWord_5414234, baseEnd_5414234] using wordTrace_append hprefix tailTrace_5414234
  have hstable : (prefixWord ++ tailWord_5414234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414234).length < 2 ^ (prefixWord ++ tailWord_5414234).sum := by decide
  have hdescent : baseEnd_5414234 < baseStart_5414234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414277 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_5414277 : Nat := 118140960795 + 5414277 * 2 ^ 59
def prefixEnd_5414277 : Nat := 4983230072969 + 3 ^ 40 * 5414277 * 2
def baseEnd_5414277 : Nat := 2780126497583218350037699

theorem tailTrace_5414277 : CollatzResearch.WordTrace tailWord_5414277 prefixEnd_5414277 2780126497583218350037699 := by
  unfold tailWord_5414277
  simp only [CollatzResearch.WordTrace]
  refine ⟨197474905406006588738785085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131649936937337725825856723 197474905406006588738785085)
  ·
    refine ⟨74053089527252470777044407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197474905406006588738785085 74053089527252470777044407)
    ·
      refine ⟨111079634290878706165566611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74053089527252470777044407 111079634290878706165566611)
      ·
        refine ⟨166619451436318059248349917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111079634290878706165566611 166619451436318059248349917)
        ·
          refine ⟨62482294288619272218131219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166619451436318059248349917 62482294288619272218131219)
          ·
            refine ⟨93723441432928908327196829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62482294288619272218131219 93723441432928908327196829)
            ·
              refine ⟨35146290537348340622698811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93723441432928908327196829 35146290537348340622698811)
              ·
                refine ⟨52719435806022510934048217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35146290537348340622698811 52719435806022510934048217)
                ·
                  refine ⟨39539576854516883200536163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52719435806022510934048217 39539576854516883200536163)
                  ·
                    refine ⟨59309365281775324800804245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39539576854516883200536163 59309365281775324800804245)
                    ·
                      refine ⟨2780126497583218350037699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59309365281775324800804245 2780126497583218350037699)
                      ·
                        rfl

theorem cell23_5414277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_5414277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414277 prefixEnd_5414277 := by exact prefixLift 5414277
  have htrace : WordTrace (prefixWord ++ tailWord_5414277) baseStart_5414277 baseEnd_5414277 := by
    simpa [prefixWord, tailWord_5414277, baseEnd_5414277] using wordTrace_append hprefix tailTrace_5414277
  have hstable : (prefixWord ++ tailWord_5414277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414277).length < 2 ^ (prefixWord ++ tailWord_5414277).sum := by decide
  have hdescent : baseEnd_5414277 < baseStart_5414277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414284 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_5414284 : Nat := 118140960795 + 5414284 * 2 ^ 59
def prefixEnd_5414284 : Nat := 4983230072969 + 3 ^ 40 * 5414284 * 2
def baseEnd_5414284 : Nat := 2780130091947799822650167

theorem tailTrace_5414284 : CollatzResearch.WordTrace tailWord_5414284 prefixEnd_5414284 2780130091947799822650167 := by
  unfold tailWord_5414284
  simp only [CollatzResearch.WordTrace]
  refine ⟨98737580358490614467144953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131650107144654152622859937 98737580358490614467144953)
  ·
    refine ⟨74053185268867960850358715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98737580358490614467144953 74053185268867960850358715)
    ·
      refine ⟨111079777903301941275538073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74053185268867960850358715 111079777903301941275538073)
      ·
        refine ⟨83309833427476455956653555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111079777903301941275538073 83309833427476455956653555)
        ·
          refine ⟨124964750141214683934980333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83309833427476455956653555 124964750141214683934980333)
          ·
            refine ⟨46861781302955506475617625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124964750141214683934980333 46861781302955506475617625)
            ·
              refine ⟨35146335977216629856713219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46861781302955506475617625 35146335977216629856713219)
              ·
                refine ⟨52719503965824944785069829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35146335977216629856713219 52719503965824944785069829)
                ·
                  refine ⟨9884906993592177147200593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52719503965824944785069829 9884906993592177147200593)
                  ·
                    refine ⟨7413680245194132860400445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9884906993592177147200593 7413680245194132860400445)
                    ·
                      refine ⟨2780130091947799822650167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7413680245194132860400445 2780130091947799822650167)
                      ·
                        rfl

theorem cell23_5414284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_5414284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414284 prefixEnd_5414284 := by exact prefixLift 5414284
  have htrace : WordTrace (prefixWord ++ tailWord_5414284) baseStart_5414284 baseEnd_5414284 := by
    simpa [prefixWord, tailWord_5414284, baseEnd_5414284] using wordTrace_append hprefix tailTrace_5414284
  have hstable : (prefixWord ++ tailWord_5414284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414284).length < 2 ^ (prefixWord ++ tailWord_5414284).sum := by decide
  have hdescent : baseEnd_5414284 < baseStart_5414284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414307 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_5414307 : Nat := 118140960795 + 5414307 * 2 ^ 59
def prefixEnd_5414307 : Nat := 4983230072969 + 3 ^ 40 * 5414307 * 2
def baseEnd_5414307 : Nat := 2780141902002853232662561

theorem tailTrace_5414307 : CollatzResearch.WordTrace tailWord_5414307 prefixEnd_5414307 2780141902002853232662561 := by
  unfold tailWord_5414307
  simp only [CollatzResearch.WordTrace]
  refine ⟨197475999595897903862377175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131650666397265269241584783 197475999595897903862377175)
  ·
    refine ⟨296213999393846855793565763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197475999595897903862377175 296213999393846855793565763)
    ·
      refine ⟨444320999090770283690348645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296213999393846855793565763 444320999090770283690348645)
      ·
        refine ⟨83310187329519428191940371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 444320999090770283690348645 83310187329519428191940371)
        ·
          refine ⟨124965280994279142287910557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83310187329519428191940371 124965280994279142287910557)
          ·
            refine ⟨46861980372854678357966459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124965280994279142287910557 46861980372854678357966459)
            ·
              refine ⟨70292970559282017536949689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46861980372854678357966459 70292970559282017536949689)
              ·
                refine ⟨52719727919461513152712267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70292970559282017536949689 52719727919461513152712267)
                ·
                  refine ⟨79079591879192269729068401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52719727919461513152712267 79079591879192269729068401)
                  ·
                    refine ⟨59309693909394202296801301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79079591879192269729068401 59309693909394202296801301)
                    ·
                      refine ⟨2780141902002853232662561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59309693909394202296801301 2780141902002853232662561)
                      ·
                        rfl

theorem cell23_5414307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_5414307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414307 prefixEnd_5414307 := by exact prefixLift 5414307
  have htrace : WordTrace (prefixWord ++ tailWord_5414307) baseStart_5414307 baseEnd_5414307 := by
    simpa [prefixWord, tailWord_5414307, baseEnd_5414307] using wordTrace_append hprefix tailTrace_5414307
  have hstable : (prefixWord ++ tailWord_5414307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414307).length < 2 ^ (prefixWord ++ tailWord_5414307).sum := by decide
  have hdescent : baseEnd_5414307 < baseStart_5414307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414325 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_5414325 : Nat := 118140960795 + 5414325 * 2 ^ 59
def prefixEnd_5414325 : Nat := 4983230072969 + 3 ^ 40 * 5414325 * 2
def baseEnd_5414325 : Nat := 926717048218211387412493

theorem tailTrace_5414325 : CollatzResearch.WordTrace tailWord_5414325 prefixEnd_5414325 926717048218211387412493 := by
  unfold tailWord_5414325
  simp only [CollatzResearch.WordTrace]
  refine ⟨197476656109832692936532429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131651104073221795291021619 197476656109832692936532429)
  ·
    refine ⟨74053746041187259851199661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197476656109832692936532429 74053746041187259851199661)
    ·
      refine ⟨27770154765445222444199873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74053746041187259851199661 27770154765445222444199873)
      ·
        refine ⟨20827616074083916833149905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27770154765445222444199873 20827616074083916833149905)
        ·
          refine ⟨15620712055562937624862429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20827616074083916833149905 15620712055562937624862429)
          ·
            refine ⟨5857767020836101609323411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15620712055562937624862429 5857767020836101609323411)
            ·
              refine ⟨8786650531254152413985117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5857767020836101609323411 8786650531254152413985117)
              ·
                refine ⟨3294993949220307155244419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8786650531254152413985117 3294993949220307155244419)
                ·
                  refine ⟨4942490923830460732866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294993949220307155244419 4942490923830460732866629)
                  ·
                    refine ⟨926717048218211387412493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4942490923830460732866629 926717048218211387412493)
                    ·
                      rfl

theorem cell23_5414325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_5414325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414325 prefixEnd_5414325 := by exact prefixLift 5414325
  have htrace : WordTrace (prefixWord ++ tailWord_5414325) baseStart_5414325 baseEnd_5414325 := by
    simpa [prefixWord, tailWord_5414325, baseEnd_5414325] using wordTrace_append hprefix tailTrace_5414325
  have hstable : (prefixWord ++ tailWord_5414325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414325).length < 2 ^ (prefixWord ++ tailWord_5414325).sum := by decide
  have hdescent : baseEnd_5414325 < baseStart_5414325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414334 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_5414334 : Nat := 118140960795 + 5414334 * 2 ^ 59
def prefixEnd_5414334 : Nat := 4983230072969 + 3 ^ 40 * 5414334 * 2
def baseEnd_5414334 : Nat := 926718588660174875674979

theorem tailTrace_5414334 : CollatzResearch.WordTrace tailWord_5414334 prefixEnd_5414334 926718588660174875674979 := by
  unfold tailWord_5414334
  simp only [CollatzResearch.WordTrace]
  refine ⟨24684623045850010934201257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131651322911200058315740037 24684623045850010934201257)
  ·
    refine ⟨18513467284387508200650943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24684623045850010934201257 18513467284387508200650943)
    ·
      refine ⟨27770200926581262300976415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18513467284387508200650943 27770200926581262300976415)
      ·
        refine ⟨41655301389871893451464623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27770200926581262300976415 41655301389871893451464623)
        ·
          refine ⟨62482952084807840177196935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41655301389871893451464623 62482952084807840177196935)
          ·
            refine ⟨93724428127211760265795403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62482952084807840177196935 93724428127211760265795403)
            ·
              refine ⟨140586642190817640398693105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93724428127211760265795403 140586642190817640398693105)
              ·
                refine ⟨105439981643113230299019829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140586642190817640398693105 105439981643113230299019829)
                ·
                  refine ⟨9884998279041865340533109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105439981643113230299019829 9884998279041865340533109)
                  ·
                    refine ⟨926718588660174875674979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9884998279041865340533109 926718588660174875674979)
                    ·
                      rfl

theorem cell23_5414334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_5414334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414334 prefixEnd_5414334 := by exact prefixLift 5414334
  have htrace : WordTrace (prefixWord ++ tailWord_5414334) baseStart_5414334 baseEnd_5414334 := by
    simpa [prefixWord, tailWord_5414334, baseEnd_5414334] using wordTrace_append hprefix tailTrace_5414334
  have hstable : (prefixWord ++ tailWord_5414334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414334).length < 2 ^ (prefixWord ++ tailWord_5414334).sum := by decide
  have hdescent : baseEnd_5414334 < baseStart_5414334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414348 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5414348 : Nat := 118140960795 + 5414348 * 2 ^ 59
def prefixEnd_5414348 : Nat := 4983230072969 + 3 ^ 40 * 5414348 * 2
def baseEnd_5414348 : Nat := 2780162954709687572249873

theorem tailTrace_5414348 : CollatzResearch.WordTrace tailWord_5414348 prefixEnd_5414348 2780162954709687572249873 := by
  unfold tailWord_5414348
  simp only [CollatzResearch.WordTrace]
  refine ⟨98738747494374683932309849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131651663325832911909746465 98738747494374683932309849)
  ·
    refine ⟨74054060620781012949232387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98738747494374683932309849 74054060620781012949232387)
    ·
      refine ⟨111081090931171519423848581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74054060620781012949232387 111081090931171519423848581)
      ·
        refine ⟨20827704549594659891971609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111081090931171519423848581 20827704549594659891971609)
        ·
          refine ⟨15620778412195994918978707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20827704549594659891971609 15620778412195994918978707)
          ·
            refine ⟨23431167618293992378468061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15620778412195994918978707 23431167618293992378468061)
            ·
              refine ⟨8786687856860247141925523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23431167618293992378468061 8786687856860247141925523)
              ·
                refine ⟨13180031785290370712888285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8786687856860247141925523 13180031785290370712888285)
                ·
                  refine ⟨4942511919483889017333107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13180031785290370712888285 4942511919483889017333107)
                  ·
                    refine ⟨7413767879225833525999661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4942511919483889017333107 7413767879225833525999661)
                    ·
                      refine ⟨2780162954709687572249873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7413767879225833525999661 2780162954709687572249873)
                      ·
                        rfl

theorem cell23_5414348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5414348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414348 prefixEnd_5414348 := by exact prefixLift 5414348
  have htrace : WordTrace (prefixWord ++ tailWord_5414348) baseStart_5414348 baseEnd_5414348 := by
    simpa [prefixWord, tailWord_5414348, baseEnd_5414348] using wordTrace_append hprefix tailTrace_5414348
  have hstable : (prefixWord ++ tailWord_5414348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414348).length < 2 ^ (prefixWord ++ tailWord_5414348).sum := by decide
  have hdescent : baseEnd_5414348 < baseStart_5414348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414371 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5414371 : Nat := 118140960795 + 5414371 * 2 ^ 59
def prefixEnd_5414371 : Nat := 4983230072969 + 3 ^ 40 * 5414371 * 2
def baseEnd_5414371 : Nat := 2780174764764740982262267

theorem tailTrace_5414371 : CollatzResearch.WordTrace tailWord_5414371 prefixEnd_5414371 2780174764764740982262267 := by
  unfold tailWord_5414371
  simp only [CollatzResearch.WordTrace]
  refine ⟨197478333867666042792706967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131652222578444028528471311 197478333867666042792706967)
  ·
    refine ⟨296217500801499064189060451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197478333867666042792706967 296217500801499064189060451)
    ·
      refine ⟨444326251202248596283590677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296217500801499064189060451 444326251202248596283590677)
      ·
        refine ⟨20827793025105402950793313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 444326251202248596283590677 20827793025105402950793313)
        ·
          refine ⟨15620844768829052213094985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20827793025105402950793313 15620844768829052213094985)
          ·
            refine ⟨11715633576621789159821239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15620844768829052213094985 11715633576621789159821239)
            ·
              refine ⟨17573450364932683739731859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11715633576621789159821239 17573450364932683739731859)
              ·
                refine ⟨26360175547399025609597789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17573450364932683739731859 26360175547399025609597789)
                ·
                  refine ⟨9885065830274634603599171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26360175547399025609597789 9885065830274634603599171)
                  ·
                    refine ⟨14827598745411951905398757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9885065830274634603599171 14827598745411951905398757)
                    ·
                      refine ⟨2780174764764740982262267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14827598745411951905398757 2780174764764740982262267)
                      ·
                        rfl

theorem cell23_5414371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5414371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414371 prefixEnd_5414371 := by exact prefixLift 5414371
  have htrace : WordTrace (prefixWord ++ tailWord_5414371) baseStart_5414371 baseEnd_5414371 := by
    simpa [prefixWord, tailWord_5414371, baseEnd_5414371] using wordTrace_append hprefix tailTrace_5414371
  have hstable : (prefixWord ++ tailWord_5414371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414371).length < 2 ^ (prefixWord ++ tailWord_5414371).sum := by decide
  have hdescent : baseEnd_5414371 < baseStart_5414371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414384 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_5414384 : Nat := 118140960795 + 5414384 * 2 ^ 59
def prefixEnd_5414384 : Nat := 4983230072969 + 3 ^ 40 * 5414384 * 2
def baseEnd_5414384 : Nat := 2780181440013249431399707

theorem tailTrace_5414384 : CollatzResearch.WordTrace tailWord_5414384 prefixEnd_5414384 2780181440013249431399707 := by
  unfold tailWord_5414384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98739404008309473006465103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131652538677745964008620137 98739404008309473006465103)
  ·
    refine ⟨148109106012464209509697655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98739404008309473006465103 148109106012464209509697655)
    ·
      refine ⟨222163659018696314264546483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148109106012464209509697655 222163659018696314264546483)
      ·
        refine ⟨333245488528044471396819725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222163659018696314264546483 333245488528044471396819725)
        ·
          refine ⟨124967058198016676773807397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333245488528044471396819725 124967058198016676773807397)
          ·
            refine ⟨23431323412128126895088887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124967058198016676773807397 23431323412128126895088887)
            ·
              refine ⟨35146985118192190342633331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23431323412128126895088887 35146985118192190342633331)
              ·
                refine ⟨52720477677288285513949997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35146985118192190342633331 52720477677288285513949997)
                ·
                  refine ⟨19770179128983107067731249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52720477677288285513949997 19770179128983107067731249)
                  ·
                    refine ⟨14827634346737330300798437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19770179128983107067731249 14827634346737330300798437)
                    ·
                      refine ⟨2780181440013249431399707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14827634346737330300798437 2780181440013249431399707)
                      ·
                        rfl

theorem cell23_5414384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_5414384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414384 prefixEnd_5414384 := by exact prefixLift 5414384
  have htrace : WordTrace (prefixWord ++ tailWord_5414384) baseStart_5414384 baseEnd_5414384 := by
    simpa [prefixWord, tailWord_5414384, baseEnd_5414384] using wordTrace_append hprefix tailTrace_5414384
  have hstable : (prefixWord ++ tailWord_5414384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414384).length < 2 ^ (prefixWord ++ tailWord_5414384).sum := by decide
  have hdescent : baseEnd_5414384 < baseStart_5414384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414411 : List Nat := [1, 1, 1, 1, 8, 2, 1, 8]
def baseStart_5414411 : Nat := 118140960795 + 5414411 * 2 ^ 59
def prefixEnd_5414411 : Nat := 4983230072969 + 3 ^ 40 * 5414411 * 2
def baseEnd_5414411 : Nat := 102970196444108178731929

theorem tailTrace_5414411 : CollatzResearch.WordTrace tailWord_5414411 prefixEnd_5414411 102970196444108178731929 := by
  unfold tailWord_5414411
  simp only [CollatzResearch.WordTrace]
  refine ⟨197479792787521129624163087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131653195191680753082775391 197479792787521129624163087)
  ·
    refine ⟨296219689181281694436244631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197479792787521129624163087 296219689181281694436244631)
    ·
      refine ⟨444329533771922541654366947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296219689181281694436244631 444329533771922541654366947)
      ·
        refine ⟨666494300657883812481550421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444329533771922541654366947 666494300657883812481550421)
        ·
          refine ⟨7810480085834575927518169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 666494300657883812481550421 7810480085834575927518169)
          ·
            refine ⟨5857860064375931945638627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7810480085834575927518169 5857860064375931945638627)
            ·
              refine ⟨8786790096563897918457941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5857860064375931945638627 8786790096563897918457941)
              ·
                refine ⟨102970196444108178731929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8786790096563897918457941 102970196444108178731929)
                ·
                  rfl

theorem cell23_5414411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 8].length) (baseStart_5414411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414411 prefixEnd_5414411 := by exact prefixLift 5414411
  have htrace : WordTrace (prefixWord ++ tailWord_5414411) baseStart_5414411 baseEnd_5414411 := by
    simpa [prefixWord, tailWord_5414411, baseEnd_5414411] using wordTrace_append hprefix tailTrace_5414411
  have hstable : (prefixWord ++ tailWord_5414411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414411).length < 2 ^ (prefixWord ++ tailWord_5414411).sum := by decide
  have hdescent : baseEnd_5414411 < baseStart_5414411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414421 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_5414421 : Nat := 118140960795 + 5414421 * 2 ^ 59
def prefixEnd_5414421 : Nat := 4983230072969 + 3 ^ 40 * 5414421 * 2
def baseEnd_5414421 : Nat := 2780200438797465786637037

theorem tailTrace_5414421 : CollatzResearch.WordTrace tailWord_5414421 prefixEnd_5414421 2780200438797465786637037 := by
  unfold tailWord_5414421
  simp only [CollatzResearch.WordTrace]
  refine ⟨197480157517484901332027117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131653438344989934221351411 197480157517484901332027117)
  ·
    refine ⟨74055059069056837999510169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197480157517484901332027117 74055059069056837999510169)
    ·
      refine ⟨55541294301792628499632627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74055059069056837999510169 55541294301792628499632627)
      ·
        refine ⟨83311941452688942749448941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55541294301792628499632627 83311941452688942749448941)
        ·
          refine ⟨31241978044758353531043353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83311941452688942749448941 31241978044758353531043353)
          ·
            refine ⟨23431483533568765148282515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31241978044758353531043353 23431483533568765148282515)
            ·
              refine ⟨35147225300353147722423773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23431483533568765148282515 35147225300353147722423773)
              ·
                refine ⟨13180209487632430395908915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35147225300353147722423773 13180209487632430395908915)
                ·
                  refine ⟨19770314231448645593863373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13180209487632430395908915 19770314231448645593863373)
                  ·
                    refine ⟨7413867836793242097698765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19770314231448645593863373 7413867836793242097698765)
                    ·
                      refine ⟨2780200438797465786637037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7413867836793242097698765 2780200438797465786637037)
                      ·
                        rfl

theorem cell23_5414421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_5414421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414421 prefixEnd_5414421 := by exact prefixLift 5414421
  have htrace : WordTrace (prefixWord ++ tailWord_5414421) baseStart_5414421 baseEnd_5414421 := by
    simpa [prefixWord, tailWord_5414421, baseEnd_5414421] using wordTrace_append hprefix tailTrace_5414421
  have hstable : (prefixWord ++ tailWord_5414421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414421).length < 2 ^ (prefixWord ++ tailWord_5414421).sum := by decide
  have hdescent : baseEnd_5414421 < baseStart_5414421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414455 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_5414455 : Nat := 118140960795 + 5414455 * 2 ^ 59
def prefixEnd_5414455 : Nat := 4983230072969 + 3 ^ 40 * 5414455 * 2
def baseEnd_5414455 : Nat := 2780217897139718653611881

theorem tailTrace_5414455 : CollatzResearch.WordTrace tailWord_5414455 prefixEnd_5414455 2780217897139718653611881 := by
  unfold tailWord_5414455
  simp only [CollatzResearch.WordTrace]
  refine ⟨197481397599361725138764819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131654265066241150092509879 197481397599361725138764819)
  ·
    refine ⟨296222096399042587708147229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197481397599361725138764819 296222096399042587708147229)
    ·
      refine ⟨111083286149640970390555211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296222096399042587708147229 111083286149640970390555211)
      ·
        refine ⟨166624929224461455585832817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111083286149640970390555211 166624929224461455585832817)
        ·
          refine ⟨124968696918346091689374613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166624929224461455585832817 124968696918346091689374613)
          ·
            refine ⟨5857907668047473047939435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124968696918346091689374613 5857907668047473047939435)
            ·
              refine ⟨8786861502071209571909153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5857907668047473047939435 8786861502071209571909153)
              ·
                refine ⟨6590146126553407178931865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8786861502071209571909153 6590146126553407178931865)
                ·
                  refine ⟨4942609594915055384198899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6590146126553407178931865 4942609594915055384198899)
                  ·
                    refine ⟨7413914392372583076298349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4942609594915055384198899 7413914392372583076298349)
                    ·
                      refine ⟨2780217897139718653611881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7413914392372583076298349 2780217897139718653611881)
                      ·
                        rfl

theorem cell23_5414455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_5414455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414455 prefixEnd_5414455 := by exact prefixLift 5414455
  have htrace : WordTrace (prefixWord ++ tailWord_5414455) baseStart_5414455 baseEnd_5414455 := by
    simpa [prefixWord, tailWord_5414455, baseEnd_5414455] using wordTrace_append hprefix tailTrace_5414455
  have hstable : (prefixWord ++ tailWord_5414455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414455).length < 2 ^ (prefixWord ++ tailWord_5414455).sum := by decide
  have hdescent : baseEnd_5414455 < baseStart_5414455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414464 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_5414464 : Nat := 118140960795 + 5414464 * 2 ^ 59
def prefixEnd_5414464 : Nat := 4983230072969 + 3 ^ 40 * 5414464 * 2
def baseEnd_5414464 : Nat := 2780222518465609118399339

theorem tailTrace_5414464 : CollatzResearch.WordTrace tailWord_5414464 prefixEnd_5414464 2780222518465609118399339 := by
  unfold tailWord_5414464
  simp only [CollatzResearch.WordTrace]
  refine ⟨98740862928164559837921223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131654483904219413117228297 98740862928164559837921223)
  ·
    refine ⟨148111294392246839756881835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98740862928164559837921223 148111294392246839756881835)
    ·
      refine ⟨222166941588370259635322753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148111294392246839756881835 222166941588370259635322753)
      ·
        refine ⟨166625206191277694726492065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222166941588370259635322753 166625206191277694726492065)
        ·
          refine ⟨124968904643458271044869049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166625206191277694726492065 124968904643458271044869049)
          ·
            refine ⟨93726678482593703283651787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124968904643458271044869049 93726678482593703283651787)
            ·
              refine ⟨140590017723890554925477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93726678482593703283651787 140590017723890554925477681)
              ·
                refine ⟨105442513292917916194108261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140590017723890554925477681 105442513292917916194108261)
                ·
                  refine ⟨19770471242422109286395299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105442513292917916194108261 19770471242422109286395299)
                  ·
                    refine ⟨29655706863633163929592949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19770471242422109286395299 29655706863633163929592949)
                    ·
                      refine ⟨2780222518465609118399339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29655706863633163929592949 2780222518465609118399339)
                      ·
                        rfl

theorem cell23_5414464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_5414464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414464 prefixEnd_5414464 := by exact prefixLift 5414464
  have htrace : WordTrace (prefixWord ++ tailWord_5414464) baseStart_5414464 baseEnd_5414464 := by
    simpa [prefixWord, tailWord_5414464, baseEnd_5414464] using wordTrace_append hprefix tailTrace_5414464
  have hstable : (prefixWord ++ tailWord_5414464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414464).length < 2 ^ (prefixWord ++ tailWord_5414464).sum := by decide
  have hdescent : baseEnd_5414464 < baseStart_5414464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414518 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_5414518 : Nat := 118140960795 + 5414518 * 2 ^ 59
def prefixEnd_5414518 : Nat := 4983230072969 + 3 ^ 40 * 5414518 * 2
def baseEnd_5414518 : Nat := 308916694046772434124899

theorem tailTrace_5414518 : CollatzResearch.WordTrace tailWord_5414518 prefixEnd_5414518 308916694046772434124899 := by
  unfold tailWord_5414518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12342730962383342931144263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131655796932088991265538805 12342730962383342931144263)
  ·
    refine ⟨18514096443575014396716395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12342730962383342931144263 18514096443575014396716395)
    ·
      refine ⟨27771144665362521595074593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18514096443575014396716395 27771144665362521595074593)
      ·
        refine ⟨20828358499021891196305945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27771144665362521595074593 20828358499021891196305945)
        ·
          refine ⟨15621268874266418397229459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20828358499021891196305945 15621268874266418397229459)
          ·
            refine ⟨23431903311399627595844189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15621268874266418397229459 23431903311399627595844189)
            ·
              refine ⟨8786963741774860348441571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23431903311399627595844189 8786963741774860348441571)
              ·
                refine ⟨13180445612662290522662357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8786963741774860348441571 13180445612662290522662357)
                ·
                  refine ⟨308916694046772434124899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13180445612662290522662357 308916694046772434124899)
                  ·
                    rfl

theorem cell23_5414518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_5414518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414518 prefixEnd_5414518 := by exact prefixLift 5414518
  have htrace : WordTrace (prefixWord ++ tailWord_5414518) baseStart_5414518 baseEnd_5414518 := by
    simpa [prefixWord, tailWord_5414518, baseEnd_5414518] using wordTrace_append hprefix tailTrace_5414518
  have hstable : (prefixWord ++ tailWord_5414518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414518).length < 2 ^ (prefixWord ++ tailWord_5414518).sum := by decide
  have hdescent : baseEnd_5414518 < baseStart_5414518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414529 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_5414529 : Nat := 118140960795 + 5414529 * 2 ^ 59
def prefixEnd_5414529 : Nat := 4983230072969 + 3 ^ 40 * 5414529 * 2
def baseEnd_5414529 : Nat := 2780255894708151364086541

theorem tailTrace_5414529 : CollatzResearch.WordTrace tailWord_5414529 prefixEnd_5414529 2780255894708151364086541 := by
  unfold tailWord_5414529
  simp only [CollatzResearch.WordTrace]
  refine ⟨197484096601093635776958641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131656064400729090517972427 197484096601093635776958641)
  ·
    refine ⟨148113072450820226832718981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197484096601093635776958641 148113072450820226832718981)
    ·
      refine ⟨27771201084528792531134809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148113072450820226832718981 27771201084528792531134809)
      ·
        refine ⟨20828400813396594398351107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27771201084528792531134809 20828400813396594398351107)
        ·
          refine ⟨31242601220094891597526661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20828400813396594398351107 31242601220094891597526661)
          ·
            refine ⟨5857987728767792174536249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31242601220094891597526661 5857987728767792174536249)
            ·
              refine ⟨4393490796575844130902187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5857987728767792174536249 4393490796575844130902187)
              ·
                refine ⟨6590236194863766196353281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393490796575844130902187 6590236194863766196353281)
                ·
                  refine ⟨4942677146147824647264961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6590236194863766196353281 4942677146147824647264961)
                  ·
                    refine ⟨3707007859610868485448721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4942677146147824647264961 3707007859610868485448721)
                    ·
                      refine ⟨2780255894708151364086541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707007859610868485448721 2780255894708151364086541)
                      ·
                        rfl

theorem cell23_5414529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_5414529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414529 prefixEnd_5414529 := by exact prefixLift 5414529
  have htrace : WordTrace (prefixWord ++ tailWord_5414529) baseStart_5414529 baseEnd_5414529 := by
    simpa [prefixWord, tailWord_5414529, baseEnd_5414529] using wordTrace_append hprefix tailTrace_5414529
  have hstable : (prefixWord ++ tailWord_5414529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414529).length < 2 ^ (prefixWord ++ tailWord_5414529).sum := by decide
  have hdescent : baseEnd_5414529 < baseStart_5414529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414544 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_5414544 : Nat := 118140960795 + 5414544 * 2 ^ 59
def prefixEnd_5414544 : Nat := 4983230072969 + 3 ^ 40 * 5414544 * 2
def baseEnd_5414544 : Nat := 926754532305989601799657

theorem tailTrace_5414544 : CollatzResearch.WordTrace tailWord_5414544 prefixEnd_5414544 926754532305989601799657 := by
  unfold tailWord_5414544
  simp only [CollatzResearch.WordTrace]
  refine ⟨98742321848019646669377343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131656429130692862225836457 98742321848019646669377343)
  ·
    refine ⟨148113482772029470004066015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98742321848019646669377343 148113482772029470004066015)
    ·
      refine ⟨222170224158044205006099023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148113482772029470004066015 222170224158044205006099023)
      ·
        refine ⟨333255336237066307509148535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222170224158044205006099023 333255336237066307509148535)
        ·
          refine ⟨499883004355599461263722803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333255336237066307509148535 499883004355599461263722803)
          ·
            refine ⟨749824506533399191895584205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499883004355599461263722803 749824506533399191895584205)
            ·
              refine ⟨281184189950024696960844077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749824506533399191895584205 281184189950024696960844077)
              ·
                refine ⟨105444071231259261360316529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281184189950024696960844077 105444071231259261360316529)
                ·
                  refine ⟨79083053423444446020237397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105444071231259261360316529 79083053423444446020237397)
                  ·
                    refine ⟨926754532305989601799657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79083053423444446020237397 926754532305989601799657)
                    ·
                      rfl

theorem cell23_5414544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_5414544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414544 prefixEnd_5414544 := by exact prefixLift 5414544
  have htrace : WordTrace (prefixWord ++ tailWord_5414544) baseStart_5414544 baseEnd_5414544 := by
    simpa [prefixWord, tailWord_5414544, baseEnd_5414544] using wordTrace_append hprefix tailTrace_5414544
  have hstable : (prefixWord ++ tailWord_5414544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414544).length < 2 ^ (prefixWord ++ tailWord_5414544).sum := by decide
  have hdescent : baseEnd_5414544 < baseStart_5414544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414558 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5414558 : Nat := 118140960795 + 5414558 * 2 ^ 59
def prefixEnd_5414558 : Nat := 4983230072969 + 3 ^ 40 * 5414558 * 2
def baseEnd_5414558 : Nat := 2780270785647131750623907

theorem tailTrace_5414558 : CollatzResearch.WordTrace tailWord_5414558 prefixEnd_5414558 2780270785647131750623907 := by
  unfold tailWord_5414558
  simp only [CollatzResearch.WordTrace]
  refine ⟨24685644289748571716220541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131656769545325715819842885 24685644289748571716220541)
  ·
    refine ⟨9257116608655714393582703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24685644289748571716220541 9257116608655714393582703)
    ·
      refine ⟨13885674912983571590374055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9257116608655714393582703 13885674912983571590374055)
      ·
        refine ⟨20828512369475357385561083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13885674912983571590374055 20828512369475357385561083)
        ·
          refine ⟨31242768554213036078341625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20828512369475357385561083 31242768554213036078341625)
          ·
            refine ⟨23432076415659777058756219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31242768554213036078341625 23432076415659777058756219)
            ·
              refine ⟨35148114623489665588134329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23432076415659777058756219 35148114623489665588134329)
              ·
                refine ⟨26361085967617249191100747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35148114623489665588134329 26361085967617249191100747)
                ·
                  refine ⟨39541628951425873786651121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26361085967617249191100747 39541628951425873786651121)
                  ·
                    refine ⟨29656221713569405339988341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39541628951425873786651121 29656221713569405339988341)
                    ·
                      refine ⟨2780270785647131750623907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29656221713569405339988341 2780270785647131750623907)
                      ·
                        rfl

theorem cell23_5414558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5414558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414558 prefixEnd_5414558 := by exact prefixLift 5414558
  have htrace : WordTrace (prefixWord ++ tailWord_5414558) baseStart_5414558 baseEnd_5414558 := by
    simpa [prefixWord, tailWord_5414558, baseEnd_5414558] using wordTrace_append hprefix tailTrace_5414558
  have hstable : (prefixWord ++ tailWord_5414558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414558).length < 2 ^ (prefixWord ++ tailWord_5414558).sum := by decide
  have hdescent : baseEnd_5414558 < baseStart_5414558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414591 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 6]
def baseStart_5414591 : Nat := 118140960795 + 5414591 * 2 ^ 59
def prefixEnd_5414591 : Nat := 4983230072969 + 3 ^ 40 * 5414591 * 2
def baseEnd_5414591 : Nat := 308920858945414457945695

theorem tailTrace_5414591 : CollatzResearch.WordTrace tailWord_5414591 prefixEnd_5414591 308920858945414457945695 := by
  unfold tailWord_5414591
  simp only [CollatzResearch.WordTrace]
  refine ⟨197486357926869020365715627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131657571951246013577143751 197486357926869020365715627)
  ·
    refine ⟨296229536890303530548573441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197486357926869020365715627 296229536890303530548573441)
    ·
      refine ⟨222172152667727647911430081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296229536890303530548573441 222172152667727647911430081)
      ·
        refine ⟨166629114500795735933572561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222172152667727647911430081 166629114500795735933572561)
        ·
          refine ⟨124971835875596801950179421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166629114500795735933572561 124971835875596801950179421)
          ·
            refine ⟨46864438453348800731317283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124971835875596801950179421 46864438453348800731317283)
            ·
              refine ⟨70296657680023201096975925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46864438453348800731317283 70296657680023201096975925)
              ·
                refine ⟨6590311657502175102841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70296657680023201096975925 6590311657502175102841493)
                ·
                  refine ⟨308920858945414457945695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6590311657502175102841493 308920858945414457945695)
                  ·
                    rfl

theorem cell23_5414591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 6].length) (baseStart_5414591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414591 prefixEnd_5414591 := by exact prefixLift 5414591
  have htrace : WordTrace (prefixWord ++ tailWord_5414591) baseStart_5414591 baseEnd_5414591 := by
    simpa [prefixWord, tailWord_5414591, baseEnd_5414591] using wordTrace_append hprefix tailTrace_5414591
  have hstable : (prefixWord ++ tailWord_5414591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414591).length < 2 ^ (prefixWord ++ tailWord_5414591).sum := by decide
  have hdescent : baseEnd_5414591 < baseStart_5414591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414602 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_5414602 : Nat := 118140960795 + 5414602 * 2 ^ 59
def prefixEnd_5414602 : Nat := 4983230072969 + 3 ^ 40 * 5414602 * 2
def baseEnd_5414602 : Nat := 2780293378795929578473705

theorem tailTrace_5414602 : CollatzResearch.WordTrace tailWord_5414602 prefixEnd_5414602 2780293378795929578473705 := by
  unfold tailWord_5414602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49371689782457292311091515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131657839419886112829577373 49371689782457292311091515)
  ·
    refine ⟨74057534673685938466637273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49371689782457292311091515 74057534673685938466637273)
    ·
      refine ⟨55543151005264453849977955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74057534673685938466637273 55543151005264453849977955)
      ·
        refine ⟨83314726507896680774966933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55543151005264453849977955 83314726507896680774966933)
        ·
          refine ⟨3905377805057656911326575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83314726507896680774966933 3905377805057656911326575)
          ·
            refine ⟨5858066707586485366989863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905377805057656911326575 5858066707586485366989863)
            ·
              refine ⟨8787100061379728050484795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858066707586485366989863 8787100061379728050484795)
              ·
                refine ⟨13180650092069592075727193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8787100061379728050484795 13180650092069592075727193)
                ·
                  refine ⟨9885487569052194056795395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13180650092069592075727193 9885487569052194056795395)
                  ·
                    refine ⟨14828231353578291085193093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9885487569052194056795395 14828231353578291085193093)
                    ·
                      refine ⟨2780293378795929578473705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14828231353578291085193093 2780293378795929578473705)
                      ·
                        rfl

theorem cell23_5414602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_5414602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414602 prefixEnd_5414602 := by exact prefixLift 5414602
  have htrace : WordTrace (prefixWord ++ tailWord_5414602) baseStart_5414602 baseEnd_5414602 := by
    simpa [prefixWord, tailWord_5414602, baseEnd_5414602] using wordTrace_append hprefix tailTrace_5414602
  have hstable : (prefixWord ++ tailWord_5414602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414602).length < 2 ^ (prefixWord ++ tailWord_5414602).sum := by decide
  have hdescent : baseEnd_5414602 < baseStart_5414602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414612 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_5414612 : Nat := 118140960795 + 5414612 * 2 ^ 59
def prefixEnd_5414612 : Nat := 4983230072969 + 3 ^ 40 * 5414612 * 2
def baseEnd_5414612 : Nat := 926766171200824846449553

theorem tailTrace_5414612 : CollatzResearch.WordTrace tailWord_5414612 prefixEnd_5414612 926766171200824846449553 := by
  unfold tailWord_5414612
  simp only [CollatzResearch.WordTrace]
  refine ⟨98743561929896470476115045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131658082573195293968153393 98743561929896470476115045)
  ·
    refine ⟨18514417861855588214271571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98743561929896470476115045 18514417861855588214271571)
    ·
      refine ⟨27771626792783382321407357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18514417861855588214271571 27771626792783382321407357)
      ·
        refine ⟨10414360047293768370527759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27771626792783382321407357 10414360047293768370527759)
        ·
          refine ⟨15621540070940652555791639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10414360047293768370527759 15621540070940652555791639)
          ·
            refine ⟨23432310106410978833687459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15621540070940652555791639 23432310106410978833687459)
            ·
              refine ⟨35148465159616468250531189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23432310106410978833687459 35148465159616468250531189)
              ·
                refine ⟨3295168608714043898487299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35148465159616468250531189 3295168608714043898487299)
                ·
                  refine ⟨4942752913071065847730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295168608714043898487299 4942752913071065847730949)
                  ·
                    refine ⟨926766171200824846449553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4942752913071065847730949 926766171200824846449553)
                    ·
                      rfl

theorem cell23_5414612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_5414612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414612 prefixEnd_5414612 := by exact prefixLift 5414612
  have htrace : WordTrace (prefixWord ++ tailWord_5414612) baseStart_5414612 baseEnd_5414612 := by
    simpa [prefixWord, tailWord_5414612, baseEnd_5414612] using wordTrace_append hprefix tailTrace_5414612
  have hstable : (prefixWord ++ tailWord_5414612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414612).length < 2 ^ (prefixWord ++ tailWord_5414612).sum := by decide
  have hdescent : baseEnd_5414612 < baseStart_5414612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414625 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 6]
def baseStart_5414625 : Nat := 118140960795 + 5414625 * 2 ^ 59
def prefixEnd_5414625 : Nat := 4983230072969 + 3 ^ 40 * 5414625 * 2
def baseEnd_5414625 : Nat := 308922798761220332054011

theorem tailTrace_5414625 : CollatzResearch.WordTrace tailWord_5414625 prefixEnd_5414625 308922798761220332054011 := by
  unfold tailWord_5414625
  simp only [CollatzResearch.WordTrace]
  refine ⟨197487598008745844172453329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131658398672497229448302219 197487598008745844172453329)
  ·
    refine ⟨148115698506559383129339997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197487598008745844172453329 148115698506559383129339997)
    ·
      refine ⟨55543386939959768673502499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148115698506559383129339997 55543386939959768673502499)
      ·
        refine ⟨83315080409939653010253749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55543386939959768673502499 83315080409939653010253749)
        ·
          refine ⟨7810788788431842469711289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83315080409939653010253749 7810788788431842469711289)
          ·
            refine ⟨5858091591323881852283467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7810788788431842469711289 5858091591323881852283467)
            ·
              refine ⟨8787137386985822778425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858091591323881852283467 8787137386985822778425201)
              ·
                refine ⟨6590353040239367083818901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8787137386985822778425201 6590353040239367083818901)
                ·
                  refine ⟨308922798761220332054011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6590353040239367083818901 308922798761220332054011)
                  ·
                    rfl

theorem cell23_5414625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 6].length) (baseStart_5414625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414625 prefixEnd_5414625 := by exact prefixLift 5414625
  have htrace : WordTrace (prefixWord ++ tailWord_5414625) baseStart_5414625 baseEnd_5414625 := by
    simpa [prefixWord, tailWord_5414625, baseEnd_5414625] using wordTrace_append hprefix tailTrace_5414625
  have hstable : (prefixWord ++ tailWord_5414625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414625).length < 2 ^ (prefixWord ++ tailWord_5414625).sum := by decide
  have hdescent : baseEnd_5414625 < baseStart_5414625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414651 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 1, 6]
def baseStart_5414651 : Nat := 118140960795 + 5414651 * 2 ^ 59
def prefixEnd_5414651 : Nat := 4983230072969 + 3 ^ 40 * 5414651 * 2
def baseEnd_5414651 : Nat := 926772846449333295586993

theorem tailTrace_5414651 : CollatzResearch.WordTrace tailWord_5414651 prefixEnd_5414651 926772846449333295586993 := by
  unfold tailWord_5414651
  simp only [CollatzResearch.WordTrace]
  refine ⟨197488546306651650612899807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131659030871101100408599871 197488546306651650612899807)
  ·
    refine ⟨296232819459977475919349711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197488546306651650612899807 296232819459977475919349711)
    ·
      refine ⟨444349229189966213879024567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296232819459977475919349711 444349229189966213879024567)
      ·
        refine ⟨666523843784949320818536851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444349229189966213879024567 666523843784949320818536851)
        ·
          refine ⟨999785765677423981227805277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666523843784949320818536851 999785765677423981227805277)
          ·
            refine ⟨374919662129033992960426979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 999785765677423981227805277 374919662129033992960426979)
            ·
              refine ⟨562379493193550989440640469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374919662129033992960426979 562379493193550989440640469)
              ·
                refine ⟨13180769371723851315015011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 562379493193550989440640469 13180769371723851315015011)
                ·
                  refine ⟨19771154057585776972522517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13180769371723851315015011 19771154057585776972522517)
                  ·
                    refine ⟨926772846449333295586993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19771154057585776972522517 926772846449333295586993)
                    ·
                      rfl

theorem cell23_5414651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 6].length) (baseStart_5414651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414651 prefixEnd_5414651 := by exact prefixLift 5414651
  have htrace : WordTrace (prefixWord ++ tailWord_5414651) baseStart_5414651 baseEnd_5414651 := by
    simpa [prefixWord, tailWord_5414651, baseEnd_5414651] using wordTrace_append hprefix tailTrace_5414651
  have hstable : (prefixWord ++ tailWord_5414651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414651).length < 2 ^ (prefixWord ++ tailWord_5414651).sum := by decide
  have hdescent : baseEnd_5414651 < baseStart_5414651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414668 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_5414668 : Nat := 118140960795 + 5414668 * 2 ^ 59
def prefixEnd_5414668 : Nat := 4983230072969 + 3 ^ 40 * 5414668 * 2
def baseEnd_5414668 : Nat := 926775756173042106749467

theorem tailTrace_5414668 : CollatzResearch.WordTrace tailWord_5414668 prefixEnd_5414668 926775756173042106749467 := by
  unfold tailWord_5414668
  simp only [CollatzResearch.WordTrace]
  refine ⟨98744583173795031258134329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131659444231726708344179105 98744583173795031258134329)
  ·
    refine ⟨74058437380346273443600747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98744583173795031258134329 74058437380346273443600747)
    ·
      refine ⟨111087656070519410165401121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74058437380346273443600747 111087656070519410165401121)
      ·
        refine ⟨83315742052889557624050841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111087656070519410165401121 83315742052889557624050841)
        ·
          refine ⟨62486806539667168218038131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83315742052889557624050841 62486806539667168218038131)
          ·
            refine ⟨93730209809500752327057197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62486806539667168218038131 93730209809500752327057197)
            ·
              refine ⟨35148828678562782122646449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93730209809500752327057197 35148828678562782122646449)
              ·
                refine ⟨26361621508922086591984837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35148828678562782122646449 26361621508922086591984837)
                ·
                  refine ⟨4942804032922891235997157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26361621508922086591984837 4942804032922891235997157)
                  ·
                    refine ⟨926775756173042106749467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4942804032922891235997157 926775756173042106749467)
                    ·
                      rfl

theorem cell23_5414668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_5414668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414668 prefixEnd_5414668 := by exact prefixLift 5414668
  have htrace : WordTrace (prefixWord ++ tailWord_5414668) baseStart_5414668 baseEnd_5414668 := by
    simpa [prefixWord, tailWord_5414668, baseEnd_5414668] using wordTrace_append hprefix tailTrace_5414668
  have hstable : (prefixWord ++ tailWord_5414668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414668).length < 2 ^ (prefixWord ++ tailWord_5414668).sum := by decide
  have hdescent : baseEnd_5414668 < baseStart_5414668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414709 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_5414709 : Nat := 118140960795 + 5414709 * 2 ^ 59
def prefixEnd_5414709 : Nat := 4983230072969 + 3 ^ 40 * 5414709 * 2
def baseEnd_5414709 : Nat := 2780348321225960659835713

theorem tailTrace_5414709 : CollatzResearch.WordTrace tailWord_5414709 prefixEnd_5414709 2780348321225960659835713 := by
  unfold tailWord_5414709
  simp only [CollatzResearch.WordTrace]
  refine ⟨197490661740441526518511181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131660441160294351012340787 197490661740441526518511181)
  ·
    refine ⟨74058998152665572444441693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197490661740441526518511181 74058998152665572444441693)
    ·
      refine ⟨27772124307249589666665635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74058998152665572444441693 27772124307249589666665635)
      ·
        refine ⟨41658186460874384499998453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27772124307249589666665635 41658186460874384499998453)
        ·
          refine ⟨3905454980706973546874855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41658186460874384499998453 3905454980706973546874855)
          ·
            refine ⟨5858182471060460320312283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905454980706973546874855 5858182471060460320312283)
            ·
              refine ⟨8787273706590690480468425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858182471060460320312283 8787273706590690480468425)
              ·
                refine ⟨6590455279943017860351319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8787273706590690480468425 6590455279943017860351319)
                ·
                  refine ⟨9885682919914526790526979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590455279943017860351319 9885682919914526790526979)
                  ·
                    refine ⟨14828524379871790185790469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9885682919914526790526979 14828524379871790185790469)
                    ·
                      refine ⟨2780348321225960659835713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14828524379871790185790469 2780348321225960659835713)
                      ·
                        rfl

theorem cell23_5414709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_5414709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414709 prefixEnd_5414709 := by exact prefixLift 5414709
  have htrace : WordTrace (prefixWord ++ tailWord_5414709) baseStart_5414709 baseEnd_5414709 := by
    simpa [prefixWord, tailWord_5414709, baseEnd_5414709] using wordTrace_append hprefix tailTrace_5414709
  have hstable : (prefixWord ++ tailWord_5414709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414709).length < 2 ^ (prefixWord ++ tailWord_5414709).sum := by decide
  have hdescent : baseEnd_5414709 < baseStart_5414709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414711 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 4, 7]
def baseStart_5414711 : Nat := 118140960795 + 5414711 * 2 ^ 59
def prefixEnd_5414711 : Nat := 4983230072969 + 3 ^ 40 * 5414711 * 2
def baseEnd_5414711 : Nat := 926783116062423217336901

theorem tailTrace_5414711 : CollatzResearch.WordTrace tailWord_5414711 prefixEnd_5414711 926783116062423217336901 := by
  unfold tailWord_5414711
  simp only [CollatzResearch.WordTrace]
  refine ⟨197490734686434280860083987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131660489790956187240055991 197490734686434280860083987)
  ·
    refine ⟨296236102029651421290125981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197490734686434280860083987 296236102029651421290125981)
    ·
      refine ⟨111088538261119282983797243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296236102029651421290125981 111088538261119282983797243)
      ·
        refine ⟨166632807391678924475695865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111088538261119282983797243 166632807391678924475695865)
        ·
          refine ⟨124974605543759193356771899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166632807391678924475695865 124974605543759193356771899)
          ·
            refine ⟨187461908315638790035157849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124974605543759193356771899 187461908315638790035157849)
            ·
              refine ⟨140596431236729092526368387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187461908315638790035157849 140596431236729092526368387)
              ·
                refine ⟨210894646855093638789552581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140596431236729092526368387 210894646855093638789552581)
                ·
                  refine ⟨39542746285330057273041109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210894646855093638789552581 39542746285330057273041109)
                  ·
                    refine ⟨926783116062423217336901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39542746285330057273041109 926783116062423217336901)
                    ·
                      rfl

theorem cell23_5414711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_5414711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414711 prefixEnd_5414711 := by exact prefixLift 5414711
  have htrace : WordTrace (prefixWord ++ tailWord_5414711) baseStart_5414711 baseEnd_5414711 := by
    simpa [prefixWord, tailWord_5414711, baseEnd_5414711] using wordTrace_append hprefix tailTrace_5414711
  have hstable : (prefixWord ++ tailWord_5414711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414711).length < 2 ^ (prefixWord ++ tailWord_5414711).sum := by decide
  have hdescent : baseEnd_5414711 < baseStart_5414711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414712 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_5414712 : Nat := 118140960795 + 5414712 * 2 ^ 59
def prefixEnd_5414712 : Nat := 4983230072969 + 3 ^ 40 * 5414712 * 2
def baseEnd_5414712 : Nat := 2780349861667924148098199

theorem tailTrace_5414712 : CollatzResearch.WordTrace tailWord_5414712 prefixEnd_5414712 2780349861667924148098199 := by
  unfold tailWord_5414712
  simp only [CollatzResearch.WordTrace]
  refine ⟨98745385579715329015435195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131660514106287105353913593 98745385579715329015435195)
  ·
    refine ⟨148118078369572993523152793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98745385579715329015435195 148118078369572993523152793)
    ·
      refine ⟨111088558777179745142364595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148118078369572993523152793 111088558777179745142364595)
      ·
        refine ⟨166632838165769617713546893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111088558777179745142364595 166632838165769617713546893)
        ·
          refine ⟨62487314312163606642580085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166632838165769617713546893 62487314312163606642580085)
          ·
            refine ⟨5858185716765338122741883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62487314312163606642580085 5858185716765338122741883)
            ·
              refine ⟨8787278575148007184112825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858185716765338122741883 8787278575148007184112825)
              ·
                refine ⟨6590458931361005388084619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8787278575148007184112825 6590458931361005388084619)
                ·
                  refine ⟨9885688397041508082126929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590458931361005388084619 9885688397041508082126929)
                  ·
                    refine ⟨7414266297781131061595197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9885688397041508082126929 7414266297781131061595197)
                    ·
                      refine ⟨2780349861667924148098199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7414266297781131061595197 2780349861667924148098199)
                      ·
                        rfl

theorem cell23_5414712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_5414712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414712 prefixEnd_5414712 := by exact prefixLift 5414712
  have htrace : WordTrace (prefixWord ++ tailWord_5414712) baseStart_5414712 baseEnd_5414712 := by
    simpa [prefixWord, tailWord_5414712, baseEnd_5414712] using wordTrace_append hprefix tailTrace_5414712
  have hstable : (prefixWord ++ tailWord_5414712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414712).length < 2 ^ (prefixWord ++ tailWord_5414712).sum := by decide
  have hdescent : baseEnd_5414712 < baseStart_5414712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414726 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5414726 : Nat := 118140960795 + 5414726 * 2 ^ 59
def prefixEnd_5414726 : Nat := 4983230072969 + 3 ^ 40 * 5414726 * 2
def baseEnd_5414726 : Nat := 2780357050397087093323135

theorem tailTrace_5414726 : CollatzResearch.WordTrace tailWord_5414726 prefixEnd_5414726 2780357050397087093323135 := by
  unfold tailWord_5414726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6171602555668123075683751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131660854520919958947920021 6171602555668123075683751)
  ·
    refine ⟨9257403833502184613525627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6171602555668123075683751 9257403833502184613525627)
    ·
      refine ⟨13886105750253276920288441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9257403833502184613525627 13886105750253276920288441)
      ·
        refine ⟨10414579312689957690216331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13886105750253276920288441 10414579312689957690216331)
        ·
          refine ⟨15621868969034936535324497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10414579312689957690216331 15621868969034936535324497)
          ·
            refine ⟨11716401726776202401493373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15621868969034936535324497 11716401726776202401493373)
            ·
              refine ⟨4393650647541075900560015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11716401726776202401493373 4393650647541075900560015)
              ·
                refine ⟨6590475971311613850840023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393650647541075900560015 6590475971311613850840023)
                ·
                  refine ⟨9885713956967420776260035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590475971311613850840023 9885713956967420776260035)
                  ·
                    refine ⟨14828570935451131164390053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9885713956967420776260035 14828570935451131164390053)
                    ·
                      refine ⟨2780357050397087093323135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14828570935451131164390053 2780357050397087093323135)
                      ·
                        rfl

theorem cell23_5414726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5414726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414726 prefixEnd_5414726 := by exact prefixLift 5414726
  have htrace : WordTrace (prefixWord ++ tailWord_5414726) baseStart_5414726 baseEnd_5414726 := by
    simpa [prefixWord, tailWord_5414726, baseEnd_5414726] using wordTrace_append hprefix tailTrace_5414726
  have hstable : (prefixWord ++ tailWord_5414726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414726).length < 2 ^ (prefixWord ++ tailWord_5414726).sum := by decide
  have hdescent : baseEnd_5414726 < baseStart_5414726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414743 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 1, 2, 2]
def baseStart_5414743 : Nat := 118140960795 + 5414743 * 2 ^ 59
def prefixEnd_5414743 : Nat := 4983230072969 + 3 ^ 40 * 5414743 * 2
def baseEnd_5414743 : Nat := 2780365779568213526810557

theorem tailTrace_5414743 : CollatzResearch.WordTrace tailWord_5414743 prefixEnd_5414743 2780365779568213526810557 := by
  unfold tailWord_5414743
  simp only [CollatzResearch.WordTrace]
  refine ⟨197491901822318350325248883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131661267881545566883499255 197491901822318350325248883)
  ·
    refine ⟨296237852733477525487873325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197491901822318350325248883 296237852733477525487873325)
    ·
      refine ⟨111089194775054072057952497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296237852733477525487873325 111089194775054072057952497)
      ·
        refine ⟨83316896081290554043464373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111089194775054072057952497 83316896081290554043464373)
        ·
          refine ⟨7810959007620989441574785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83316896081290554043464373 7810959007620989441574785)
          ·
            refine ⟨5858219255715742081181089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7810959007620989441574785 5858219255715742081181089)
            ·
              refine ⟨4393664441786806560885817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5858219255715742081181089 4393664441786806560885817)
              ·
                refine ⟨3295248331340104920664363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4393664441786806560885817 3295248331340104920664363)
                ·
                  refine ⟨4942872497010157380996545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295248331340104920664363 4942872497010157380996545)
                  ·
                    refine ⟨3707154372757618035747409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4942872497010157380996545 3707154372757618035747409)
                    ·
                      refine ⟨2780365779568213526810557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707154372757618035747409 2780365779568213526810557)
                      ·
                        rfl

theorem cell23_5414743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_5414743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414743 prefixEnd_5414743 := by exact prefixLift 5414743
  have htrace : WordTrace (prefixWord ++ tailWord_5414743) baseStart_5414743 baseEnd_5414743 := by
    simpa [prefixWord, tailWord_5414743, baseEnd_5414743] using wordTrace_append hprefix tailTrace_5414743
  have hstable : (prefixWord ++ tailWord_5414743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414743).length < 2 ^ (prefixWord ++ tailWord_5414743).sum := by decide
  have hdescent : baseEnd_5414743 < baseStart_5414743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414768 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_5414768 : Nat := 118140960795 + 5414768 * 2 ^ 59
def prefixEnd_5414768 : Nat := 4983230072969 + 3 ^ 40 * 5414768 * 2
def baseEnd_5414768 : Nat := 2780378616584575928997941

theorem tailTrace_5414768 : CollatzResearch.WordTrace tailWord_5414768 prefixEnd_5414768 2780378616584575928997941 := by
  unfold tailWord_5414768
  simp only [CollatzResearch.WordTrace]
  refine ⟨98746406823613889797454479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131661875764818519729939305 98746406823613889797454479)
  ·
    refine ⟨148119610235420834696181719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98746406823613889797454479 148119610235420834696181719)
    ·
      refine ⟨222179415353131252044272579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148119610235420834696181719 222179415353131252044272579)
      ·
        refine ⟨333269123029696878066408869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222179415353131252044272579 333269123029696878066408869)
        ·
          refine ⟨62487960568068164637451663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333269123029696878066408869 62487960568068164637451663)
          ·
            refine ⟨93731940852102246956177495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62487960568068164637451663 93731940852102246956177495)
            ·
              refine ⟨140597911278153370434266243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93731940852102246956177495 140597911278153370434266243)
              ·
                refine ⟨210896866917230055651399365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140597911278153370434266243 210896866917230055651399365)
                ·
                  refine ⟨39543162546980635434637381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210896866917230055651399365 39543162546980635434637381)
                  ·
                    refine ⟨7414342977558869143994509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39543162546980635434637381 7414342977558869143994509)
                    ·
                      refine ⟨2780378616584575928997941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7414342977558869143994509 2780378616584575928997941)
                      ·
                        rfl

theorem cell23_5414768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_5414768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414768 prefixEnd_5414768 := by exact prefixLift 5414768
  have htrace : WordTrace (prefixWord ++ tailWord_5414768) baseStart_5414768 baseEnd_5414768 := by
    simpa [prefixWord, tailWord_5414768, baseEnd_5414768] using wordTrace_append hprefix tailTrace_5414768
  have hstable : (prefixWord ++ tailWord_5414768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414768).length < 2 ^ (prefixWord ++ tailWord_5414768).sum := by decide
  have hdescent : baseEnd_5414768 < baseStart_5414768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414805 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 5]
def baseStart_5414805 : Nat := 118140960795 + 5414805 * 2 ^ 59
def prefixEnd_5414805 : Nat := 4983230072969 + 3 ^ 40 * 5414805 * 2
def baseEnd_5414805 : Nat := 308933068374310253803919

theorem tailTrace_5414805 : CollatzResearch.WordTrace tailWord_5414805 prefixEnd_5414805 308933068374310253803919 := by
  unfold tailWord_5414805
  simp only [CollatzResearch.WordTrace]
  refine ⟨197494163148093734914005869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131662775432062489942670579 197494163148093734914005869)
  ·
    refine ⟨74060311180535150592752201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197494163148093734914005869 74060311180535150592752201)
    ·
      refine ⟨55545233385401362944564151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74060311180535150592752201 55545233385401362944564151)
      ·
        refine ⟨83317850078102044416846227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55545233385401362944564151 83317850078102044416846227)
        ·
          refine ⟨124976775117153066625269341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83317850078102044416846227 124976775117153066625269341)
          ·
            refine ⟨46866290668932399984476003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124976775117153066625269341 46866290668932399984476003)
            ·
              refine ⟨70299436003398599976714005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46866290668932399984476003 70299436003398599976714005)
              ·
                refine ⟨3295286062659309373908469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70299436003398599976714005 3295286062659309373908469)
                ·
                  refine ⟨308933068374310253803919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3295286062659309373908469 308933068374310253803919)
                  ·
                    rfl

theorem cell23_5414805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_5414805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414805 prefixEnd_5414805 := by exact prefixLift 5414805
  have htrace : WordTrace (prefixWord ++ tailWord_5414805) baseStart_5414805 baseEnd_5414805 := by
    simpa [prefixWord, tailWord_5414805, baseEnd_5414805] using wordTrace_append hprefix tailTrace_5414805
  have hstable : (prefixWord ++ tailWord_5414805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414805).length < 2 ^ (prefixWord ++ tailWord_5414805).sum := by decide
  have hdescent : baseEnd_5414805 < baseStart_5414805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414865 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 3, 4]
def baseStart_5414865 : Nat := 118140960795 + 5414865 * 2 ^ 59
def prefixEnd_5414865 : Nat := 4983230072969 + 3 ^ 40 * 5414865 * 2
def baseEnd_5414865 : Nat := 926809474736020683161665

theorem tailTrace_5414865 : CollatzResearch.WordTrace tailWord_5414865 prefixEnd_5414865 926809474736020683161665 := by
  unfold tailWord_5414865
  simp only [CollatzResearch.WordTrace]
  refine ⟨197496351527876365161190049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131664234351917576774126699 197496351527876365161190049)
  ·
    refine ⟨148122263645907273870892537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197496351527876365161190049 148122263645907273870892537)
    ·
      refine ⟨111091697734430455403169403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148122263645907273870892537 111091697734430455403169403)
      ·
        refine ⟨166637546601645683104754105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111091697734430455403169403 166637546601645683104754105)
        ·
          refine ⟨124978159951234262328565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166637546601645683104754105 124978159951234262328565579)
          ·
            refine ⟨187467239926851393492848369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124978159951234262328565579 187467239926851393492848369)
            ·
              refine ⟨140600429945138545119636277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187467239926851393492848369 140600429945138545119636277)
              ·
                refine ⟨13181290307356738604965901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140600429945138545119636277 13181290307356738604965901)
                ·
                  refine ⟨4942983865258776976862213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13181290307356738604965901 4942983865258776976862213)
                  ·
                    refine ⟨926809474736020683161665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4942983865258776976862213 926809474736020683161665)
                    ·
                      rfl

theorem cell23_5414865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_5414865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414865 prefixEnd_5414865 := by exact prefixLift 5414865
  have htrace : WordTrace (prefixWord ++ tailWord_5414865) baseStart_5414865 baseEnd_5414865 := by
    simpa [prefixWord, tailWord_5414865, baseEnd_5414865] using wordTrace_append hprefix tailTrace_5414865
  have hstable : (prefixWord ++ tailWord_5414865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414865).length < 2 ^ (prefixWord ++ tailWord_5414865).sum := by decide
  have hdescent : baseEnd_5414865 < baseStart_5414865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414949 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 2, 3, 2]
def baseStart_5414949 : Nat := 118140960795 + 5414949 * 2 ^ 59
def prefixEnd_5414949 : Nat := 4983230072969 + 3 ^ 40 * 5414949 * 2
def baseEnd_5414949 : Nat := 2780471556583039720834609

theorem tailTrace_5414949 : CollatzResearch.WordTrace tailWord_5414949 prefixEnd_5414949 2780471556583039720834609 := by
  unfold tailWord_5414949
  simp only [CollatzResearch.WordTrace]
  refine ⟨197499415259572047507247901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131666276839714698338165267 197499415259572047507247901)
  ·
    refine ⟨74062280722339517815217963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197499415259572047507247901 74062280722339517815217963)
    ·
      refine ⟨111093421083509276722826945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74062280722339517815217963 111093421083509276722826945)
      ·
        refine ⟨83320065812631957542120209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111093421083509276722826945 83320065812631957542120209)
        ·
          refine ⟨62490049359473968156590157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83320065812631957542120209 62490049359473968156590157)
          ·
            refine ⟨23433768509802738058721309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62490049359473968156590157 23433768509802738058721309)
            ·
              refine ⟨8787663191176026772020491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23433768509802738058721309 8787663191176026772020491)
              ·
                refine ⟨13181494786764040158030737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8787663191176026772020491 13181494786764040158030737)
                ·
                  refine ⟨9886121090073030118523053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13181494786764040158030737 9886121090073030118523053)
                  ·
                    refine ⟨3707295408777386294446145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9886121090073030118523053 3707295408777386294446145)
                    ·
                      refine ⟨2780471556583039720834609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707295408777386294446145 2780471556583039720834609)
                      ·
                        rfl

theorem cell23_5414949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_5414949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414949 prefixEnd_5414949 := by exact prefixLift 5414949
  have htrace : WordTrace (prefixWord ++ tailWord_5414949) baseStart_5414949 baseEnd_5414949 := by
    simpa [prefixWord, tailWord_5414949, baseEnd_5414949] using wordTrace_append hprefix tailTrace_5414949
  have hstable : (prefixWord ++ tailWord_5414949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414949).length < 2 ^ (prefixWord ++ tailWord_5414949).sum := by decide
  have hdescent : baseEnd_5414949 < baseStart_5414949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414972 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_5414972 : Nat := 118140960795 + 5414972 * 2 ^ 59
def prefixEnd_5414972 : Nat := 4983230072969 + 3 ^ 40 * 5414972 * 2
def baseEnd_5414972 : Nat := 926827788879364376949001

theorem tailTrace_5414972 : CollatzResearch.WordTrace tailWord_5414972 prefixEnd_5414972 926827788879364376949001 := by
  unfold tailWord_5414972
  simp only [CollatzResearch.WordTrace]
  refine ⟨98750127069244361217667585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131666836092325814956890113 98750127069244361217667585)
  ·
    refine ⟨74062595301933270913250689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98750127069244361217667585 74062595301933270913250689)
    ·
      refine ⟨55546946476449953184938017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74062595301933270913250689 55546946476449953184938017)
      ·
        refine ⟨41660209857337464888703513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55546946476449953184938017 41660209857337464888703513)
        ·
          refine ⟨31245157393003098666527635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41660209857337464888703513 31245157393003098666527635)
          ·
            refine ⟨46867736089504647999791453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31245157393003098666527635 46867736089504647999791453)
            ·
              refine ⟨17575401033564242999921795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46867736089504647999791453 17575401033564242999921795)
              ·
                refine ⟨26363101550346364499882693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17575401033564242999921795 26363101550346364499882693)
                ·
                  refine ⟨4943081540689943343728005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26363101550346364499882693 4943081540689943343728005)
                  ·
                    refine ⟨926827788879364376949001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943081540689943343728005 926827788879364376949001)
                    ·
                      rfl

theorem cell23_5414972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_5414972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414972 prefixEnd_5414972 := by exact prefixLift 5414972
  have htrace : WordTrace (prefixWord ++ tailWord_5414972) baseStart_5414972 baseEnd_5414972 := by
    simpa [prefixWord, tailWord_5414972, baseEnd_5414972] using wordTrace_append hprefix tailTrace_5414972
  have hstable : (prefixWord ++ tailWord_5414972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414972).length < 2 ^ (prefixWord ++ tailWord_5414972).sum := by decide
  have hdescent : baseEnd_5414972 < baseStart_5414972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5414975 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_5414975 : Nat := 118140960795 + 5414975 * 2 ^ 59
def prefixEnd_5414975 : Nat := 4983230072969 + 3 ^ 40 * 5414975 * 2
def baseEnd_5414975 : Nat := 2780484907080056619109489

theorem tailTrace_5414975 : CollatzResearch.WordTrace tailWord_5414975 prefixEnd_5414975 2780484907080056619109489 := by
  unfold tailWord_5414975
  simp only [CollatzResearch.WordTrace]
  refine ⟨197500363557477853947694379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131666909038318569298462919 197500363557477853947694379)
  ·
    refine ⟨296250545336216780921541569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197500363557477853947694379 296250545336216780921541569)
    ·
      refine ⟨222187909002162585691156177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296250545336216780921541569 222187909002162585691156177)
      ·
        refine ⟨166640931751621939268367133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222187909002162585691156177 166640931751621939268367133)
        ·
          refine ⟨62490349406858227225637675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166640931751621939268367133 62490349406858227225637675)
          ·
            refine ⟨93735524110287340838456513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62490349406858227225637675 93735524110287340838456513)
            ·
              refine ⟨70301643082715505628842385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93735524110287340838456513 70301643082715505628842385)
              ·
                refine ⟨52726232312036629221631789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70301643082715505628842385 52726232312036629221631789)
                ·
                  refine ⟨19772337117013735958111921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52726232312036629221631789 19772337117013735958111921)
                  ·
                    refine ⟨14829252837760301968583941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19772337117013735958111921 14829252837760301968583941)
                    ·
                      refine ⟨2780484907080056619109489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14829252837760301968583941 2780484907080056619109489)
                      ·
                        rfl

theorem cell23_5414975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_5414975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5414975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5414975 prefixEnd_5414975 := by exact prefixLift 5414975
  have htrace : WordTrace (prefixWord ++ tailWord_5414975) baseStart_5414975 baseEnd_5414975 := by
    simpa [prefixWord, tailWord_5414975, baseEnd_5414975] using wordTrace_append hprefix tailTrace_5414975
  have hstable : (prefixWord ++ tailWord_5414975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5414975).length < 2 ^ (prefixWord ++ tailWord_5414975).sum := by decide
  have hdescent : baseEnd_5414975 < baseStart_5414975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5414975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415012 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_5415012 : Nat := 118140960795 + 5415012 * 2 ^ 59
def prefixEnd_5415012 : Nat := 4983230072969 + 3 ^ 40 * 5415012 * 2
def baseEnd_5415012 : Nat := 2780503905864272974346819

theorem tailTrace_5415012 : CollatzResearch.WordTrace tailWord_5415012 prefixEnd_5415012 2780503905864272974346819 := by
  unfold tailWord_5415012
  simp only [CollatzResearch.WordTrace]
  refine ⟨98750856529171904633395645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131667808705562539511194193 98750856529171904633395645)
  ·
    refine ⟨37031571198439464237523367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98750856529171904633395645 37031571198439464237523367)
    ·
      refine ⟨55547356797659196356285051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37031571198439464237523367 55547356797659196356285051)
      ·
        refine ⟨83321035196488794534427577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55547356797659196356285051 83321035196488794534427577)
        ·
          refine ⟨62490776397366595900820683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83321035196488794534427577 62490776397366595900820683)
          ·
            refine ⟨93736164596049893851231025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62490776397366595900820683 93736164596049893851231025)
            ·
              refine ⟨70302123447037420388423269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93736164596049893851231025 70302123447037420388423269)
              ·
                refine ⟨13181648146319516322829363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70302123447037420388423269 13181648146319516322829363)
                ·
                  refine ⟨19772472219479274484244045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13181648146319516322829363 19772472219479274484244045)
                  ·
                    refine ⟨7414677082304727931591517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19772472219479274484244045 7414677082304727931591517)
                    ·
                      refine ⟨2780503905864272974346819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7414677082304727931591517 2780503905864272974346819)
                      ·
                        rfl

theorem cell23_5415012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_5415012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415012 prefixEnd_5415012 := by exact prefixLift 5415012
  have htrace : WordTrace (prefixWord ++ tailWord_5415012) baseStart_5415012 baseEnd_5415012 := by
    simpa [prefixWord, tailWord_5415012, baseEnd_5415012] using wordTrace_append hprefix tailTrace_5415012
  have hstable : (prefixWord ++ tailWord_5415012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415012).length < 2 ^ (prefixWord ++ tailWord_5415012).sum := by decide
  have hdescent : baseEnd_5415012 < baseStart_5415012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415013 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 1, 2, 2]
def baseStart_5415013 : Nat := 118140960795 + 5415013 * 2 ^ 59
def prefixEnd_5415013 : Nat := 4983230072969 + 3 ^ 40 * 5415013 * 2
def baseEnd_5415013 : Nat := 2780504419344927470434315

theorem tailTrace_5415013 : CollatzResearch.WordTrace tailWord_5415013 prefixEnd_5415013 2780504419344927470434315 := by
  unfold tailWord_5415013
  simp only [CollatzResearch.WordTrace]
  refine ⟨197501749531340186437577693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131667833020893457625051795 197501749531340186437577693)
  ·
    refine ⟨74063156074252569914091635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197501749531340186437577693 74063156074252569914091635)
    ·
      refine ⟨111094734111378854871137453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74063156074252569914091635 111094734111378854871137453)
      ·
        refine ⟨41660525291767070576676545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111094734111378854871137453 41660525291767070576676545)
        ·
          refine ⟨31245393968825302932507409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41660525291767070576676545 31245393968825302932507409)
          ·
            refine ⟨23434045476618977199380557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31245393968825302932507409 23434045476618977199380557)
            ·
              refine ⟨8787767053732116449767709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23434045476618977199380557 8787767053732116449767709)
              ·
                refine ⟨3295412645149543668662891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8787767053732116449767709 3295412645149543668662891)
                ·
                  refine ⟨4943118967724315502994337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295412645149543668662891 4943118967724315502994337)
                  ·
                    refine ⟨3707339225793236627245753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4943118967724315502994337 3707339225793236627245753)
                    ·
                      refine ⟨2780504419344927470434315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707339225793236627245753 2780504419344927470434315)
                      ·
                        rfl

theorem cell23_5415013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_5415013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415013 prefixEnd_5415013 := by exact prefixLift 5415013
  have htrace : WordTrace (prefixWord ++ tailWord_5415013) baseStart_5415013 baseEnd_5415013 := by
    simpa [prefixWord, tailWord_5415013, baseEnd_5415013] using wordTrace_append hprefix tailTrace_5415013
  have hstable : (prefixWord ++ tailWord_5415013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415013).length < 2 ^ (prefixWord ++ tailWord_5415013).sum := by decide
  have hdescent : baseEnd_5415013 < baseStart_5415013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415025 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_5415025 : Nat := 118140960795 + 5415025 * 2 ^ 59
def prefixEnd_5415025 : Nat := 4983230072969 + 3 ^ 40 * 5415025 * 2
def baseEnd_5415025 : Nat := 2780510581112781423484259

theorem tailTrace_5415025 : CollatzResearch.WordTrace tailWord_5415025 prefixEnd_5415025 2780510581112781423484259 := by
  unfold tailWord_5415025
  simp only [CollatzResearch.WordTrace]
  refine ⟨197502187207296712487014529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131668124804864474991343019 197502187207296712487014529)
  ·
    refine ⟨148126640405472534365260897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197502187207296712487014529 148126640405472534365260897)
    ·
      refine ⟨111094980304104400773945673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148126640405472534365260897 111094980304104400773945673)
      ·
        refine ⟨83321235228078300580459255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111094980304104400773945673 83321235228078300580459255)
        ·
          refine ⟨124981852842117450870688883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83321235228078300580459255 124981852842117450870688883)
          ·
            refine ⟨187472779263176176306033325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124981852842117450870688883 187472779263176176306033325)
            ·
              refine ⟨70302292223691066114762497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187472779263176176306033325 70302292223691066114762497)
              ·
                refine ⟨52726719167768299586071873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70302292223691066114762497 52726719167768299586071873)
                ·
                  refine ⟨39545039375826224689553905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52726719167768299586071873 39545039375826224689553905)
                  ·
                    refine ⟨29658779531869668517165429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39545039375826224689553905 29658779531869668517165429)
                    ·
                      refine ⟨2780510581112781423484259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29658779531869668517165429 2780510581112781423484259)
                      ·
                        rfl

theorem cell23_5415025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_5415025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415025 prefixEnd_5415025 := by exact prefixLift 5415025
  have htrace : WordTrace (prefixWord ++ tailWord_5415025) baseStart_5415025 baseEnd_5415025 := by
    simpa [prefixWord, tailWord_5415025, baseEnd_5415025] using wordTrace_append hprefix tailTrace_5415025
  have hstable : (prefixWord ++ tailWord_5415025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415025).length < 2 ^ (prefixWord ++ tailWord_5415025).sum := by decide
  have hdescent : baseEnd_5415025 < baseStart_5415025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415069 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_5415069 : Nat := 118140960795 + 5415069 * 2 ^ 59
def prefixEnd_5415069 : Nat := 4983230072969 + 3 ^ 40 * 5415069 * 2
def baseEnd_5415069 : Nat := 2780533174261579251334057

theorem tailTrace_5415069 : CollatzResearch.WordTrace tailWord_5415069 prefixEnd_5415069 2780533174261579251334057 := by
  unfold tailWord_5415069
  simp only [CollatzResearch.WordTrace]
  refine ⟨197503792019137308001616261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131669194679424872001077507 197503792019137308001616261)
  ·
    refine ⟨37031961003588245250303049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197503792019137308001616261 37031961003588245250303049)
    ·
      refine ⟨27773970752691183937727287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37031961003588245250303049 27773970752691183937727287)
      ·
        refine ⟨41660956129036775906590931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27773970752691183937727287 41660956129036775906590931)
        ·
          refine ⟨62491434193555163859886397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41660956129036775906590931 62491434193555163859886397)
          ·
            refine ⟨23434287822583186447457399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62491434193555163859886397 23434287822583186447457399)
            ·
              refine ⟨35151431733874779671186099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23434287822583186447457399 35151431733874779671186099)
              ·
                refine ⟨52727147600812169506779149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35151431733874779671186099 52727147600812169506779149)
                ·
                  refine ⟨19772680350304563565042181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52727147600812169506779149 19772680350304563565042181)
                  ·
                    refine ⟨3707377565682105668445409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19772680350304563565042181 3707377565682105668445409)
                    ·
                      refine ⟨2780533174261579251334057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707377565682105668445409 2780533174261579251334057)
                      ·
                        rfl

theorem cell23_5415069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_5415069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415069 prefixEnd_5415069 := by exact prefixLift 5415069
  have htrace : WordTrace (prefixWord ++ tailWord_5415069) baseStart_5415069 baseEnd_5415069 := by
    simpa [prefixWord, tailWord_5415069, baseEnd_5415069] using wordTrace_append hprefix tailTrace_5415069
  have hstable : (prefixWord ++ tailWord_5415069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415069).length < 2 ^ (prefixWord ++ tailWord_5415069).sum := by decide
  have hdescent : baseEnd_5415069 < baseStart_5415069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415072 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5415072 : Nat := 118140960795 + 5415072 * 2 ^ 59
def prefixEnd_5415072 : Nat := 4983230072969 + 3 ^ 40 * 5415072 * 2
def baseEnd_5415072 : Nat := 2780534714703542739596543

theorem tailTrace_5415072 : CollatzResearch.WordTrace tailWord_5415072 prefixEnd_5415072 2780534714703542739596543 := by
  unfold tailWord_5415072
  simp only [CollatzResearch.WordTrace]
  refine ⟨98751950719063219756987735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131669267625417626342650313 98751950719063219756987735)
  ·
    refine ⟨148127926078594829635481603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98751950719063219756987735 148127926078594829635481603)
    ·
      refine ⟨222191889117892244453222405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148127926078594829635481603 222191889117892244453222405)
      ·
        refine ⟨41660979209604795834979201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222191889117892244453222405 41660979209604795834979201)
        ·
          refine ⟨31245734407203596876234401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41660979209604795834979201 31245734407203596876234401)
          ·
            refine ⟨23434300805402697657175801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31245734407203596876234401 23434300805402697657175801)
            ·
              refine ⟨17575725604052023242881851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23434300805402697657175801 17575725604052023242881851)
              ·
                refine ⟨26363588406078034864322777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17575725604052023242881851 26363588406078034864322777)
                ·
                  refine ⟨19772691304558526148242083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26363588406078034864322777 19772691304558526148242083)
                  ·
                    refine ⟨29659036956837789222363125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19772691304558526148242083 29659036956837789222363125)
                    ·
                      refine ⟨2780534714703542739596543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29659036956837789222363125 2780534714703542739596543)
                      ·
                        rfl

theorem cell23_5415072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5415072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415072 prefixEnd_5415072 := by exact prefixLift 5415072
  have htrace : WordTrace (prefixWord ++ tailWord_5415072) baseStart_5415072 baseEnd_5415072 := by
    simpa [prefixWord, tailWord_5415072, baseEnd_5415072] using wordTrace_append hprefix tailTrace_5415072
  have hstable : (prefixWord ++ tailWord_5415072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415072).length < 2 ^ (prefixWord ++ tailWord_5415072).sum := by decide
  have hdescent : baseEnd_5415072 < baseStart_5415072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415073 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_5415073 : Nat := 118140960795 + 5415073 * 2 ^ 59
def prefixEnd_5415073 : Nat := 4983230072969 + 3 ^ 40 * 5415073 * 2
def baseEnd_5415073 : Nat := 2780535228184197235684039

theorem tailTrace_5415073 : CollatzResearch.WordTrace tailWord_5415073 prefixEnd_5415073 2780535228184197235684039 := by
  unfold tailWord_5415073
  simp only [CollatzResearch.WordTrace]
  refine ⟨197503937911122816684761873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131669291940748544456507915 197503937911122816684761873)
  ·
    refine ⟨148127953433342112513571405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197503937911122816684761873 148127953433342112513571405)
    ·
      refine ⟨55547982537503292192589277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148127953433342112513571405 55547982537503292192589277)
      ·
        refine ⟨20830493451563734572220979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55547982537503292192589277 20830493451563734572220979)
        ·
          refine ⟨31245740177345601858331469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20830493451563734572220979 31245740177345601858331469)
          ·
            refine ⟨11717152566504600696874301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31245740177345601858331469 11717152566504600696874301)
            ·
              refine ⟨4393932212439225261327863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11717152566504600696874301 4393932212439225261327863)
              ·
                refine ⟨6590898318658837891991795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393932212439225261327863 6590898318658837891991795)
                ·
                  refine ⟨9886347477988256837987693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590898318658837891991795 9886347477988256837987693)
                  ·
                    refine ⟨3707380304245596314245385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9886347477988256837987693 3707380304245596314245385)
                    ·
                      refine ⟨2780535228184197235684039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707380304245596314245385 2780535228184197235684039)
                      ·
                        rfl

theorem cell23_5415073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_5415073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415073 prefixEnd_5415073 := by exact prefixLift 5415073
  have htrace : WordTrace (prefixWord ++ tailWord_5415073) baseStart_5415073 baseEnd_5415073 := by
    simpa [prefixWord, tailWord_5415073, baseEnd_5415073] using wordTrace_append hprefix tailTrace_5415073
  have hstable : (prefixWord ++ tailWord_5415073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415073).length < 2 ^ (prefixWord ++ tailWord_5415073).sum := by decide
  have hdescent : baseEnd_5415073 < baseStart_5415073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415169 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5415169 : Nat := 118140960795 + 5415169 * 2 ^ 59
def prefixEnd_5415169 : Nat := 4983230072969 + 3 ^ 40 * 5415169 * 2
def baseEnd_5415169 : Nat := 926861507442342953361199

theorem tailTrace_5415169 : CollatzResearch.WordTrace tailWord_5415169 prefixEnd_5415169 926861507442342953361199 := by
  unfold tailWord_5415169
  simp only [CollatzResearch.WordTrace]
  refine ⟨197507439318775025080256561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131671626212516683386837707 197507439318775025080256561)
  ·
    refine ⟨148130579489081268810192421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197507439318775025080256561 148130579489081268810192421)
    ·
      refine ⟨27774483654202737901911079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148130579489081268810192421 27774483654202737901911079)
      ·
        refine ⟨41661725481304106852866619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27774483654202737901911079 41661725481304106852866619)
        ·
          refine ⟨62492588221956160279299929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41661725481304106852866619 62492588221956160279299929)
          ·
            refine ⟨46869441166467120209474947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62492588221956160279299929 46869441166467120209474947)
            ·
              refine ⟨70304161749700680314212421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46869441166467120209474947 70304161749700680314212421)
              ·
                refine ⟨13182030328068877558914829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70304161749700680314212421 13182030328068877558914829)
                ·
                  refine ⟨4943261373025829084593061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13182030328068877558914829 4943261373025829084593061)
                  ·
                    refine ⟨926861507442342953361199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943261373025829084593061 926861507442342953361199)
                    ·
                      rfl

theorem cell23_5415169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5415169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415169 prefixEnd_5415169 := by exact prefixLift 5415169
  have htrace : WordTrace (prefixWord ++ tailWord_5415169) baseStart_5415169 baseEnd_5415169 := by
    simpa [prefixWord, tailWord_5415169, baseEnd_5415169] using wordTrace_append hprefix tailTrace_5415169
  have hstable : (prefixWord ++ tailWord_5415169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415169).length < 2 ^ (prefixWord ++ tailWord_5415169).sum := by decide
  have hdescent : baseEnd_5415169 < baseStart_5415169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415179 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 3]
def baseStart_5415179 : Nat := 118140960795 + 5415179 * 2 ^ 59
def prefixEnd_5415179 : Nat := 4983230072969 + 3 ^ 40 * 5415179 * 2
def baseEnd_5415179 : Nat := 2780589657133573820958551

theorem tailTrace_5415179 : CollatzResearch.WordTrace tailWord_5415179 prefixEnd_5415179 2780589657133573820958551 := by
  unfold tailWord_5415179
  simp only [CollatzResearch.WordTrace]
  refine ⟨197507804048738796788120591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131671869365825864525413727 197507804048738796788120591)
  ·
    refine ⟨296261706073108195182180887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197507804048738796788120591 296261706073108195182180887)
    ·
      refine ⟨444392559109662292773271331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296261706073108195182180887 444392559109662292773271331)
      ·
        refine ⟨666588838664493439159906997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444392559109662292773271331 666588838664493439159906997)
        ·
          refine ⟨62492703624796259921241281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 666588838664493439159906997 62492703624796259921241281)
          ·
            refine ⟨46869527718597194940930961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62492703624796259921241281 46869527718597194940930961)
            ·
              refine ⟨35152145788947896205698221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46869527718597194940930961 35152145788947896205698221)
              ·
                refine ⟨13182054670855461077136833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35152145788947896205698221 13182054670855461077136833)
                ·
                  refine ⟨9886541003141595807852625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13182054670855461077136833 9886541003141595807852625)
                  ·
                    refine ⟨7414905752356196855889469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9886541003141595807852625 7414905752356196855889469)
                    ·
                      refine ⟨2780589657133573820958551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7414905752356196855889469 2780589657133573820958551)
                      ·
                        rfl

theorem cell23_5415179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 3].length) (baseStart_5415179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415179 prefixEnd_5415179 := by exact prefixLift 5415179
  have htrace : WordTrace (prefixWord ++ tailWord_5415179) baseStart_5415179 baseEnd_5415179 := by
    simpa [prefixWord, tailWord_5415179, baseEnd_5415179] using wordTrace_append hprefix tailTrace_5415179
  have hstable : (prefixWord ++ tailWord_5415179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415179).length < 2 ^ (prefixWord ++ tailWord_5415179).sum := by decide
  have hdescent : baseEnd_5415179 < baseStart_5415179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415182 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_5415182 : Nat := 118140960795 + 5415182 * 2 ^ 59
def prefixEnd_5415182 : Nat := 4983230072969 + 3 ^ 40 * 5415182 * 2
def baseEnd_5415182 : Nat := 308954577508393034357893

theorem tailTrace_5415182 : CollatzResearch.WordTrace tailWord_5415182 prefixEnd_5415182 308954577508393034357893 := by
  unfold tailWord_5415182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24688489183465991037559975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131671942311818618866986533 24688489183465991037559975)
  ·
    refine ⟨37032733775198986556339963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24688489183465991037559975 37032733775198986556339963)
    ·
      refine ⟨55549100662798479834509945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37032733775198986556339963 55549100662798479834509945)
      ·
        refine ⟨41661825497098859875882459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55549100662798479834509945 41661825497098859875882459)
        ·
          refine ⟨62492738245648289813823689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41661825497098859875882459 62492738245648289813823689)
          ·
            refine ⟨46869553684236217360367767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62492738245648289813823689 46869553684236217360367767)
            ·
              refine ⟨70304330526354326040551651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46869553684236217360367767 70304330526354326040551651)
              ·
                refine ⟨105456495789531489060827477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70304330526354326040551651 105456495789531489060827477)
                ·
                  refine ⟨308954577508393034357893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105456495789531489060827477 308954577508393034357893)
                  ·
                    rfl

theorem cell23_5415182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_5415182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415182 prefixEnd_5415182 := by exact prefixLift 5415182
  have htrace : WordTrace (prefixWord ++ tailWord_5415182) baseStart_5415182 baseEnd_5415182 := by
    simpa [prefixWord, tailWord_5415182, baseEnd_5415182] using wordTrace_append hprefix tailTrace_5415182
  have hstable : (prefixWord ++ tailWord_5415182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415182).length < 2 ^ (prefixWord ++ tailWord_5415182).sum := by decide
  have hdescent : baseEnd_5415182 < baseStart_5415182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415203 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 1, 4]
def baseStart_5415203 : Nat := 118140960795 + 5415203 * 2 ^ 59
def prefixEnd_5415203 : Nat := 4983230072969 + 3 ^ 40 * 5415203 * 2
def baseEnd_5415203 : Nat := 926867326889760575686147

theorem tailTrace_5415203 : CollatzResearch.WordTrace tailWord_5415203 prefixEnd_5415203 926867326889760575686147 := by
  unfold tailWord_5415203
  simp only [CollatzResearch.WordTrace]
  refine ⟨197508679400651848886994263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131672452933767899257996175 197508679400651848886994263)
  ·
    refine ⟨296263019100977773330491395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197508679400651848886994263 296263019100977773330491395)
    ·
      refine ⟨444394528651466659995737093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296263019100977773330491395 444394528651466659995737093)
      ·
        refine ⟨83323974122149998749200705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 444394528651466659995737093 83323974122149998749200705)
        ·
          refine ⟨62492980591612499061900529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83323974122149998749200705 62492980591612499061900529)
          ·
            refine ⟨46869735443709374296425397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62492980591612499061900529 46869735443709374296425397)
            ·
              refine ⟨4394037697847753840289881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46869735443709374296425397 4394037697847753840289881)
              ·
                refine ⟨3295528273385815380217411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394037697847753840289881 3295528273385815380217411)
                ·
                  refine ⟨4943292410078723070326117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295528273385815380217411 4943292410078723070326117)
                  ·
                    refine ⟨926867326889760575686147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943292410078723070326117 926867326889760575686147)
                    ·
                      rfl

theorem cell23_5415203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 4].length) (baseStart_5415203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415203 prefixEnd_5415203 := by exact prefixLift 5415203
  have htrace : WordTrace (prefixWord ++ tailWord_5415203) baseStart_5415203 baseEnd_5415203 := by
    simpa [prefixWord, tailWord_5415203, baseEnd_5415203] using wordTrace_append hprefix tailTrace_5415203
  have hstable : (prefixWord ++ tailWord_5415203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415203).length < 2 ^ (prefixWord ++ tailWord_5415203).sum := by decide
  have hdescent : baseEnd_5415203 < baseStart_5415203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415266 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5415266 : Nat := 118140960795 + 5415266 * 2 ^ 59
def prefixEnd_5415266 : Nat := 4983230072969 + 3 ^ 40 * 5415266 * 2
def baseEnd_5415266 : Nat := 2780634329950514980570651

theorem tailTrace_5415266 : CollatzResearch.WordTrace tailWord_5415266 prefixEnd_5415266 2780634329950514980570651 := by
  unfold tailWord_5415266
  simp only [CollatzResearch.WordTrace]
  refine ⟨49377744299855902661634413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131673984799615740431025101 49377744299855902661634413)
  ·
    refine ⟨18516654112445963498112905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49377744299855902661634413 18516654112445963498112905)
    ·
      refine ⟨13887490584334472623584679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18516654112445963498112905 13887490584334472623584679)
      ·
        refine ⟨20831235876501708935377019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13887490584334472623584679 20831235876501708935377019)
        ·
          refine ⟨31246853814752563403065529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20831235876501708935377019 31246853814752563403065529)
          ·
            refine ⟨23435140361064422552299147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31246853814752563403065529 23435140361064422552299147)
            ·
              refine ⟨35152710541596633828448721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23435140361064422552299147 35152710541596633828448721)
              ·
                refine ⟨26364532906197475371336541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35152710541596633828448721 26364532906197475371336541)
                ·
                  refine ⟨9886699839824053264251203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26364532906197475371336541 9886699839824053264251203)
                  ·
                    refine ⟨14830049759736079896376805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9886699839824053264251203 14830049759736079896376805)
                    ·
                      refine ⟨2780634329950514980570651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14830049759736079896376805 2780634329950514980570651)
                      ·
                        rfl

theorem cell23_5415266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5415266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415266 prefixEnd_5415266 := by exact prefixLift 5415266
  have htrace : WordTrace (prefixWord ++ tailWord_5415266) baseStart_5415266 baseEnd_5415266 := by
    simpa [prefixWord, tailWord_5415266, baseEnd_5415266] using wordTrace_append hprefix tailTrace_5415266
  have hstable : (prefixWord ++ tailWord_5415266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415266).length < 2 ^ (prefixWord ++ tailWord_5415266).sum := by decide
  have hdescent : baseEnd_5415266 < baseStart_5415266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415276 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_5415276 : Nat := 118140960795 + 5415276 * 2 ^ 59
def prefixEnd_5415276 : Nat := 4983230072969 + 3 ^ 40 * 5415276 * 2
def baseEnd_5415276 : Nat := 926879821585686647148535

theorem tailTrace_5415276 : CollatzResearch.WordTrace tailWord_5415276 prefixEnd_5415276 926879821585686647148535 := by
  unfold tailWord_5415276
  simp only [CollatzResearch.WordTrace]
  refine ⟨98755670964693691177200841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131674227952924921569601121 98755670964693691177200841)
  ·
    refine ⟨74066753223520268382900631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98755670964693691177200841 74066753223520268382900631)
    ·
      refine ⟨111100129835280402574350947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74066753223520268382900631 111100129835280402574350947)
      ·
        refine ⟨166650194752920603861526421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111100129835280402574350947 166650194752920603861526421)
        ·
          refine ⟨7811727879043153306009051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166650194752920603861526421 7811727879043153306009051)
          ·
            refine ⟨11717591818564729959013577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7811727879043153306009051 11717591818564729959013577)
            ·
              refine ⟨8788193863923547469260183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11717591818564729959013577 8788193863923547469260183)
              ·
                refine ⟨13182290795885321203890275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8788193863923547469260183 13182290795885321203890275)
                ·
                  refine ⟨19773436193827981805835413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13182290795885321203890275 19773436193827981805835413)
                  ·
                    refine ⟨926879821585686647148535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19773436193827981805835413 926879821585686647148535)
                    ·
                      rfl

theorem cell23_5415276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_5415276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415276 prefixEnd_5415276 := by exact prefixLift 5415276
  have htrace : WordTrace (prefixWord ++ tailWord_5415276) baseStart_5415276 baseEnd_5415276 := by
    simpa [prefixWord, tailWord_5415276, baseEnd_5415276] using wordTrace_append hprefix tailTrace_5415276
  have hstable : (prefixWord ++ tailWord_5415276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415276).length < 2 ^ (prefixWord ++ tailWord_5415276).sum := by decide
  have hdescent : baseEnd_5415276 < baseStart_5415276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415306 : List Nat := [3, 1, 2, 5, 1, 1, 10]
def baseStart_5415306 : Nat := 118140960795 + 5415306 * 2 ^ 59
def prefixEnd_5415306 : Nat := 4983230072969 + 3 ^ 40 * 5415306 * 2
def baseEnd_5415306 : Nat := 34329072458971541037907

theorem tailTrace_5415306 : CollatzResearch.WordTrace tailWord_5415306 prefixEnd_5415306 34329072458971541037907 := by
  unfold tailWord_5415306
  simp only [CollatzResearch.WordTrace]
  refine ⟨49378109029819674369498443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131674957412852464985329181 49378109029819674369498443)
  ·
    refine ⟨74067163544729511554247665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49378109029819674369498443 74067163544729511554247665)
    ·
      refine ⟨55550372658547133665685749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74067163544729511554247665 55550372658547133665685749)
      ·
        refine ⟨5207847436738793781158039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55550372658547133665685749 5207847436738793781158039)
        ·
          refine ⟨7811771155108190671737059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5207847436738793781158039 7811771155108190671737059)
          ·
            refine ⟨11717656732662286007605589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7811771155108190671737059 11717656732662286007605589)
            ·
              refine ⟨34329072458971541037907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11717656732662286007605589 34329072458971541037907)
              ·
                rfl

theorem cell23_5415306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 10].length) (baseStart_5415306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415306 prefixEnd_5415306 := by exact prefixLift 5415306
  have htrace : WordTrace (prefixWord ++ tailWord_5415306) baseStart_5415306 baseEnd_5415306 := by
    simpa [prefixWord, tailWord_5415306, baseEnd_5415306] using wordTrace_append hprefix tailTrace_5415306
  have hstable : (prefixWord ++ tailWord_5415306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415306).length < 2 ^ (prefixWord ++ tailWord_5415306).sum := by decide
  have hdescent : baseEnd_5415306 < baseStart_5415306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415310 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_5415310 : Nat := 118140960795 + 5415310 * 2 ^ 59
def prefixEnd_5415310 : Nat := 4983230072969 + 3 ^ 40 * 5415310 * 2
def baseEnd_5415310 : Nat := 926885641033104269473483

theorem tailTrace_5415310 : CollatzResearch.WordTrace tailWord_5415310 prefixEnd_5415310 926885641033104269473483 := by
  unfold tailWord_5415310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689072751408025770142423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131675054674176137440759589 24689072751408025770142423)
  ·
    refine ⟨37033609127112038655213635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24689072751408025770142423 37033609127112038655213635)
    ·
      refine ⟨55550413690668057982820453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37033609127112038655213635 55550413690668057982820453)
      ·
        refine ⟨10415702567000260871778835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55550413690668057982820453 10415702567000260871778835)
        ·
          refine ⟨15623553850500391307668253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10415702567000260871778835 15623553850500391307668253)
          ·
            refine ⟨5858832693937646740375595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15623553850500391307668253 5858832693937646740375595)
            ·
              refine ⟨8788249040906470110563393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858832693937646740375595 8788249040906470110563393)
              ·
                refine ⟨6591186780679852582922545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8788249040906470110563393 6591186780679852582922545)
                ·
                  refine ⟨4943390085509889437191909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6591186780679852582922545 4943390085509889437191909)
                  ·
                    refine ⟨926885641033104269473483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943390085509889437191909 926885641033104269473483)
                    ·
                      rfl

theorem cell23_5415310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_5415310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415310 prefixEnd_5415310 := by exact prefixLift 5415310
  have htrace : WordTrace (prefixWord ++ tailWord_5415310) baseStart_5415310 baseEnd_5415310 := by
    simpa [prefixWord, tailWord_5415310, baseEnd_5415310] using wordTrace_append hprefix tailTrace_5415310
  have hstable : (prefixWord ++ tailWord_5415310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415310).length < 2 ^ (prefixWord ++ tailWord_5415310).sum := by decide
  have hdescent : baseEnd_5415310 < baseStart_5415310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415359 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_5415359 : Nat := 118140960795 + 5415359 * 2 ^ 59
def prefixEnd_5415359 : Nat := 4983230072969 + 3 ^ 40 * 5415359 * 2
def baseEnd_5415359 : Nat := 2780682083651383116707723

theorem tailTrace_5415359 : CollatzResearch.WordTrace tailWord_5415359 prefixEnd_5415359 2780682083651383116707723 := by
  unfold tailWord_5415359
  simp only [CollatzResearch.WordTrace]
  refine ⟨197514369188086687529673131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131676246125391125019782087 197514369188086687529673131)
  ·
    refine ⟨296271553782130031294509697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197514369188086687529673131 296271553782130031294509697)
    ·
      refine ⟨222203665336597523470882273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296271553782130031294509697 222203665336597523470882273)
      ·
        refine ⟨166652749002448142603161705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222203665336597523470882273 166652749002448142603161705)
        ·
          refine ⟨124989561751836106952371279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166652749002448142603161705 124989561751836106952371279)
          ·
            refine ⟨187484342627754160428556919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124989561751836106952371279 187484342627754160428556919)
            ·
              refine ⟨281226513941631240642835379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187484342627754160428556919 281226513941631240642835379)
              ·
                refine ⟨421839770912446860964253069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281226513941631240642835379 421839770912446860964253069)
                ·
                  refine ⟨158189914092167572861594901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421839770912446860964253069 158189914092167572861594901)
                  ·
                    refine ⟨7415152223070354977887261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 158189914092167572861594901 7415152223070354977887261)
                    ·
                      refine ⟨2780682083651383116707723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7415152223070354977887261 2780682083651383116707723)
                      ·
                        rfl

theorem cell23_5415359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_5415359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415359 prefixEnd_5415359 := by exact prefixLift 5415359
  have htrace : WordTrace (prefixWord ++ tailWord_5415359) baseStart_5415359 baseEnd_5415359 := by
    simpa [prefixWord, tailWord_5415359, baseEnd_5415359] using wordTrace_append hprefix tailTrace_5415359
  have hstable : (prefixWord ++ tailWord_5415359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415359).length < 2 ^ (prefixWord ++ tailWord_5415359).sum := by decide
  have hdescent : baseEnd_5415359 < baseStart_5415359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415369 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_5415369 : Nat := 118140960795 + 5415369 * 2 ^ 59
def prefixEnd_5415369 : Nat := 4983230072969 + 3 ^ 40 * 5415369 * 2
def baseEnd_5415369 : Nat := 2780687218457928077582677

theorem tailTrace_5415369 : CollatzResearch.WordTrace tailWord_5415369 prefixEnd_5415369 2780687218457928077582677 := by
  unfold tailWord_5415369
  simp only [CollatzResearch.WordTrace]
  refine ⟨197514733918050459237537161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131676489278700306158358107 197514733918050459237537161)
  ·
    refine ⟨148136050438537844428152871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197514733918050459237537161 148136050438537844428152871)
    ·
      refine ⟨222204075657806766642229307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148136050438537844428152871 222204075657806766642229307)
      ·
        refine ⟨333306113486710149963343961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222204075657806766642229307 333306113486710149963343961)
        ·
          refine ⟨249979585115032612472507971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333306113486710149963343961 249979585115032612472507971)
          ·
            refine ⟨374969377672548918708761957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249979585115032612472507971 374969377672548918708761957)
            ·
              refine ⟨70306758313602922257892867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374969377672548918708761957 70306758313602922257892867)
              ·
                refine ⟨105460137470404383386839301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70306758313602922257892867 105460137470404383386839301)
                ·
                  refine ⟨19773775775700821885032369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105460137470404383386839301 19773775775700821885032369)
                  ·
                    refine ⟨14830331831775616413774277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19773775775700821885032369 14830331831775616413774277)
                    ·
                      refine ⟨2780687218457928077582677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14830331831775616413774277 2780687218457928077582677)
                      ·
                        rfl

theorem cell23_5415369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_5415369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415369 prefixEnd_5415369 := by exact prefixLift 5415369
  have htrace : WordTrace (prefixWord ++ tailWord_5415369) baseStart_5415369 baseEnd_5415369 := by
    simpa [prefixWord, tailWord_5415369, baseEnd_5415369] using wordTrace_append hprefix tailTrace_5415369
  have hstable : (prefixWord ++ tailWord_5415369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415369).length < 2 ^ (prefixWord ++ tailWord_5415369).sum := by decide
  have hdescent : baseEnd_5415369 < baseStart_5415369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415436 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_5415436 : Nat := 118140960795 + 5415436 * 2 ^ 59
def prefixEnd_5415436 : Nat := 4983230072969 + 3 ^ 40 * 5415436 * 2
def baseEnd_5415436 : Nat := 2780721621661779315444869

theorem tailTrace_5415436 : CollatzResearch.WordTrace tailWord_5415436 prefixEnd_5415436 2780721621661779315444869 := by
  unfold tailWord_5415436
  simp only [CollatzResearch.WordTrace]
  refine ⟨98758588804403864840113081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131678118405871819786817441 98758588804403864840113081)
  ·
    refine ⟨74068941603302898630084811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98758588804403864840113081 74068941603302898630084811)
    ·
      refine ⟨111103412404954347945127217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74068941603302898630084811 111103412404954347945127217)
      ·
        refine ⟨83327559303715760958845413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111103412404954347945127217 83327559303715760958845413)
        ·
          refine ⟨15623917369446705179783515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83327559303715760958845413 15623917369446705179783515)
          ·
            refine ⟨23435876054170057769675273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15623917369446705179783515 23435876054170057769675273)
            ·
              refine ⟨17576907040627543327256455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23435876054170057769675273 17576907040627543327256455)
              ·
                refine ⟨26365360560941314990884683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17576907040627543327256455 26365360560941314990884683)
                ·
                  refine ⟨39548040841411972486327025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26365360560941314990884683 39548040841411972486327025)
                  ·
                    refine ⟨29661030631058979364745269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39548040841411972486327025 29661030631058979364745269)
                    ·
                      refine ⟨2780721621661779315444869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29661030631058979364745269 2780721621661779315444869)
                      ·
                        rfl

theorem cell23_5415436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_5415436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415436 prefixEnd_5415436 := by exact prefixLift 5415436
  have htrace : WordTrace (prefixWord ++ tailWord_5415436) baseStart_5415436 baseEnd_5415436 := by
    simpa [prefixWord, tailWord_5415436, baseEnd_5415436] using wordTrace_append hprefix tailTrace_5415436
  have hstable : (prefixWord ++ tailWord_5415436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415436).length < 2 ^ (prefixWord ++ tailWord_5415436).sum := by decide
  have hdescent : baseEnd_5415436 < baseStart_5415436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415449 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_5415449 : Nat := 118140960795 + 5415449 * 2 ^ 59
def prefixEnd_5415449 : Nat := 4983230072969 + 3 ^ 40 * 5415449 * 2
def baseEnd_5415449 : Nat := 2780728296910287764582309

theorem tailTrace_5415449 : CollatzResearch.WordTrace tailWord_5415449 prefixEnd_5415449 2780728296910287764582309 := by
  unfold tailWord_5415449
  simp only [CollatzResearch.WordTrace]
  refine ⟨197517651757760632900449401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131678434505173755266966267 197517651757760632900449401)
  ·
    refine ⟨148138238818320474675337051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197517651757760632900449401 148138238818320474675337051)
    ·
      refine ⟨222207358227480712013005577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148138238818320474675337051 222207358227480712013005577)
      ·
        refine ⟨166655518670610534009754183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222207358227480712013005577 166655518670610534009754183)
        ·
          refine ⟨249983278005915801014631275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166655518670610534009754183 249983278005915801014631275)
          ·
            refine ⟨374974917008873701521946913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249983278005915801014631275 374974917008873701521946913)
            ·
              refine ⟨281231187756655276141460185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374974917008873701521946913 281231187756655276141460185)
              ·
                refine ⟨210923390817491457106095139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281231187756655276141460185 210923390817491457106095139)
                ·
                  refine ⟨316385086226237185659142709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210923390817491457106095139 316385086226237185659142709)
                  ·
                    refine ⟨29661101833709736155544629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 316385086226237185659142709 29661101833709736155544629)
                    ·
                      refine ⟨2780728296910287764582309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29661101833709736155544629 2780728296910287764582309)
                      ·
                        rfl

theorem cell23_5415449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_5415449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415449 prefixEnd_5415449 := by exact prefixLift 5415449
  have htrace : WordTrace (prefixWord ++ tailWord_5415449) baseStart_5415449 baseEnd_5415449 := by
    simpa [prefixWord, tailWord_5415449, baseEnd_5415449] using wordTrace_append hprefix tailTrace_5415449
  have hstable : (prefixWord ++ tailWord_5415449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415449).length < 2 ^ (prefixWord ++ tailWord_5415449).sum := by decide
  have hdescent : baseEnd_5415449 < baseStart_5415449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415506 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_5415506 : Nat := 118140960795 + 5415506 * 2 ^ 59
def prefixEnd_5415506 : Nat := 4983230072969 + 3 ^ 40 * 5415506 * 2
def baseEnd_5415506 : Nat := 2780757565307594041569547

theorem tailTrace_5415506 : CollatzResearch.WordTrace tailWord_5415506 prefixEnd_5415506 2780757565307594041569547 := by
  unfold tailWord_5415506
  simp only [CollatzResearch.WordTrace]
  refine ⟨49379932679638532908818593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131679820479036087756849581 49379932679638532908818593)
  ·
    refine ⟨37034949509728899681613945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49379932679638532908818593 37034949509728899681613945)
    ·
      refine ⟨27776212132296674761210459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37034949509728899681613945 27776212132296674761210459)
      ·
        refine ⟨41664318198445012141815689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27776212132296674761210459 41664318198445012141815689)
        ·
          refine ⟨31248238648833759106361767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41664318198445012141815689 31248238648833759106361767)
          ·
            refine ⟨46872357973250638659542651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31248238648833759106361767 46872357973250638659542651)
            ·
              refine ⟨70308536959875957989313977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46872357973250638659542651 70308536959875957989313977)
              ·
                refine ⟨52731402719906968491985483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70308536959875957989313977 52731402719906968491985483)
                ·
                  refine ⟨79097104079860452737978225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52731402719906968491985483 79097104079860452737978225)
                  ·
                    refine ⟨59322828059895339553483669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79097104079860452737978225 59322828059895339553483669)
                    ·
                      refine ⟨2780757565307594041569547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59322828059895339553483669 2780757565307594041569547)
                      ·
                        rfl

theorem cell23_5415506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_5415506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415506 prefixEnd_5415506 := by exact prefixLift 5415506
  have htrace : WordTrace (prefixWord ++ tailWord_5415506) baseStart_5415506 baseEnd_5415506 := by
    simpa [prefixWord, tailWord_5415506, baseEnd_5415506] using wordTrace_append hprefix tailTrace_5415506
  have hstable : (prefixWord ++ tailWord_5415506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415506).length < 2 ^ (prefixWord ++ tailWord_5415506).sum := by decide
  have hdescent : baseEnd_5415506 < baseStart_5415506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415523 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 1, 5, 2]
def baseStart_5415523 : Nat := 118140960795 + 5415523 * 2 ^ 59
def prefixEnd_5415523 : Nat := 4983230072969 + 3 ^ 40 * 5415523 * 2
def baseEnd_5415523 : Nat := 2780766294478720475056969

theorem tailTrace_5415523 : CollatzResearch.WordTrace tailWord_5415523 prefixEnd_5415523 2780766294478720475056969 := by
  unfold tailWord_5415523
  simp only [CollatzResearch.WordTrace]
  refine ⟨197520350759492543538643223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131680233839661695692428815 197520350759492543538643223)
  ·
    refine ⟨296280526139238815307964835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197520350759492543538643223 296280526139238815307964835)
    ·
      refine ⟨444420789208858222961947253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296280526139238815307964835 444420789208858222961947253)
      ·
        refine ⟨41664448988330458402682555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 444420789208858222961947253 41664448988330458402682555)
        ·
          refine ⟨62496673482495687604023833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41664448988330458402682555 62496673482495687604023833)
          ·
            refine ⟨46872505111871765703017875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62496673482495687604023833 46872505111871765703017875)
            ·
              refine ⟨70308757667807648554526813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46872505111871765703017875 70308757667807648554526813)
              ·
                refine ⟨26365784125427868207947555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70308757667807648554526813 26365784125427868207947555)
                ·
                  refine ⟨39548676188141802311921333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26365784125427868207947555 39548676188141802311921333)
                  ·
                    refine ⟨3707688392638293966742625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39548676188141802311921333 3707688392638293966742625)
                    ·
                      refine ⟨2780766294478720475056969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707688392638293966742625 2780766294478720475056969)
                      ·
                        rfl

theorem cell23_5415523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_5415523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415523 prefixEnd_5415523 := by exact prefixLift 5415523
  have htrace : WordTrace (prefixWord ++ tailWord_5415523) baseStart_5415523 baseEnd_5415523 := by
    simpa [prefixWord, tailWord_5415523, baseEnd_5415523] using wordTrace_append hprefix tailTrace_5415523
  have hstable : (prefixWord ++ tailWord_5415523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415523).length < 2 ^ (prefixWord ++ tailWord_5415523).sum := by decide
  have hdescent : baseEnd_5415523 < baseStart_5415523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415553 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5415553 : Nat := 118140960795 + 5415553 * 2 ^ 59
def prefixEnd_5415553 : Nat := 4983230072969 + 3 ^ 40 * 5415553 * 2
def baseEnd_5415553 : Nat := 2780781698898355357681831

theorem tailTrace_5415553 : CollatzResearch.WordTrace tailWord_5415553 prefixEnd_5415553 2780781698898355357681831 := by
  unfold tailWord_5415553
  simp only [CollatzResearch.WordTrace]
  refine ⟨197521444949383858662235313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131680963299589239108156875 197521444949383858662235313)
  ·
    refine ⟨148141083712037893996676485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197521444949383858662235313 148141083712037893996676485)
    ·
      refine ⟨27776453196007105124376841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148141083712037893996676485 27776453196007105124376841)
      ·
        refine ⟨20832339897005328843282631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27776453196007105124376841 20832339897005328843282631)
        ·
          refine ⟨31248509845507993264923947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20832339897005328843282631 31248509845507993264923947)
          ·
            refine ⟨46872764768261989897385921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31248509845507993264923947 46872764768261989897385921)
            ·
              refine ⟨35154573576196492423039441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46872764768261989897385921 35154573576196492423039441)
              ·
                refine ⟨26365930182147369317279581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35154573576196492423039441 26365930182147369317279581)
                ·
                  refine ⟨9887223818305263493979843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26365930182147369317279581 9887223818305263493979843)
                  ·
                    refine ⟨14830835727457895240969765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9887223818305263493979843 14830835727457895240969765)
                    ·
                      refine ⟨2780781698898355357681831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14830835727457895240969765 2780781698898355357681831)
                      ·
                        rfl

theorem cell23_5415553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5415553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415553 prefixEnd_5415553 := by exact prefixLift 5415553
  have htrace : WordTrace (prefixWord ++ tailWord_5415553) baseStart_5415553 baseEnd_5415553 := by
    simpa [prefixWord, tailWord_5415553, baseEnd_5415553] using wordTrace_append hprefix tailTrace_5415553
  have hstable : (prefixWord ++ tailWord_5415553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415553).length < 2 ^ (prefixWord ++ tailWord_5415553).sum := by decide
  have hdescent : baseEnd_5415553 < baseStart_5415553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415554 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_5415554 : Nat := 118140960795 + 5415554 * 2 ^ 59
def prefixEnd_5415554 : Nat := 4983230072969 + 3 ^ 40 * 5415554 * 2
def baseEnd_5415554 : Nat := 308975801375445539307703

theorem tailTrace_5415554 : CollatzResearch.WordTrace tailWord_5415554 prefixEnd_5415554 308975801375445539307703 := by
  unfold tailWord_5415554
  simp only [CollatzResearch.WordTrace]
  refine ⟨49380370355595058958255429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131680987614920157222014477 49380370355595058958255429)
  ·
    refine ⟨9258819441674073554672893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49380370355595058958255429 9258819441674073554672893)
    ·
      refine ⟨3472057290627777583002335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9258819441674073554672893 3472057290627777583002335)
      ·
        refine ⟨5208085935941666374503503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472057290627777583002335 5208085935941666374503503)
        ·
          refine ⟨7812128903912499561755255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208085935941666374503503 7812128903912499561755255)
          ·
            refine ⟨11718193355868749342632883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7812128903912499561755255 11718193355868749342632883)
            ·
              refine ⟨17577290033803124013949325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11718193355868749342632883 17577290033803124013949325)
              ·
                refine ⟨6591483762676171505230997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17577290033803124013949325 6591483762676171505230997)
                ·
                  refine ⟨308975801375445539307703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6591483762676171505230997 308975801375445539307703)
                  ·
                    rfl

theorem cell23_5415554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_5415554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415554 prefixEnd_5415554 := by exact prefixLift 5415554
  have htrace : WordTrace (prefixWord ++ tailWord_5415554) baseStart_5415554 baseEnd_5415554 := by
    simpa [prefixWord, tailWord_5415554, baseEnd_5415554] using wordTrace_append hprefix tailTrace_5415554
  have hstable : (prefixWord ++ tailWord_5415554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415554).length < 2 ^ (prefixWord ++ tailWord_5415554).sum := by decide
  have hdescent : baseEnd_5415554 < baseStart_5415554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415570 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5415570 : Nat := 118140960795 + 5415570 * 2 ^ 59
def prefixEnd_5415570 : Nat := 4983230072969 + 3 ^ 40 * 5415570 * 2
def baseEnd_5415570 : Nat := 2780790428069481791169253

theorem tailTrace_5415570 : CollatzResearch.WordTrace tailWord_5415570 prefixEnd_5415570 2780790428069481791169253 := by
  unfold tailWord_5415570
  simp only [CollatzResearch.WordTrace]
  refine ⟨49380516247580567641401041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131681376660214847043736109 49380516247580567641401041)
  ·
    refine ⟨37035387185685425731050781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49380516247580567641401041 37035387185685425731050781)
    ·
      refine ⟨13888270194632034649144043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37035387185685425731050781 13888270194632034649144043)
      ·
        refine ⟨20832405291948051973716065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13888270194632034649144043 20832405291948051973716065)
        ·
          refine ⟨15624303968961038980287049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20832405291948051973716065 15624303968961038980287049)
          ·
            refine ⟨11718227976720779235215287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15624303968961038980287049 11718227976720779235215287)
            ·
              refine ⟨17577341965081168852822931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11718227976720779235215287 17577341965081168852822931)
              ·
                refine ⟨26366012947621753279234397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17577341965081168852822931 26366012947621753279234397)
                ·
                  refine ⟨9887254855358157479712899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26366012947621753279234397 9887254855358157479712899)
                  ·
                    refine ⟨14830882283037236219569349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9887254855358157479712899 14830882283037236219569349)
                    ·
                      refine ⟨2780790428069481791169253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14830882283037236219569349 2780790428069481791169253)
                      ·
                        rfl

theorem cell23_5415570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5415570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415570 prefixEnd_5415570 := by exact prefixLift 5415570
  have htrace : WordTrace (prefixWord ++ tailWord_5415570) baseStart_5415570 baseEnd_5415570 := by
    simpa [prefixWord, tailWord_5415570, baseEnd_5415570] using wordTrace_append hprefix tailTrace_5415570
  have hstable : (prefixWord ++ tailWord_5415570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415570).length < 2 ^ (prefixWord ++ tailWord_5415570).sum := by decide
  have hdescent : baseEnd_5415570 < baseStart_5415570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415576 : List Nat := [2, 1, 2, 4, 1, 1, 1, 11]
def baseStart_5415576 : Nat := 118140960795 + 5415576 * 2 ^ 59
def prefixEnd_5415576 : Nat := 4983230072969 + 3 ^ 40 * 5415576 * 2
def baseEnd_5415576 : Nat := 102992352183459583988675

theorem tailTrace_5415576 : CollatzResearch.WordTrace tailWord_5415576 prefixEnd_5415576 102992352183459583988675 := by
  unfold tailWord_5415576
  simp only [CollatzResearch.WordTrace]
  refine ⟨98761141914150266795161291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131681522552200355726881721 98761141914150266795161291)
  ·
    refine ⟨148141712871225400192741937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98761141914150266795161291 148141712871225400192741937)
    ·
      refine ⟨111106284653419050144556453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148141712871225400192741937 111106284653419050144556453)
      ·
        refine ⟨20832428372516071902104335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111106284653419050144556453 20832428372516071902104335)
        ·
          refine ⟨31248642558774107853156503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20832428372516071902104335 31248642558774107853156503)
          ·
            refine ⟨46872963838161161779734755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31248642558774107853156503 46872963838161161779734755)
            ·
              refine ⟨70309445757241742669602133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46872963838161161779734755 70309445757241742669602133)
              ·
                refine ⟨102992352183459583988675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 70309445757241742669602133 102992352183459583988675)
                ·
                  rfl

theorem cell23_5415576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 11].length) (baseStart_5415576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415576 prefixEnd_5415576 := by exact prefixLift 5415576
  have htrace : WordTrace (prefixWord ++ tailWord_5415576) baseStart_5415576 baseEnd_5415576 := by
    simpa [prefixWord, tailWord_5415576, baseEnd_5415576] using wordTrace_append hprefix tailTrace_5415576
  have hstable : (prefixWord ++ tailWord_5415576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415576).length < 2 ^ (prefixWord ++ tailWord_5415576).sum := by decide
  have hdescent : baseEnd_5415576 < baseStart_5415576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415597 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_5415597 : Nat := 118140960795 + 5415597 * 2 ^ 59
def prefixEnd_5415597 : Nat := 4983230072969 + 3 ^ 40 * 5415597 * 2
def baseEnd_5415597 : Nat := 926934764015717728510543

theorem tailTrace_5415597 : CollatzResearch.WordTrace tailWord_5415597 prefixEnd_5415597 926934764015717728510543 := by
  unfold tailWord_5415597
  simp only [CollatzResearch.WordTrace]
  refine ⟨197523049761224454176837045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131682033174149636117891363 197523049761224454176837045)
  ·
    refine ⟨18517785915114792579078473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197523049761224454176837045 18517785915114792579078473)
    ·
      refine ⟨13888339436336094434308855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18517785915114792579078473 13888339436336094434308855)
      ·
        refine ⟨20832509154504141651463283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13888339436336094434308855 20832509154504141651463283)
        ·
          refine ⟨31248763731756212477194925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20832509154504141651463283 31248763731756212477194925)
          ·
            refine ⟨11718286399408579678948097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31248763731756212477194925 11718286399408579678948097)
            ·
              refine ⟨8788714799556434759211073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11718286399408579678948097 8788714799556434759211073)
              ·
                refine ⟨6591536099667326069408305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8788714799556434759211073 6591536099667326069408305)
                ·
                  refine ⟨4943652074750494552056229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6591536099667326069408305 4943652074750494552056229)
                  ·
                    refine ⟨926934764015717728510543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943652074750494552056229 926934764015717728510543)
                    ·
                      rfl

theorem cell23_5415597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_5415597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415597 prefixEnd_5415597 := by exact prefixLift 5415597
  have htrace : WordTrace (prefixWord ++ tailWord_5415597) baseStart_5415597 baseEnd_5415597 := by
    simpa [prefixWord, tailWord_5415597, baseEnd_5415597] using wordTrace_append hprefix tailTrace_5415597
  have hstable : (prefixWord ++ tailWord_5415597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415597).length < 2 ^ (prefixWord ++ tailWord_5415597).sum := by decide
  have hdescent : baseEnd_5415597 < baseStart_5415597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415598 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5415598 : Nat := 118140960795 + 5415598 * 2 ^ 59
def prefixEnd_5415598 : Nat := 4983230072969 + 3 ^ 40 * 5415598 * 2
def baseEnd_5415598 : Nat := 2780804805527807681619125

theorem tailTrace_5415598 : CollatzResearch.WordTrace tailWord_5415598 prefixEnd_5415598 2780804805527807681619125 := by
  unfold tailWord_5415598
  simp only [CollatzResearch.WordTrace]
  refine ⟨24690385779277603918452931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131682057489480554231748965 24690385779277603918452931)
  ·
    refine ⟨37035578668916405877679397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24690385779277603918452931 37035578668916405877679397)
    ·
      refine ⟨6944171000421826102064887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37035578668916405877679397 6944171000421826102064887)
      ·
        refine ⟨10416256500632739153097331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6944171000421826102064887 10416256500632739153097331)
        ·
          refine ⟨15624384750949108729645997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10416256500632739153097331 15624384750949108729645997)
          ·
            refine ⟨5859144281605915773617249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15624384750949108729645997 5859144281605915773617249)
            ·
              refine ⟨4394358211204436830212937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859144281605915773617249 4394358211204436830212937)
              ·
                refine ⟨3295768658403327622659703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394358211204436830212937 3295768658403327622659703)
                ·
                  refine ⟨4943652987604991433989555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295768658403327622659703 4943652987604991433989555)
                  ·
                    refine ⟨7415479481407487150984333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4943652987604991433989555 7415479481407487150984333)
                    ·
                      refine ⟨2780804805527807681619125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7415479481407487150984333 2780804805527807681619125)
                      ·
                        rfl

theorem cell23_5415598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5415598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415598 prefixEnd_5415598 := by exact prefixLift 5415598
  have htrace : WordTrace (prefixWord ++ tailWord_5415598) baseStart_5415598 baseEnd_5415598 := by
    simpa [prefixWord, tailWord_5415598, baseEnd_5415598] using wordTrace_append hprefix tailTrace_5415598
  have hstable : (prefixWord ++ tailWord_5415598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415598).length < 2 ^ (prefixWord ++ tailWord_5415598).sum := by decide
  have hdescent : baseEnd_5415598 < baseStart_5415598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415620 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_5415620 : Nat := 118140960795 + 5415620 * 2 ^ 59
def prefixEnd_5415620 : Nat := 4983230072969 + 3 ^ 40 * 5415620 * 2
def baseEnd_5415620 : Nat := 2780816102102206595544023

theorem tailTrace_5415620 : CollatzResearch.WordTrace tailWord_5415620 prefixEnd_5415620 2780816102102206595544023 := by
  unfold tailWord_5415620
  simp only [CollatzResearch.WordTrace]
  refine ⟨98761944320070564552462157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131682592426760752736616209 98761944320070564552462157)
  ·
    refine ⟨37035729120026461707173309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98761944320070564552462157 37035729120026461707173309)
    ·
      refine ⟨13888398420009923140189991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37035729120026461707173309 13888398420009923140189991)
      ·
        refine ⟨20832597630014884710284987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13888398420009923140189991 20832597630014884710284987)
        ·
          refine ⟨31248896445022327065427481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20832597630014884710284987 31248896445022327065427481)
          ·
            refine ⟨23436672333766745299070611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31248896445022327065427481 23436672333766745299070611)
            ·
              refine ⟨35155008500650117948605917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23436672333766745299070611 35155008500650117948605917)
              ·
                refine ⟨13183128187743794230727219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35155008500650117948605917 13183128187743794230727219)
                ·
                  refine ⟨19774692281615691346090829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13183128187743794230727219 19774692281615691346090829)
                  ·
                    refine ⟨7415509605605884254784061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19774692281615691346090829 7415509605605884254784061)
                    ·
                      refine ⟨2780816102102206595544023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7415509605605884254784061 2780816102102206595544023)
                      ·
                        rfl

theorem cell23_5415620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_5415620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415620 prefixEnd_5415620 := by exact prefixLift 5415620
  have htrace : WordTrace (prefixWord ++ tailWord_5415620) baseStart_5415620 baseEnd_5415620 := by
    simpa [prefixWord, tailWord_5415620, baseEnd_5415620] using wordTrace_append hprefix tailTrace_5415620
  have hstable : (prefixWord ++ tailWord_5415620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415620).length < 2 ^ (prefixWord ++ tailWord_5415620).sum := by decide
  have hdescent : baseEnd_5415620 < baseStart_5415620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415647 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 1, 3, 2]
def baseStart_5415647 : Nat := 118140960795 + 5415647 * 2 ^ 59
def prefixEnd_5415647 : Nat := 4983230072969 + 3 ^ 40 * 5415647 * 2
def baseEnd_5415647 : Nat := 2780829966079877989906399

theorem tailTrace_5415647 : CollatzResearch.WordTrace tailWord_5415647 prefixEnd_5415647 2780829966079877989906399 := by
  unfold tailWord_5415647
  simp only [CollatzResearch.WordTrace]
  refine ⟨197524873411043312716157195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131683248940695541810771463 197524873411043312716157195)
  ·
    refine ⟨296287310116564969074235793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197524873411043312716157195 296287310116564969074235793)
    ·
      refine ⟨222215482587423726805676845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296287310116564969074235793 222215482587423726805676845)
      ·
        refine ⟨83330805970283897552128817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222215482587423726805676845 83330805970283897552128817)
        ·
          refine ⟨62498104477712923164096613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83330805970283897552128817 62498104477712923164096613)
          ·
            refine ⟨11718394589571173093268115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62498104477712923164096613 11718394589571173093268115)
            ·
              refine ⟨17577591884356759639902173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11718394589571173093268115 17577591884356759639902173)
              ·
                refine ⟨6591596956633784864963315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17577591884356759639902173 6591596956633784864963315)
                ·
                  refine ⟨9887395434950677297444973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6591596956633784864963315 9887395434950677297444973)
                  ·
                    refine ⟨3707773288106503986541865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9887395434950677297444973 3707773288106503986541865)
                    ·
                      refine ⟨2780829966079877989906399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3707773288106503986541865 2780829966079877989906399)
                      ·
                        rfl

theorem cell23_5415647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_5415647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415647 prefixEnd_5415647 := by exact prefixLift 5415647
  have htrace : WordTrace (prefixWord ++ tailWord_5415647) baseStart_5415647 baseEnd_5415647 := by
    simpa [prefixWord, tailWord_5415647, baseEnd_5415647] using wordTrace_append hprefix tailTrace_5415647
  have hstable : (prefixWord ++ tailWord_5415647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415647).length < 2 ^ (prefixWord ++ tailWord_5415647).sum := by decide
  have hdescent : baseEnd_5415647 < baseStart_5415647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415653 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_5415653 : Nat := 118140960795 + 5415653 * 2 ^ 59
def prefixEnd_5415653 : Nat := 4983230072969 + 3 ^ 40 * 5415653 * 2
def baseEnd_5415653 : Nat := 926944348987934988810457

theorem tailTrace_5415653 : CollatzResearch.WordTrace tailWord_5415653 prefixEnd_5415653 926944348987934988810457 := by
  unfold tailWord_5415653
  simp only [CollatzResearch.WordTrace]
  refine ⟨197525092249021575740875613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131683394832681050493917075 197525092249021575740875613)
  ·
    refine ⟨74071909593383090902828355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197525092249021575740875613 74071909593383090902828355)
    ·
      refine ⟨111107864390074636354242533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74071909593383090902828355 111107864390074636354242533)
      ·
        refine ⟨20832724573138994316420475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111107864390074636354242533 20832724573138994316420475)
        ·
          refine ⟨31249086859708491474630713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20832724573138994316420475 31249086859708491474630713)
          ·
            refine ⟨23436815144781368605973035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31249086859708491474630713 23436815144781368605973035)
            ·
              refine ⟨35155222717172052908959553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23436815144781368605973035 35155222717172052908959553)
              ·
                refine ⟨26366417037879039681719665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35155222717172052908959553 26366417037879039681719665)
                ·
                  refine ⟨19774812778409279761289749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26366417037879039681719665 19774812778409279761289749)
                  ·
                    refine ⟨926944348987934988810457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19774812778409279761289749 926944348987934988810457)
                    ·
                      rfl

theorem cell23_5415653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_5415653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415653 prefixEnd_5415653 := by exact prefixLift 5415653
  have htrace : WordTrace (prefixWord ++ tailWord_5415653) baseStart_5415653 baseEnd_5415653 := by
    simpa [prefixWord, tailWord_5415653, baseEnd_5415653] using wordTrace_append hprefix tailTrace_5415653
  have hstable : (prefixWord ++ tailWord_5415653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415653).length < 2 ^ (prefixWord ++ tailWord_5415653).sum := by decide
  have hdescent : baseEnd_5415653 < baseStart_5415653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415717 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 5]
def baseStart_5415717 : Nat := 118140960795 + 5415717 * 2 ^ 59
def prefixEnd_5415717 : Nat := 4983230072969 + 3 ^ 40 * 5415717 * 2
def baseEnd_5415717 : Nat := 308985101080632524003453

theorem tailTrace_5415717 : CollatzResearch.WordTrace tailWord_5415717 prefixEnd_5415717 308985101080632524003453 := by
  unfold tailWord_5415717
  simp only [CollatzResearch.WordTrace]
  refine ⟨197527426520789714671205405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131684951013859809780803603 197527426520789714671205405)
  ·
    refine ⟨74072784945296143001702027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197527426520789714671205405 74072784945296143001702027)
    ·
      refine ⟨111109177417944214502553041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74072784945296143001702027 111109177417944214502553041)
      ·
        refine ⟨83331883063458160876914781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111109177417944214502553041 83331883063458160876914781)
        ·
          refine ⟨31249456148796810328843043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83331883063458160876914781 31249456148796810328843043)
          ·
            refine ⟨46874184223195215493264565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31249456148796810328843043 46874184223195215493264565)
            ·
              refine ⟨4394454770924551452493553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46874184223195215493264565 4394454770924551452493553)
              ·
                refine ⟨3295841078193413589370165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394454770924551452493553 3295841078193413589370165)
                ·
                  refine ⟨308985101080632524003453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3295841078193413589370165 308985101080632524003453)
                  ·
                    rfl

theorem cell23_5415717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_5415717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415717 prefixEnd_5415717 := by exact prefixLift 5415717
  have htrace : WordTrace (prefixWord ++ tailWord_5415717) baseStart_5415717 baseEnd_5415717 := by
    simpa [prefixWord, tailWord_5415717, baseEnd_5415717] using wordTrace_append hprefix tailTrace_5415717
  have hstable : (prefixWord ++ tailWord_5415717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415717).length < 2 ^ (prefixWord ++ tailWord_5415717).sum := by decide
  have hdescent : baseEnd_5415717 < baseStart_5415717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
