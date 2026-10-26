import V185TrunkScan20Chunk023

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_146402 : List Nat := [3, 3, 3, 1, 1, 1, 4, 4]
def baseStart_146402 : Nat := 118140960795 + 146402 * 2 ^ 59
def prefixEnd_146402 : Nat := 4983230072969 + 3 ^ 40 * 146402 * 2
def baseEnd_146402 : Nat := 22273954008782647467175

theorem tailTrace_146402 : CollatzResearch.WordTrace tailWord_146402 prefixEnd_146402 22273954008782647467175 := by
  unfold tailWord_146402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334929903904508079020365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3559813077078688210720973 1334929903904508079020365)
  ·
    refine ⟨500598713964190529632637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1334929903904508079020365 500598713964190529632637)
    ·
      refine ⟨187724517736571448612239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 500598713964190529632637 187724517736571448612239)
      ·
        refine ⟨281586776604857172918359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187724517736571448612239 281586776604857172918359)
        ·
          refine ⟨422380164907285759377539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281586776604857172918359 422380164907285759377539)
          ·
            refine ⟨633570247360928639066309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422380164907285759377539 633570247360928639066309)
            ·
              refine ⟨118794421380174119824933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 633570247360928639066309 118794421380174119824933)
              ·
                refine ⟨22273954008782647467175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118794421380174119824933 22273954008782647467175)
                ·
                  rfl

theorem cell20_146402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_146402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146402 prefixEnd_146402 := by exact prefixLift 146402
  have htrace : WordTrace (prefixWord ++ tailWord_146402) baseStart_146402 baseEnd_146402 := by
    simpa [prefixWord, tailWord_146402, baseEnd_146402] using wordTrace_append hprefix tailTrace_146402
  have hstable : (prefixWord ++ tailWord_146402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146402).length < 2 ^ (prefixWord ++ tailWord_146402).sum := by decide
  have hdescent : baseEnd_146402 < baseStart_146402 := by decide
  rcases family_descends (prefixWord ++ tailWord_146402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146433 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 2]
def baseStart_146433 : Nat := 118140960795 + 146433 * 2 ^ 59
def prefixEnd_146433 : Nat := 4983230072969 + 3 ^ 40 * 146433 * 2
def baseEnd_146433 : Nat := 66836011271049612368065

theorem tailTrace_146433 : CollatzResearch.WordTrace tailWord_146433 prefixEnd_146433 66836011271049612368065 := by
  unfold tailWord_146433
  simp only [CollatzResearch.WordTrace]
  refine ⟨5340850278505724610459953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3560566852337149740306635 5340850278505724610459953)
  ·
    refine ⟨4005637708879293457844965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5340850278505724610459953 4005637708879293457844965)
    ·
      refine ⟨751057070414867523345931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4005637708879293457844965 751057070414867523345931)
      ·
        refine ⟨1126585605622301285018897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751057070414867523345931 1126585605622301285018897)
        ·
          refine ⟨844939204216725963764173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126585605622301285018897 844939204216725963764173)
          ·
            refine ⟨316852201581272236411565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 844939204216725963764173 316852201581272236411565)
            ·
              refine ⟨118819575592977088654337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316852201581272236411565 118819575592977088654337)
              ·
                refine ⟨89114681694732816490753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118819575592977088654337 89114681694732816490753)
                ·
                  refine ⟨66836011271049612368065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89114681694732816490753 66836011271049612368065)
                  ·
                    rfl

theorem cell20_146433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_146433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146433 prefixEnd_146433 := by exact prefixLift 146433
  have htrace : WordTrace (prefixWord ++ tailWord_146433) baseStart_146433 baseEnd_146433 := by
    simpa [prefixWord, tailWord_146433, baseEnd_146433] using wordTrace_append hprefix tailTrace_146433
  have hstable : (prefixWord ++ tailWord_146433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146433).length < 2 ^ (prefixWord ++ tailWord_146433).sum := by decide
  have hdescent : baseEnd_146433 < baseStart_146433 := by decide
  rcases family_descends (prefixWord ++ tailWord_146433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146444 : List Nat := [2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_146444 : Nat := 118140960795 + 146444 * 2 ^ 59
def prefixEnd_146444 : Nat := 4983230072969 + 3 ^ 40 * 146444 * 2
def baseEnd_146444 : Nat := 22280343990260821000451

theorem tailTrace_146444 : CollatzResearch.WordTrace tailWord_146444 prefixEnd_146444 22280343990260821000451 := by
  unfold tailWord_146444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670625740732936744555193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3560834320977248992740257 2670625740732936744555193)
  ·
    refine ⟨2002969305549702558416395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2670625740732936744555193 2002969305549702558416395)
    ·
      refine ⟨3004453958324553837624593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002969305549702558416395 3004453958324553837624593)
      ·
        refine ⟨2253340468743415378218445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3004453958324553837624593 2253340468743415378218445)
        ·
          refine ⟨845002675778780766831917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2253340468743415378218445 845002675778780766831917)
          ·
            refine ⟨316876003417042787561969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 845002675778780766831917 316876003417042787561969)
            ·
              refine ⟨237657002562782090671477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316876003417042787561969 237657002562782090671477)
              ·
                refine ⟨22280343990260821000451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237657002562782090671477 22280343990260821000451)
                ·
                  rfl

theorem cell20_146444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_146444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146444 prefixEnd_146444 := by exact prefixLift 146444
  have htrace : WordTrace (prefixWord ++ tailWord_146444) baseStart_146444 baseEnd_146444 := by
    simpa [prefixWord, tailWord_146444, baseEnd_146444] using wordTrace_append hprefix tailTrace_146444
  have hstable : (prefixWord ++ tailWord_146444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146444).length < 2 ^ (prefixWord ++ tailWord_146444).sum := by decide
  have hdescent : baseEnd_146444 < baseStart_146444 := by decide
  rcases family_descends (prefixWord ++ tailWord_146444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146458 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_146458 : Nat := 118140960795 + 146458 * 2 ^ 59
def prefixEnd_146458 : Nat := 4983230072969 + 3 ^ 40 * 146458 * 2
def baseEnd_146458 : Nat := 66847421952260636534629

theorem tailTrace_146458 : CollatzResearch.WordTrace tailWord_146458 prefixEnd_146458 66847421952260636534629 := by
  unfold tailWord_146458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335440525853788470030007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3561174735610102586746685 1335440525853788470030007)
  ·
    refine ⟨2003160788780682705045011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335440525853788470030007 2003160788780682705045011)
    ·
      refine ⟨3004741183171024057567517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003160788780682705045011 3004741183171024057567517)
      ·
        refine ⟨1126777943689134021587819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3004741183171024057567517 1126777943689134021587819)
        ·
          refine ⟨1690166915533701032381729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126777943689134021587819 1690166915533701032381729)
          ·
            refine ⟨1267625186650275774286297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1690166915533701032381729 1267625186650275774286297)
            ·
              refine ⟨950718889987706830714723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267625186650275774286297 950718889987706830714723)
              ·
                refine ⟨1426078334981560246072085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950718889987706830714723 1426078334981560246072085)
                ·
                  refine ⟨66847421952260636534629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1426078334981560246072085 66847421952260636534629)
                  ·
                    rfl

theorem cell20_146458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_146458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146458 prefixEnd_146458 := by exact prefixLift 146458
  have htrace : WordTrace (prefixWord ++ tailWord_146458) baseStart_146458 baseEnd_146458 := by
    simpa [prefixWord, tailWord_146458, baseEnd_146458] using wordTrace_append hprefix tailTrace_146458
  have hstable : (prefixWord ++ tailWord_146458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146458).length < 2 ^ (prefixWord ++ tailWord_146458).sum := by decide
  have hdescent : baseEnd_146458 < baseStart_146458 := by decide
  rcases family_descends (prefixWord ++ tailWord_146458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146475 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 2]
def baseStart_146475 : Nat := 118140960795 + 146475 * 2 ^ 59
def prefixEnd_146475 : Nat := 4983230072969 + 3 ^ 40 * 146475 * 2
def baseEnd_146475 : Nat := 66855181215484132967893

theorem tailTrace_146475 : CollatzResearch.WordTrace tailWord_146475 prefixEnd_146475 66855181215484132967893 := by
  unfold tailWord_146475
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342382144353565783488879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3561588096235710522325919 5342382144353565783488879)
  ·
    refine ⟨8013573216530348675233319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5342382144353565783488879 8013573216530348675233319)
    ·
      refine ⟨12020359824795523012849979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013573216530348675233319 12020359824795523012849979)
      ·
        refine ⟨18030539737193284519274969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12020359824795523012849979 18030539737193284519274969)
        ·
          refine ⟨13522904802894963389456227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18030539737193284519274969 13522904802894963389456227)
          ·
            refine ⟨20284357204342445084184341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13522904802894963389456227 20284357204342445084184341)
            ·
              refine ⟨950829243953552113321141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20284357204342445084184341 950829243953552113321141)
              ·
                refine ⟨89140241620645510623857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950829243953552113321141 89140241620645510623857)
                ·
                  refine ⟨66855181215484132967893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89140241620645510623857 66855181215484132967893)
                  ·
                    rfl

theorem cell20_146475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 2].length) (baseStart_146475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146475 prefixEnd_146475 := by exact prefixLift 146475
  have htrace : WordTrace (prefixWord ++ tailWord_146475) baseStart_146475 baseEnd_146475 := by
    simpa [prefixWord, tailWord_146475, baseEnd_146475] using wordTrace_append hprefix tailTrace_146475
  have hstable : (prefixWord ++ tailWord_146475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146475).length < 2 ^ (prefixWord ++ tailWord_146475).sum := by decide
  have hdescent : baseEnd_146475 < baseStart_146475 := by decide
  rcases family_descends (prefixWord ++ tailWord_146475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146492 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 2]
def baseStart_146492 : Nat := 118140960795 + 146492 * 2 ^ 59
def prefixEnd_146492 : Nat := 4983230072969 + 3 ^ 40 * 146492 * 2
def baseEnd_146492 : Nat := 66862940478707629401157

theorem tailTrace_146492 : CollatzResearch.WordTrace tailWord_146492 prefixEnd_146492 66862940478707629401157 := by
  unfold tailWord_146492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671501092645988843428865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3562001456861318457905153 2671501092645988843428865)
  ·
    refine ⟨2003625819484491632571649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2671501092645988843428865 2003625819484491632571649)
    ·
      refine ⟨1502719364613368724428737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2003625819484491632571649 1502719364613368724428737)
      ·
        refine ⟨1127039523460026543321553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1502719364613368724428737 1127039523460026543321553)
        ·
          refine ⟨845279642595019907491165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127039523460026543321553 845279642595019907491165)
          ·
            refine ⟨316979865973132465309187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 845279642595019907491165 316979865973132465309187)
            ·
              refine ⟨475469798959698697963781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316979865973132465309187 475469798959698697963781)
              ·
                refine ⟨89150587304943505868209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 475469798959698697963781 89150587304943505868209)
                ·
                  refine ⟨66862940478707629401157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89150587304943505868209 66862940478707629401157)
                  ·
                    rfl

theorem cell20_146492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_146492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146492 prefixEnd_146492 := by exact prefixLift 146492
  have htrace : WordTrace (prefixWord ++ tailWord_146492) baseStart_146492 baseEnd_146492 := by
    simpa [prefixWord, tailWord_146492, baseEnd_146492] using wordTrace_append hprefix tailTrace_146492
  have hstable : (prefixWord ++ tailWord_146492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146492).length < 2 ^ (prefixWord ++ tailWord_146492).sum := by decide
  have hdescent : baseEnd_146492 < baseStart_146492 := by decide
  rcases family_descends (prefixWord ++ tailWord_146492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146496 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_146496 : Nat := 118140960795 + 146496 * 2 ^ 59
def prefixEnd_146496 : Nat := 4983230072969 + 3 ^ 40 * 146496 * 2
def baseEnd_146496 : Nat := 66864766187701393267807

theorem tailTrace_146496 : CollatzResearch.WordTrace tailWord_146496 prefixEnd_146496 66864766187701393267807 := by
  unfold tailWord_146496
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671574038638743185001671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3562098718184990913335561 2671574038638743185001671)
  ·
    refine ⟨4007361057958114777502507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671574038638743185001671 4007361057958114777502507)
    ·
      refine ⟨6011041586937172166253761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4007361057958114777502507 6011041586937172166253761)
      ·
        refine ⟨4508281190202879124690321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6011041586937172166253761 4508281190202879124690321)
        ·
          refine ⟨3381210892652159343517741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4508281190202879124690321 3381210892652159343517741)
          ·
            refine ⟨1267954084744559753819153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3381210892652159343517741 1267954084744559753819153)
            ·
              refine ⟨950965563558419815364365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267954084744559753819153 950965563558419815364365)
              ·
                refine ⟨356612086334407430761637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950965563558419815364365 356612086334407430761637)
                ·
                  refine ⟨66864766187701393267807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356612086334407430761637 66864766187701393267807)
                  ·
                    rfl

theorem cell20_146496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_146496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146496 prefixEnd_146496 := by exact prefixLift 146496
  have htrace : WordTrace (prefixWord ++ tailWord_146496) baseStart_146496 baseEnd_146496 := by
    simpa [prefixWord, tailWord_146496, baseEnd_146496] using wordTrace_append hprefix tailTrace_146496
  have hstable : (prefixWord ++ tailWord_146496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146496).length < 2 ^ (prefixWord ++ tailWord_146496).sum := by decide
  have hdescent : baseEnd_146496 < baseStart_146496 := by decide
  rcases family_descends (prefixWord ++ tailWord_146496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146520 : List Nat := [2, 1, 2, 2, 1, 3, 5, 4]
def baseStart_146520 : Nat := 118140960795 + 146520 * 2 ^ 59
def prefixEnd_146520 : Nat := 4983230072969 + 3 ^ 40 * 146520 * 2
def baseEnd_146520 : Nat := 22291906813887992155903

theorem tailTrace_146520 : CollatzResearch.WordTrace tailWord_146520 prefixEnd_146520 22291906813887992155903 := by
  unfold tailWord_146520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672011714595269234438507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3562682286127025645918009 2672011714595269234438507)
  ·
    refine ⟨4008017571892903851657761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2672011714595269234438507 4008017571892903851657761)
    ·
      refine ⟨3006013178919677888743321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4008017571892903851657761 3006013178919677888743321)
      ·
        refine ⟨2254509884189758416557491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3006013178919677888743321 2254509884189758416557491)
        ·
          refine ⟨3381764826284637624836237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254509884189758416557491 3381764826284637624836237)
          ·
            refine ⟨1268161809856739109313589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3381764826284637624836237 1268161809856739109313589)
            ·
              refine ⟨118890169674069291498149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1268161809856739109313589 118890169674069291498149)
              ·
                refine ⟨22291906813887992155903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118890169674069291498149 22291906813887992155903)
                ·
                  rfl

theorem cell20_146520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_146520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146520 prefixEnd_146520 := by exact prefixLift 146520
  have htrace : WordTrace (prefixWord ++ tailWord_146520) baseStart_146520 baseEnd_146520 := by
    simpa [prefixWord, tailWord_146520, baseEnd_146520] using wordTrace_append hprefix tailTrace_146520
  have hstable : (prefixWord ++ tailWord_146520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146520).length < 2 ^ (prefixWord ++ tailWord_146520).sum := by decide
  have hdescent : baseEnd_146520 < baseStart_146520 := by decide
  rcases family_descends (prefixWord ++ tailWord_146520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146526 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_146526 : Nat := 118140960795 + 146526 * 2 ^ 59
def prefixEnd_146526 : Nat := 4983230072969 + 3 ^ 40 * 146526 * 2
def baseEnd_146526 : Nat := 66878459005154622267685

theorem tailTrace_146526 : CollatzResearch.WordTrace tailWord_146526 prefixEnd_146526 66878459005154622267685 := by
  unfold tailWord_146526
  simp only [CollatzResearch.WordTrace]
  refine ⟨668030283396100186699429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3562828178112534329063621 668030283396100186699429)
  ·
    refine ⟨125255678136768785006143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 668030283396100186699429 125255678136768785006143)
    ·
      refine ⟨187883517205153177509215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125255678136768785006143 187883517205153177509215)
      ·
        refine ⟨281825275807729766263823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187883517205153177509215 281825275807729766263823)
        ·
          refine ⟨422737913711594649395735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281825275807729766263823 422737913711594649395735)
          ·
            refine ⟨634106870567391974093603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422737913711594649395735 634106870567391974093603)
            ·
              refine ⟨951160305851087961140405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634106870567391974093603 951160305851087961140405)
              ·
                refine ⟨89171278673539496356913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 951160305851087961140405 89171278673539496356913)
                ·
                  refine ⟨66878459005154622267685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89171278673539496356913 66878459005154622267685)
                  ·
                    rfl

theorem cell20_146526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_146526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146526 prefixEnd_146526 := by exact prefixLift 146526
  have htrace : WordTrace (prefixWord ++ tailWord_146526) baseStart_146526 baseEnd_146526 := by
    simpa [prefixWord, tailWord_146526, baseEnd_146526] using wordTrace_append hprefix tailTrace_146526
  have hstable : (prefixWord ++ tailWord_146526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146526).length < 2 ^ (prefixWord ++ tailWord_146526).sum := by decide
  have hdescent : baseEnd_146526 < baseStart_146526 := by decide
  rcases family_descends (prefixWord ++ tailWord_146526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146551 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 2]
def baseStart_146551 : Nat := 118140960795 + 146551 * 2 ^ 59
def prefixEnd_146551 : Nat := 4983230072969 + 3 ^ 40 * 146551 * 2
def baseEnd_146551 : Nat := 66889869686365646434249

theorem tailTrace_146551 : CollatzResearch.WordTrace tailWord_146551 prefixEnd_146551 66889869686365646434249 := by
  unfold tailWord_146551
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345154092078230763255507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3563436061385487175503671 5345154092078230763255507)
  ·
    refine ⟨8017731138117346144883261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345154092078230763255507 8017731138117346144883261)
    ·
      refine ⟨3006649176794004804331223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8017731138117346144883261 3006649176794004804331223)
      ·
        refine ⟨4509973765191007206496835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3006649176794004804331223 4509973765191007206496835)
        ·
          refine ⟨6764960647786510809745253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4509973765191007206496835 6764960647786510809745253)
          ·
            refine ⟨1268430121459970776827235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6764960647786510809745253 1268430121459970776827235)
            ·
              refine ⟨1902645182189956165240853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268430121459970776827235 1902645182189956165240853)
              ·
                refine ⟨89186492915154195245665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1902645182189956165240853 89186492915154195245665)
                ·
                  refine ⟨66889869686365646434249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89186492915154195245665 66889869686365646434249)
                  ·
                    rfl

theorem cell20_146551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 2].length) (baseStart_146551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146551 prefixEnd_146551 := by exact prefixLift 146551
  have htrace : WordTrace (prefixWord ++ tailWord_146551) baseStart_146551 baseEnd_146551 := by
    simpa [prefixWord, tailWord_146551, baseEnd_146551] using wordTrace_append hprefix tailTrace_146551
  have hstable : (prefixWord ++ tailWord_146551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146551).length < 2 ^ (prefixWord ++ tailWord_146551).sum := by decide
  have hdescent : baseEnd_146551 < baseStart_146551 := by decide
  rcases family_descends (prefixWord ++ tailWord_146551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146561 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 3]
def baseStart_146561 : Nat := 118140960795 + 146561 * 2 ^ 59
def prefixEnd_146561 : Nat := 4983230072969 + 3 ^ 40 * 146561 * 2
def baseEnd_146561 : Nat := 66894433958850056100875

theorem tailTrace_146561 : CollatzResearch.WordTrace tailWord_146561 prefixEnd_146561 66894433958850056100875 := by
  unfold tailWord_146561
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345518822042002471119537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3563679214694668314079691 5345518822042002471119537)
  ·
    refine ⟨4009139116531501853339653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5345518822042002471119537 4009139116531501853339653)
    ·
      refine ⟨751713584349656597501185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4009139116531501853339653 751713584349656597501185)
      ·
        refine ⟨563785188262242448125889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751713584349656597501185 563785188262242448125889)
        ·
          refine ⟨422838891196681836094417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563785188262242448125889 422838891196681836094417)
          ·
            refine ⟨317129168397511377070813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422838891196681836094417 317129168397511377070813)
            ·
              refine ⟨118923438149066766401555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317129168397511377070813 118923438149066766401555)
              ·
                refine ⟨178385157223600149602333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118923438149066766401555 178385157223600149602333)
                ·
                  refine ⟨66894433958850056100875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178385157223600149602333 66894433958850056100875)
                  ·
                    rfl

theorem cell20_146561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_146561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146561 prefixEnd_146561 := by exact prefixLift 146561
  have htrace : WordTrace (prefixWord ++ tailWord_146561) baseStart_146561 baseEnd_146561 := by
    simpa [prefixWord, tailWord_146561, baseEnd_146561] using wordTrace_append hprefix tailTrace_146561
  have hstable : (prefixWord ++ tailWord_146561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146561).length < 2 ^ (prefixWord ++ tailWord_146561).sum := by decide
  have hdescent : baseEnd_146561 < baseStart_146561 := by decide
  rcases family_descends (prefixWord ++ tailWord_146561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146596 : List Nat := [2, 3, 1, 2, 3, 3, 6]
def baseStart_146596 : Nat := 118140960795 + 146596 * 2 ^ 59
def prefixEnd_146596 : Nat := 4983230072969 + 3 ^ 40 * 146596 * 2
def baseEnd_146596 : Nat := 7434489879171721103785

theorem tailTrace_146596 : CollatzResearch.WordTrace tailWord_146596 prefixEnd_146596 7434489879171721103785 := by
  unfold tailWord_146596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673397688457601724321821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3564530251276802299095761 2673397688457601724321821)
  ·
    refine ⟨1002524133171600646620683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2673397688457601724321821 1002524133171600646620683)
    ·
      refine ⟨1503786199757400969931025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002524133171600646620683 1503786199757400969931025)
      ·
        refine ⟨1127839649818050727448269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1503786199757400969931025 1127839649818050727448269)
        ·
          refine ⟨422939868681769022793101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1127839649818050727448269 422939868681769022793101)
          ·
            refine ⟨158602450755663383547413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422939868681769022793101 158602450755663383547413)
            ·
              refine ⟨7434489879171721103785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158602450755663383547413 7434489879171721103785)
              ·
                rfl

theorem cell20_146596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 6].length) (baseStart_146596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146596 prefixEnd_146596 := by exact prefixLift 146596
  have htrace : WordTrace (prefixWord ++ tailWord_146596) baseStart_146596 baseEnd_146596 := by
    simpa [prefixWord, tailWord_146596, baseEnd_146596] using wordTrace_append hprefix tailTrace_146596
  have hstable : (prefixWord ++ tailWord_146596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146596).length < 2 ^ (prefixWord ++ tailWord_146596).sum := by decide
  have hdescent : baseEnd_146596 < baseStart_146596 := by decide
  rcases family_descends (prefixWord ++ tailWord_146596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146602 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_146602 : Nat := 118140960795 + 146602 * 2 ^ 59
def prefixEnd_146602 : Nat := 4983230072969 + 3 ^ 40 * 146602 * 2
def baseEnd_146602 : Nat := 66913147476036135734041

theorem tailTrace_146602 : CollatzResearch.WordTrace tailWord_146602 prefixEnd_146602 66913147476036135734041 := by
  unfold tailWord_146602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336753553723366618340515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3564676143262310982241373 1336753553723366618340515)
  ·
    refine ⟨2005130330585049927510773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1336753553723366618340515 2005130330585049927510773)
    ·
      refine ⟨187980968492348430704135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2005130330585049927510773 187980968492348430704135)
      ·
        refine ⟨281971452738522646056203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187980968492348430704135 281971452738522646056203)
        ·
          refine ⟨422957179107783969084305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281971452738522646056203 422957179107783969084305)
          ·
            refine ⟨317217884330837976813229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422957179107783969084305 317217884330837976813229)
            ·
              refine ⟨118956706624064241304961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317217884330837976813229 118956706624064241304961)
              ·
                refine ⟨89217529968048180978721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118956706624064241304961 89217529968048180978721)
                ·
                  refine ⟨66913147476036135734041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89217529968048180978721 66913147476036135734041)
                  ·
                    rfl

theorem cell20_146602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_146602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146602 prefixEnd_146602 := by exact prefixLift 146602
  have htrace : WordTrace (prefixWord ++ tailWord_146602) baseStart_146602 baseEnd_146602 := by
    simpa [prefixWord, tailWord_146602, baseEnd_146602] using wordTrace_append hprefix tailTrace_146602
  have hstable : (prefixWord ++ tailWord_146602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146602).length < 2 ^ (prefixWord ++ tailWord_146602).sum := by decide
  have hdescent : baseEnd_146602 < baseStart_146602 := by decide
  rcases family_descends (prefixWord ++ tailWord_146602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146617 : List Nat := [1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_146617 : Nat := 118140960795 + 146617 * 2 ^ 59
def prefixEnd_146617 : Nat := 4983230072969 + 3 ^ 40 * 146617 * 2
def baseEnd_146617 : Nat := 22306664628254250077993

theorem tailTrace_146617 : CollatzResearch.WordTrace tailWord_146617 prefixEnd_146617 22306664628254250077993 := by
  unfold tailWord_146617
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347561309839124035158105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3565040873226082690105403 5347561309839124035158105)
  ·
    refine ⟨4010670982379343026368579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5347561309839124035158105 4010670982379343026368579)
    ·
      refine ⟨6016006473569014539552869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4010670982379343026368579 6016006473569014539552869)
      ·
        refine ⟨1128001213794190226166163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6016006473569014539552869 1128001213794190226166163)
        ·
          refine ⟨1692001820691285339249245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128001213794190226166163 1692001820691285339249245)
          ·
            refine ⟨634500682759232002218467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1692001820691285339249245 634500682759232002218467)
            ·
              refine ⟨951751024138848003327701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634500682759232002218467 951751024138848003327701)
              ·
                refine ⟨22306664628254250077993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 951751024138848003327701 22306664628254250077993)
                ·
                  rfl

theorem cell20_146617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_146617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146617 prefixEnd_146617 := by exact prefixLift 146617
  have htrace : WordTrace (prefixWord ++ tailWord_146617) baseStart_146617 baseEnd_146617 := by
    simpa [prefixWord, tailWord_146617, baseEnd_146617] using wordTrace_append hprefix tailTrace_146617
  have hstable : (prefixWord ++ tailWord_146617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146617).length < 2 ^ (prefixWord ++ tailWord_146617).sum := by decide
  have hdescent : baseEnd_146617 < baseStart_146617 := by decide
  rcases family_descends (prefixWord ++ tailWord_146617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146620 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_146620 : Nat := 118140960795 + 146620 * 2 ^ 59
def prefixEnd_146620 : Nat := 4983230072969 + 3 ^ 40 * 146620 * 2
def baseEnd_146620 : Nat := 66921363166508073133967

theorem tailTrace_146620 : CollatzResearch.WordTrace tailWord_146620 prefixEnd_146620 66921363166508073133967 := by
  unfold tailWord_146620
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673835364414127773758657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3565113819218837031678209 2673835364414127773758657)
  ·
    refine ⟨2005376523310595830318993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2673835364414127773758657 2005376523310595830318993)
    ·
      refine ⟨1504032392482946872739245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2005376523310595830318993 1504032392482946872739245)
      ·
        refine ⟨564012147181105077277217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1504032392482946872739245 564012147181105077277217)
        ·
          refine ⟨423009110385828807957913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564012147181105077277217 423009110385828807957913)
          ·
            refine ⟨317256832789371605968435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423009110385828807957913 317256832789371605968435)
            ·
              refine ⟨475885249184057408952653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317256832789371605968435 475885249184057408952653)
              ·
                refine ⟨178456968444021528357245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475885249184057408952653 178456968444021528357245)
                ·
                  refine ⟨66921363166508073133967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178456968444021528357245 66921363166508073133967)
                  ·
                    rfl

theorem cell20_146620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_146620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146620 prefixEnd_146620 := by exact prefixLift 146620
  have htrace : WordTrace (prefixWord ++ tailWord_146620) baseStart_146620 baseEnd_146620 := by
    simpa [prefixWord, tailWord_146620, baseEnd_146620] using wordTrace_append hprefix tailTrace_146620
  have hstable : (prefixWord ++ tailWord_146620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146620).length < 2 ^ (prefixWord ++ tailWord_146620).sum := by decide
  have hdescent : baseEnd_146620 < baseStart_146620 := by decide
  rcases family_descends (prefixWord ++ tailWord_146620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146748 : List Nat := [2, 2, 2, 2, 1, 3, 4, 4]
def baseStart_146748 : Nat := 118140960795 + 146748 * 2 ^ 59
def prefixEnd_146748 : Nat := 4983230072969 + 3 ^ 40 * 146748 * 2
def baseEnd_146748 : Nat := 22326595284769505622259

theorem tailTrace_146748 : CollatzResearch.WordTrace tailWord_146748 prefixEnd_146748 22326595284769505622259 := by
  unfold tailWord_146748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676169636182266704088449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3568226181576355605451265 2676169636182266704088449)
  ·
    refine ⟨2007127227136700028066337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2676169636182266704088449 2007127227136700028066337)
    ·
      refine ⟨1505345420352525021049753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2007127227136700028066337 1505345420352525021049753)
      ·
        refine ⟨1129009065264393765787315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1505345420352525021049753 1129009065264393765787315)
        ·
          refine ⟨1693513597896590648680973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129009065264393765787315 1693513597896590648680973)
          ·
            refine ⟨635067599211221493255365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1693513597896590648680973 635067599211221493255365)
            ·
              refine ⟨119075174852104029985381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 635067599211221493255365 119075174852104029985381)
              ·
                refine ⟨22326595284769505622259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119075174852104029985381 22326595284769505622259)
                ·
                  rfl

theorem cell20_146748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_146748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146748 prefixEnd_146748 := by exact prefixLift 146748
  have htrace : WordTrace (prefixWord ++ tailWord_146748) baseStart_146748 baseEnd_146748 := by
    simpa [prefixWord, tailWord_146748, baseEnd_146748] using wordTrace_append hprefix tailTrace_146748
  have hstable : (prefixWord ++ tailWord_146748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146748).length < 2 ^ (prefixWord ++ tailWord_146748).sum := by decide
  have hdescent : baseEnd_146748 < baseStart_146748 := by decide
  rcases family_descends (prefixWord ++ tailWord_146748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146776 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_146776 : Nat := 118140960795 + 146776 * 2 ^ 59
def prefixEnd_146776 : Nat := 4983230072969 + 3 ^ 40 * 146776 * 2
def baseEnd_146776 : Nat := 66992565817264863933329

theorem tailTrace_146776 : CollatzResearch.WordTrace tailWord_146776 prefixEnd_146776 66992565817264863933329 := by
  unfold tailWord_146776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676680258131547095098091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3568907010842062793464121 2676680258131547095098091)
  ·
    refine ⟨4015020387197320642647137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2676680258131547095098091 4015020387197320642647137)
    ·
      refine ⟨3011265290397990481985353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4015020387197320642647137 3011265290397990481985353)
      ·
        refine ⟨2258448967798492861489015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3011265290397990481985353 2258448967798492861489015)
        ·
          refine ⟨3387673451697739292233523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258448967798492861489015 3387673451697739292233523)
          ·
            refine ⟨5081510177546608938350285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387673451697739292233523 5081510177546608938350285)
            ·
              refine ⟨1905566316579978351881357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5081510177546608938350285 1905566316579978351881357)
              ·
                refine ⟨714587368717491881955509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905566316579978351881357 714587368717491881955509)
                ·
                  refine ⟨66992565817264863933329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 714587368717491881955509 66992565817264863933329)
                  ·
                    rfl

theorem cell20_146776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_146776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146776 prefixEnd_146776 := by exact prefixLift 146776
  have htrace : WordTrace (prefixWord ++ tailWord_146776) baseStart_146776 baseEnd_146776 := by
    simpa [prefixWord, tailWord_146776, baseEnd_146776] using wordTrace_append hprefix tailTrace_146776
  have hstable : (prefixWord ++ tailWord_146776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146776).length < 2 ^ (prefixWord ++ tailWord_146776).sum := by decide
  have hdescent : baseEnd_146776 < baseStart_146776 := by decide
  rcases family_descends (prefixWord ++ tailWord_146776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146786 : List Nat := [3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_146786 : Nat := 118140960795 + 146786 * 2 ^ 59
def prefixEnd_146786 : Nat := 4983230072969 + 3 ^ 40 * 146786 * 2
def baseEnd_146786 : Nat := 22332376696583091199985

theorem tailTrace_146786 : CollatzResearch.WordTrace tailWord_146786 prefixEnd_146786 22332376696583091199985 := by
  unfold tailWord_146786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338431311556716474515053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3569150164151243932040141 1338431311556716474515053)
  ·
    refine ⟨501911741833768677943145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1338431311556716474515053 501911741833768677943145)
    ·
      refine ⟨376433806375326508457359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 501911741833768677943145 376433806375326508457359)
      ·
        refine ⟨564650709562989762686039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376433806375326508457359 564650709562989762686039)
        ·
          refine ⟨846976064344484644029059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564650709562989762686039 846976064344484644029059)
          ·
            refine ⟨1270464096516726966043589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846976064344484644029059 1270464096516726966043589)
            ·
              refine ⟨238212018096886306133173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1270464096516726966043589 238212018096886306133173)
              ·
                refine ⟨22332376696583091199985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 238212018096886306133173 22332376696583091199985)
                ·
                  rfl

theorem cell20_146786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_146786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146786 prefixEnd_146786 := by exact prefixLift 146786
  have htrace : WordTrace (prefixWord ++ tailWord_146786) baseStart_146786 baseEnd_146786 := by
    simpa [prefixWord, tailWord_146786, baseEnd_146786] using wordTrace_append hprefix tailTrace_146786
  have hstable : (prefixWord ++ tailWord_146786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146786).length < 2 ^ (prefixWord ++ tailWord_146786).sum := by decide
  have hdescent : baseEnd_146786 < baseStart_146786 := by decide
  rcases family_descends (prefixWord ++ tailWord_146786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146830 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_146830 : Nat := 118140960795 + 146830 * 2 ^ 59
def prefixEnd_146830 : Nat := 4983230072969 + 3 ^ 40 * 146830 * 2
def baseEnd_146830 : Nat := 67017212888680676133109

theorem tailTrace_146830 : CollatzResearch.WordTrace tailWord_146830 prefixEnd_146830 67017212888680676133109 := by
  unfold tailWord_146830
  simp only [CollatzResearch.WordTrace]
  refine ⟨669416257258432676582743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3570220038711640941774629 669416257258432676582743)
  ·
    refine ⟨1004124385887649014874115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 669416257258432676582743 1004124385887649014874115)
    ·
      refine ⟨1506186578831473522311173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004124385887649014874115 1506186578831473522311173)
      ·
        refine ⟨282409983530901285433345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1506186578831473522311173 282409983530901285433345)
        ·
          refine ⟨211807487648175964075009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282409983530901285433345 211807487648175964075009)
          ·
            refine ⟨158855615736131973056257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211807487648175964075009 158855615736131973056257)
            ·
              refine ⟨119141711802098979792193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158855615736131973056257 119141711802098979792193)
              ·
                refine ⟨89356283851574234844145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119141711802098979792193 89356283851574234844145)
                ·
                  refine ⟨67017212888680676133109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89356283851574234844145 67017212888680676133109)
                  ·
                    rfl

theorem cell20_146830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_146830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146830 prefixEnd_146830 := by exact prefixLift 146830
  have htrace : WordTrace (prefixWord ++ tailWord_146830) baseStart_146830 baseEnd_146830 := by
    simpa [prefixWord, tailWord_146830, baseEnd_146830] using wordTrace_append hprefix tailTrace_146830
  have hstable : (prefixWord ++ tailWord_146830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146830).length < 2 ^ (prefixWord ++ tailWord_146830).sum := by decide
  have hdescent : baseEnd_146830 < baseStart_146830 := by decide
  rcases family_descends (prefixWord ++ tailWord_146830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146852 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_146852 : Nat := 118140960795 + 146852 * 2 ^ 59
def prefixEnd_146852 : Nat := 4983230072969 + 3 ^ 40 * 146852 * 2
def baseEnd_146852 : Nat := 67027254288146377399685

theorem tailTrace_146852 : CollatzResearch.WordTrace tailWord_146852 prefixEnd_146852 67027254288146377399685 := by
  unfold tailWord_146852
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678066231993879584981405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3570754975991839446641873 2678066231993879584981405)
  ·
    refine ⟨1004274836997704844368027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2678066231993879584981405 1004274836997704844368027)
    ·
      refine ⟨1506412255496557266552041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004274836997704844368027 1506412255496557266552041)
      ·
        refine ⟨1129809191622417949914031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1506412255496557266552041 1129809191622417949914031)
        ·
          refine ⟨1694713787433626924871047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129809191622417949914031 1694713787433626924871047)
          ·
            refine ⟨2542070681150440387306571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694713787433626924871047 2542070681150440387306571)
            ·
              refine ⟨3813106021725660580959857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542070681150440387306571 3813106021725660580959857)
              ·
                refine ⟨2859829516294245435719893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3813106021725660580959857 2859829516294245435719893)
                ·
                  refine ⟨67027254288146377399685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2859829516294245435719893 67027254288146377399685)
                  ·
                    rfl

theorem cell20_146852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_146852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146852 prefixEnd_146852 := by exact prefixLift 146852
  have htrace : WordTrace (prefixWord ++ tailWord_146852) baseStart_146852 baseEnd_146852 := by
    simpa [prefixWord, tailWord_146852, baseEnd_146852] using wordTrace_append hprefix tailTrace_146852
  have hstable : (prefixWord ++ tailWord_146852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146852).length < 2 ^ (prefixWord ++ tailWord_146852).sum := by decide
  have hdescent : baseEnd_146852 < baseStart_146852 := by decide
  rcases family_descends (prefixWord ++ tailWord_146852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146917 : List Nat := [1, 3, 1, 5, 1, 3, 2, 4]
def baseStart_146917 : Nat := 118140960795 + 146917 * 2 ^ 59
def prefixEnd_146917 : Nat := 4983230072969 + 3 ^ 40 * 146917 * 2
def baseEnd_146917 : Nat := 22352307353098346744251

theorem tailTrace_146917 : CollatzResearch.WordTrace tailWord_146917 prefixEnd_146917 22352307353098346744251 := by
  unfold tailWord_146917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358503208752275271079005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3572335472501516847386003 5358503208752275271079005)
  ·
    refine ⟨2009438703282103226654627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5358503208752275271079005 2009438703282103226654627)
    ·
      refine ⟨3014158054923154839981941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2009438703282103226654627 3014158054923154839981941)
      ·
        refine ⟨282577317649045766248307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3014158054923154839981941 282577317649045766248307)
        ·
          refine ⟨423865976473568649372461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282577317649045766248307 423865976473568649372461)
          ·
            refine ⟨158949741177588243514673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423865976473568649372461 158949741177588243514673)
            ·
              refine ⟨119212305883191182636005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158949741177588243514673 119212305883191182636005)
              ·
                refine ⟨22352307353098346744251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119212305883191182636005 22352307353098346744251)
                ·
                  rfl

theorem cell20_146917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_146917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146917 prefixEnd_146917 := by exact prefixLift 146917
  have htrace : WordTrace (prefixWord ++ tailWord_146917) baseStart_146917 baseEnd_146917 := by
    simpa [prefixWord, tailWord_146917, baseEnd_146917] using wordTrace_append hprefix tailTrace_146917
  have hstable : (prefixWord ++ tailWord_146917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146917).length < 2 ^ (prefixWord ++ tailWord_146917).sum := by decide
  have hdescent : baseEnd_146917 < baseStart_146917 := by decide
  rcases family_descends (prefixWord ++ tailWord_146917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146928 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_146928 : Nat := 118140960795 + 146928 * 2 ^ 59
def prefixEnd_146928 : Nat := 4983230072969 + 3 ^ 40 * 146928 * 2
def baseEnd_146928 : Nat := 67061942759027890866041

theorem tailTrace_146928 : CollatzResearch.WordTrace tailWord_146928 prefixEnd_146928 67061942759027890866041 := by
  unfold tailWord_146928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679452205856212074864719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3572602941141616099819625 2679452205856212074864719)
  ·
    refine ⟨4019178308784318112297079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679452205856212074864719 4019178308784318112297079)
    ·
      refine ⟨6028767463176477168445619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019178308784318112297079 6028767463176477168445619)
      ·
        refine ⟨9043151194764715752668429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028767463176477168445619 9043151194764715752668429)
        ·
          refine ⟨3391181698036768407250661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9043151194764715752668429 3391181698036768407250661)
          ·
            refine ⟨635846568381894076359499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3391181698036768407250661 635846568381894076359499)
            ·
              refine ⟨953769852572841114539249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635846568381894076359499 953769852572841114539249)
              ·
                refine ⟨715327389429630835904437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953769852572841114539249 715327389429630835904437)
                ·
                  refine ⟨67061942759027890866041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 715327389429630835904437 67061942759027890866041)
                  ·
                    rfl

theorem cell20_146928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_146928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146928 prefixEnd_146928 := by exact prefixLift 146928
  have htrace : WordTrace (prefixWord ++ tailWord_146928) baseStart_146928 baseEnd_146928 := by
    simpa [prefixWord, tailWord_146928, baseEnd_146928] using wordTrace_append hprefix tailTrace_146928
  have hstable : (prefixWord ++ tailWord_146928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146928).length < 2 ^ (prefixWord ++ tailWord_146928).sum := by decide
  have hdescent : baseEnd_146928 < baseStart_146928 := by decide
  rcases family_descends (prefixWord ++ tailWord_146928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146948 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_146948 : Nat := 118140960795 + 146948 * 2 ^ 59
def prefixEnd_146948 : Nat := 4983230072969 + 3 ^ 40 * 146948 * 2
def baseEnd_146948 : Nat := 67071071303996710199293

theorem tailTrace_146948 : CollatzResearch.WordTrace tailWord_146948 prefixEnd_146948 67071071303996710199293 := by
  unfold tailWord_146948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679816935819983782728749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3573089247759978376971665 2679816935819983782728749)
  ·
    refine ⟨1004931350932493918523281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2679816935819983782728749 1004931350932493918523281)
    ·
      refine ⟨753698513199370438892461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1004931350932493918523281 753698513199370438892461)
      ·
        refine ⟨282636942449763914584673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 753698513199370438892461 282636942449763914584673)
        ·
          refine ⟨211977706837322935938505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282636942449763914584673 211977706837322935938505)
          ·
            refine ⟨158983280127992201953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211977706837322935938505 158983280127992201953879)
            ·
              refine ⟨238474920191988302930819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158983280127992201953879 238474920191988302930819)
              ·
                refine ⟨357712380287982454396229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238474920191988302930819 357712380287982454396229)
                ·
                  refine ⟨67071071303996710199293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357712380287982454396229 67071071303996710199293)
                  ·
                    rfl

theorem cell20_146948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_146948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146948 prefixEnd_146948 := by exact prefixLift 146948
  have htrace : WordTrace (prefixWord ++ tailWord_146948) baseStart_146948 baseEnd_146948 := by
    simpa [prefixWord, tailWord_146948, baseEnd_146948] using wordTrace_append hprefix tailTrace_146948
  have hstable : (prefixWord ++ tailWord_146948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146948).length < 2 ^ (prefixWord ++ tailWord_146948).sum := by decide
  have hdescent : baseEnd_146948 < baseStart_146948 := by decide
  rcases family_descends (prefixWord ++ tailWord_146948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146952 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_146952 : Nat := 118140960795 + 146952 * 2 ^ 59
def prefixEnd_146952 : Nat := 4983230072969 + 3 ^ 40 * 146952 * 2
def baseEnd_146952 : Nat := 67072897012990474065943

theorem tailTrace_146952 : CollatzResearch.WordTrace tailWord_146952 prefixEnd_146952 67072897012990474065943 := by
  unfold tailWord_146952
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679889881812738124301555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3573186509083650832402073 2679889881812738124301555)
  ·
    refine ⟨4019834822719107186452333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679889881812738124301555 4019834822719107186452333)
    ·
      refine ⟨1507438058519665194919625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4019834822719107186452333 1507438058519665194919625)
      ·
        refine ⟨1130578543889748896189719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1507438058519665194919625 1130578543889748896189719)
        ·
          refine ⟨1695867815834623344284579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130578543889748896189719 1695867815834623344284579)
          ·
            refine ⟨2543801723751935016426869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695867815834623344284579 2543801723751935016426869)
            ·
              refine ⟨238481411601743907790019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2543801723751935016426869 238481411601743907790019)
              ·
                refine ⟨357722117402615861685029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238481411601743907790019 357722117402615861685029)
                ·
                  refine ⟨67072897012990474065943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357722117402615861685029 67072897012990474065943)
                  ·
                    rfl

theorem cell20_146952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_146952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146952 prefixEnd_146952 := by exact prefixLift 146952
  have htrace : WordTrace (prefixWord ++ tailWord_146952) baseStart_146952 baseEnd_146952 := by
    simpa [prefixWord, tailWord_146952, baseEnd_146952] using wordTrace_append hprefix tailTrace_146952
  have hstable : (prefixWord ++ tailWord_146952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146952).length < 2 ^ (prefixWord ++ tailWord_146952).sum := by decide
  have hdescent : baseEnd_146952 < baseStart_146952 := by decide
  rcases family_descends (prefixWord ++ tailWord_146952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146958 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_146958 : Nat := 118140960795 + 146958 * 2 ^ 59
def prefixEnd_146958 : Nat := 4983230072969 + 3 ^ 40 * 146958 * 2
def baseEnd_146958 : Nat := 67075635576481119865919

theorem tailTrace_146958 : CollatzResearch.WordTrace tailWord_146958 prefixEnd_146958 67075635576481119865919 := by
  unfold tailWord_146958
  simp only [CollatzResearch.WordTrace]
  refine ⟨669999825200467409165191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3573332401069159515547685 669999825200467409165191)
  ·
    refine ⟨1004999737800701113747787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 669999825200467409165191 1004999737800701113747787)
    ·
      refine ⟨1507499606701051670621681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004999737800701113747787 1507499606701051670621681)
      ·
        refine ⟨1130624705025788752966261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1507499606701051670621681 1130624705025788752966261)
        ·
          refine ⟨105996066096167695590587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1130624705025788752966261 105996066096167695590587)
          ·
            refine ⟨158994099144251543385881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105996066096167695590587 158994099144251543385881)
            ·
              refine ⟨119245574358188657539411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158994099144251543385881 119245574358188657539411)
              ·
                refine ⟨178868361537282986309117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119245574358188657539411 178868361537282986309117)
                ·
                  refine ⟨67075635576481119865919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178868361537282986309117 67075635576481119865919)
                  ·
                    rfl

theorem cell20_146958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_146958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146958 prefixEnd_146958 := by exact prefixLift 146958
  have htrace : WordTrace (prefixWord ++ tailWord_146958) baseStart_146958 baseEnd_146958 := by
    simpa [prefixWord, tailWord_146958, baseEnd_146958] using wordTrace_append hprefix tailTrace_146958
  have hstable : (prefixWord ++ tailWord_146958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146958).length < 2 ^ (prefixWord ++ tailWord_146958).sum := by decide
  have hdescent : baseEnd_146958 < baseStart_146958 := by decide
  rcases family_descends (prefixWord ++ tailWord_146958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147007 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 2]
def baseStart_147007 : Nat := 118140960795 + 147007 * 2 ^ 59
def prefixEnd_147007 : Nat := 4983230072969 + 3 ^ 40 * 147007 * 2
def baseEnd_147007 : Nat := 67098000511654727232385

theorem tailTrace_147007 : CollatzResearch.WordTrace tailWord_147007 prefixEnd_147007 67098000511654727232385 := by
  unfold tailWord_147007
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361785778426220641855275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3574523852284147094570183 5361785778426220641855275)
  ·
    refine ⟨8042678667639330962782913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5361785778426220641855275 8042678667639330962782913)
    ·
      refine ⟨6032009000729498222087185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8042678667639330962782913 6032009000729498222087185)
      ·
        refine ⟨4524006750547123666565389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6032009000729498222087185 4524006750547123666565389)
        ·
          refine ⟨1696502531455171374962021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4524006750547123666565389 1696502531455171374962021)
          ·
            refine ⟨318094224647844632805379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1696502531455171374962021 318094224647844632805379)
            ·
              refine ⟨477141336971766949208069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318094224647844632805379 477141336971766949208069)
              ·
                refine ⟨89464000682206302976513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477141336971766949208069 89464000682206302976513)
                ·
                  refine ⟨67098000511654727232385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89464000682206302976513 67098000511654727232385)
                  ·
                    rfl

theorem cell20_147007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 2].length) (baseStart_147007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147007 prefixEnd_147007 := by exact prefixLift 147007
  have htrace : WordTrace (prefixWord ++ tailWord_147007) baseStart_147007 baseEnd_147007 := by
    simpa [prefixWord, tailWord_147007, baseEnd_147007] using wordTrace_append hprefix tailTrace_147007
  have hstable : (prefixWord ++ tailWord_147007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147007).length < 2 ^ (prefixWord ++ tailWord_147007).sum := by decide
  have hdescent : baseEnd_147007 < baseStart_147007 := by decide
  rcases family_descends (prefixWord ++ tailWord_147007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147028 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_147028 : Nat := 118140960795 + 147028 * 2 ^ 59
def prefixEnd_147028 : Nat := 4983230072969 + 3 ^ 40 * 147028 * 2
def baseEnd_147028 : Nat := 67107585483871987532299

theorem tailTrace_147028 : CollatzResearch.WordTrace tailWord_147028 prefixEnd_147028 67107585483871987532299 := by
  unfold tailWord_147028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681275855675070614184869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3575034474233427485579825 2681275855675070614184869)
  ·
    refine ⟨502739222939075740159663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2681275855675070614184869 502739222939075740159663)
    ·
      refine ⟨754108834408613610239495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502739222939075740159663 754108834408613610239495)
      ·
        refine ⟨1131163251612920415359243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754108834408613610239495 1131163251612920415359243)
        ·
          refine ⟨1696744877419380623038865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131163251612920415359243 1696744877419380623038865)
          ·
            refine ⟨1272558658064535467279149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696744877419380623038865 1272558658064535467279149)
            ·
              refine ⟨477209496774200800229681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1272558658064535467279149 477209496774200800229681)
              ·
                refine ⟨357907122580650600172261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477209496774200800229681 357907122580650600172261)
                ·
                  refine ⟨67107585483871987532299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357907122580650600172261 67107585483871987532299)
                  ·
                    rfl

theorem cell20_147028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_147028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147028 prefixEnd_147028 := by exact prefixLift 147028
  have htrace : WordTrace (prefixWord ++ tailWord_147028) baseStart_147028 baseEnd_147028 := by
    simpa [prefixWord, tailWord_147028, baseEnd_147028] using wordTrace_append hprefix tailTrace_147028
  have hstable : (prefixWord ++ tailWord_147028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147028).length < 2 ^ (prefixWord ++ tailWord_147028).sum := by decide
  have hdescent : baseEnd_147028 < baseStart_147028 := by decide
  rcases family_descends (prefixWord ++ tailWord_147028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147045 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 2]
def baseStart_147045 : Nat := 118140960795 + 147045 * 2 ^ 59
def prefixEnd_147045 : Nat := 4983230072969 + 3 ^ 40 * 147045 * 2
def baseEnd_147045 : Nat := 67115344747095483965563

theorem tailTrace_147045 : CollatzResearch.WordTrace tailWord_147045 prefixEnd_147045 67115344747095483965563 := by
  unfold tailWord_147045
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363171752288553131738589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3575447834859035421159059 5363171752288553131738589)
  ·
    refine ⟨2011189407108207424401971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5363171752288553131738589 2011189407108207424401971)
    ·
      refine ⟨3016784110662311136602957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011189407108207424401971 3016784110662311136602957)
      ·
        refine ⟨1131294041498366676226109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3016784110662311136602957 1131294041498366676226109)
        ·
          refine ⟨424235265561887503584791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1131294041498366676226109 424235265561887503584791)
          ·
            refine ⟨636352898342831255377187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424235265561887503584791 636352898342831255377187)
            ·
              refine ⟨954529347514246883065781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636352898342831255377187 954529347514246883065781)
              ·
                refine ⟨89487126329460645287417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 954529347514246883065781 89487126329460645287417)
                ·
                  refine ⟨67115344747095483965563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89487126329460645287417 67115344747095483965563)
                  ·
                    rfl

theorem cell20_147045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_147045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147045 prefixEnd_147045 := by exact prefixLift 147045
  have htrace : WordTrace (prefixWord ++ tailWord_147045) baseStart_147045 baseEnd_147045 := by
    simpa [prefixWord, tailWord_147045, baseEnd_147045] using wordTrace_append hprefix tailTrace_147045
  have hstable : (prefixWord ++ tailWord_147045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147045).length < 2 ^ (prefixWord ++ tailWord_147045).sum := by decide
  have hdescent : baseEnd_147045 < baseStart_147045 := by decide
  rcases family_descends (prefixWord ++ tailWord_147045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147062 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_147062 : Nat := 118140960795 + 147062 * 2 ^ 59
def prefixEnd_147062 : Nat := 4983230072969 + 3 ^ 40 * 147062 * 2
def baseEnd_147062 : Nat := 67123104010318980398827

theorem tailTrace_147062 : CollatzResearch.WordTrace tailWord_147062 prefixEnd_147062 67123104010318980398827 := by
  unfold tailWord_147062
  simp only [CollatzResearch.WordTrace]
  refine ⟨335236987076685314694215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3575861195484643356738293 335236987076685314694215)
  ·
    refine ⟨502855480615027972041323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335236987076685314694215 502855480615027972041323)
    ·
      refine ⟨754283220922541958061985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502855480615027972041323 754283220922541958061985)
      ·
        refine ⟨565712415691906468546489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 754283220922541958061985 565712415691906468546489)
        ·
          refine ⟨424284311768929851409867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565712415691906468546489 424284311768929851409867)
          ·
            refine ⟨636426467653394777114801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424284311768929851409867 636426467653394777114801)
            ·
              refine ⟨477319850740046082836101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636426467653394777114801 477319850740046082836101)
              ·
                refine ⟨89497472013758640531769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477319850740046082836101 89497472013758640531769)
                ·
                  refine ⟨67123104010318980398827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89497472013758640531769 67123104010318980398827)
                  ·
                    rfl

theorem cell20_147062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_147062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147062 prefixEnd_147062 := by exact prefixLift 147062
  have htrace : WordTrace (prefixWord ++ tailWord_147062) baseStart_147062 baseEnd_147062 := by
    simpa [prefixWord, tailWord_147062, baseEnd_147062] using wordTrace_append hprefix tailTrace_147062
  have hstable : (prefixWord ++ tailWord_147062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147062).length < 2 ^ (prefixWord ++ tailWord_147062).sum := by decide
  have hdescent : baseEnd_147062 < baseStart_147062 := by decide
  rcases family_descends (prefixWord ++ tailWord_147062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147090 : List Nat := [3, 2, 3, 1, 3, 1, 1, 6]
def baseStart_147090 : Nat := 118140960795 + 147090 * 2 ^ 59
def prefixEnd_147090 : Nat := 4983230072969 + 3 ^ 40 * 147090 * 2
def baseEnd_147090 : Nat := 22378627991091775821793

theorem tailTrace_147090 : CollatzResearch.WordTrace tailWord_147090 prefixEnd_147090 22378627991091775821793 := by
  unfold tailWord_147090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341203259281381454281681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3576542024750350544751149 1341203259281381454281681)
  ·
    refine ⟨1005902444461036090711261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1341203259281381454281681 1005902444461036090711261)
    ·
      refine ⟨377213416672888534016723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1005902444461036090711261 377213416672888534016723)
      ·
        refine ⟨565820125009332801025085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377213416672888534016723 565820125009332801025085)
        ·
          refine ⟨212182546878499800384407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 565820125009332801025085 212182546878499800384407)
          ·
            refine ⟨318273820317749700576611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212182546878499800384407 318273820317749700576611)
            ·
              refine ⟨477410730476624550864917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318273820317749700576611 477410730476624550864917)
              ·
                refine ⟨22378627991091775821793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 477410730476624550864917 22378627991091775821793)
                ·
                  rfl

theorem cell20_147090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_147090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147090 prefixEnd_147090 := by exact prefixLift 147090
  have htrace : WordTrace (prefixWord ++ tailWord_147090) baseStart_147090 baseEnd_147090 := by
    simpa [prefixWord, tailWord_147090, baseEnd_147090] using wordTrace_append hprefix tailTrace_147090
  have hstable : (prefixWord ++ tailWord_147090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147090).length < 2 ^ (prefixWord ++ tailWord_147090).sum := by decide
  have hdescent : baseEnd_147090 < baseStart_147090 := by decide
  rcases family_descends (prefixWord ++ tailWord_147090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147170 : List Nat := [3, 3, 14]
def baseStart_147170 : Nat := 118140960795 + 147170 * 2 ^ 59
def prefixEnd_147170 : Nat := 4983230072969 + 3 ^ 40 * 147170 * 2
def baseEnd_147170 : Nat := 92143207343142119065

theorem tailTrace_147170 : CollatzResearch.WordTrace tailWord_147170 prefixEnd_147170 92143207343142119065 := by
  unfold tailWord_147170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341932719208924870009741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3578487251223799653359309 1341932719208924870009741)
  ·
    refine ⟨503224769703346826253653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1341932719208924870009741 503224769703346826253653)
    ·
      refine ⟨92143207343142119065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 503224769703346826253653 92143207343142119065)
      ·
        rfl

theorem cell20_147170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 14].length) (baseStart_147170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147170 prefixEnd_147170 := by exact prefixLift 147170
  have htrace : WordTrace (prefixWord ++ tailWord_147170) baseStart_147170 baseEnd_147170 := by
    simpa [prefixWord, tailWord_147170, baseEnd_147170] using wordTrace_append hprefix tailTrace_147170
  have hstable : (prefixWord ++ tailWord_147170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147170).length < 2 ^ (prefixWord ++ tailWord_147170).sum := by decide
  have hdescent : baseEnd_147170 < baseStart_147170 := by decide
  rcases family_descends (prefixWord ++ tailWord_147170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147173 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_147173 : Nat := 118140960795 + 147173 * 2 ^ 59
def prefixEnd_147173 : Nat := 4983230072969 + 3 ^ 40 * 147173 * 2
def baseEnd_147173 : Nat := 67173767434895927698373

theorem tailTrace_147173 : CollatzResearch.WordTrace tailWord_147173 prefixEnd_147173 67173767434895927698373 := by
  unfold tailWord_147173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367840295824830992398173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3578560197216553994932115 5367840295824830992398173)
  ·
    refine ⟨2012940110934311622149315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5367840295824830992398173 2012940110934311622149315)
    ·
      refine ⟨3019410166401467433223973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012940110934311622149315 3019410166401467433223973)
      ·
        refine ⟨566139406200275143729495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3019410166401467433223973 566139406200275143729495)
        ·
          refine ⟨849209109300412715594243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566139406200275143729495 849209109300412715594243)
          ·
            refine ⟨1273813663950619073391365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849209109300412715594243 1273813663950619073391365)
            ·
              refine ⟨238840061990741076260881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1273813663950619073391365 238840061990741076260881)
              ·
                refine ⟨179130046493055807195661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238840061990741076260881 179130046493055807195661)
                ·
                  refine ⟨67173767434895927698373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179130046493055807195661 67173767434895927698373)
                  ·
                    rfl

theorem cell20_147173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_147173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147173 prefixEnd_147173 := by exact prefixLift 147173
  have htrace : WordTrace (prefixWord ++ tailWord_147173) baseStart_147173 baseEnd_147173 := by
    simpa [prefixWord, tailWord_147173, baseEnd_147173] using wordTrace_append hprefix tailTrace_147173
  have hstable : (prefixWord ++ tailWord_147173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147173).length < 2 ^ (prefixWord ++ tailWord_147173).sum := by decide
  have hdescent : baseEnd_147173 < baseStart_147173 := by decide
  rcases family_descends (prefixWord ++ tailWord_147173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147176 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 2]
def baseStart_147176 : Nat := 118140960795 + 147176 * 2 ^ 59
def prefixEnd_147176 : Nat := 4983230072969 + 3 ^ 40 * 147176 * 2
def baseEnd_147176 : Nat := 67175136716641250598361

theorem tailTrace_147176 : CollatzResearch.WordTrace tailWord_147176 prefixEnd_147176 67175136716641250598361 := by
  unfold tailWord_147176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683974857406981252378691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3578633143209308336504921 2683974857406981252378691)
  ·
    refine ⟨4025962286110471878568037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2683974857406981252378691 4025962286110471878568037)
    ·
      refine ⟨754867928645713477231507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4025962286110471878568037 754867928645713477231507)
      ·
        refine ⟨1132301892968570215847261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754867928645713477231507 1132301892968570215847261)
        ·
          refine ⟨424613209863213830942723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1132301892968570215847261 424613209863213830942723)
          ·
            refine ⟨636919814794820746414085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424613209863213830942723 636919814794820746414085)
            ·
              refine ⟨119422465274028889952641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 636919814794820746414085 119422465274028889952641)
              ·
                refine ⟨89566848955521667464481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119422465274028889952641 89566848955521667464481)
                ·
                  refine ⟨67175136716641250598361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89566848955521667464481 67175136716641250598361)
                  ·
                    rfl

theorem cell20_147176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_147176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147176 prefixEnd_147176 := by exact prefixLift 147176
  have htrace : WordTrace (prefixWord ++ tailWord_147176) baseStart_147176 baseEnd_147176 := by
    simpa [prefixWord, tailWord_147176, baseEnd_147176] using wordTrace_append hprefix tailTrace_147176
  have hstable : (prefixWord ++ tailWord_147176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147176).length < 2 ^ (prefixWord ++ tailWord_147176).sum := by decide
  have hdescent : baseEnd_147176 < baseStart_147176 := by decide
  rcases family_descends (prefixWord ++ tailWord_147176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147201 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_147201 : Nat := 118140960795 + 147201 * 2 ^ 59
def prefixEnd_147201 : Nat := 4983230072969 + 3 ^ 40 * 147201 * 2
def baseEnd_147201 : Nat := 67186547397852274764925

theorem tailTrace_147201 : CollatzResearch.WordTrace tailWord_147201 prefixEnd_147201 67186547397852274764925 := by
  unfold tailWord_147201
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368861539723391774417457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3579241026482261182944971 5368861539723391774417457)
  ·
    refine ⟨4026646154792543830813093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5368861539723391774417457 4026646154792543830813093)
    ·
      refine ⟨754996154023601968277455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4026646154792543830813093 754996154023601968277455)
      ·
        refine ⟨1132494231035402952416183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754996154023601968277455 1132494231035402952416183)
        ·
          refine ⟨1698741346553104428624275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132494231035402952416183 1698741346553104428624275)
          ·
            refine ⟨2548112019829656642936413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698741346553104428624275 2548112019829656642936413)
            ·
              refine ⟨955542007436121241101155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2548112019829656642936413 955542007436121241101155)
              ·
                refine ⟨1433313011154181861651733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955542007436121241101155 1433313011154181861651733)
                ·
                  refine ⟨67186547397852274764925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1433313011154181861651733 67186547397852274764925)
                  ·
                    rfl

theorem cell20_147201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_147201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147201 prefixEnd_147201 := by exact prefixLift 147201
  have htrace : WordTrace (prefixWord ++ tailWord_147201) baseStart_147201 baseEnd_147201 := by
    simpa [prefixWord, tailWord_147201, baseEnd_147201] using wordTrace_append hprefix tailTrace_147201
  have hstable : (prefixWord ++ tailWord_147201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147201).length < 2 ^ (prefixWord ++ tailWord_147201).sum := by decide
  have hdescent : baseEnd_147201 < baseStart_147201 := by decide
  rcases family_descends (prefixWord ++ tailWord_147201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147204 : List Nat := [2, 3, 2, 2, 1, 3, 3, 4]
def baseStart_147204 : Nat := 118140960795 + 147204 * 2 ^ 59
def prefixEnd_147204 : Nat := 4983230072969 + 3 ^ 40 * 147204 * 2
def baseEnd_147204 : Nat := 22395972226532532554971

theorem tailTrace_147204 : CollatzResearch.WordTrace tailWord_147204 prefixEnd_147204 22395972226532532554971 := by
  unfold tailWord_147204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684485479356261643388333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3579313972475015524517777 2684485479356261643388333)
  ·
    refine ⟨1006682054758598116270625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2684485479356261643388333 1006682054758598116270625)
    ·
      refine ⟨755011541068948587202969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1006682054758598116270625 755011541068948587202969)
      ·
        refine ⟨566258655801711440402227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 755011541068948587202969 566258655801711440402227)
        ·
          refine ⟨849387983702567160603341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566258655801711440402227 849387983702567160603341)
          ·
            refine ⟨318520493888462685226253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 849387983702567160603341 318520493888462685226253)
            ·
              refine ⟨119445185208173506959845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318520493888462685226253 119445185208173506959845)
              ·
                refine ⟨22395972226532532554971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119445185208173506959845 22395972226532532554971)
                ·
                  rfl

theorem cell20_147204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_147204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147204 prefixEnd_147204 := by exact prefixLift 147204
  have htrace : WordTrace (prefixWord ++ tailWord_147204) baseStart_147204 baseEnd_147204 := by
    simpa [prefixWord, tailWord_147204, baseEnd_147204] using wordTrace_append hprefix tailTrace_147204
  have hstable : (prefixWord ++ tailWord_147204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147204).length < 2 ^ (prefixWord ++ tailWord_147204).sum := by decide
  have hdescent : baseEnd_147204 < baseStart_147204 := by decide
  rcases family_descends (prefixWord ++ tailWord_147204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147206 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_147206 : Nat := 118140960795 + 147206 * 2 ^ 59
def prefixEnd_147206 : Nat := 4983230072969 + 3 ^ 40 * 147206 * 2
def baseEnd_147206 : Nat := 67188829534094479598239

theorem tailTrace_147206 : CollatzResearch.WordTrace tailWord_147206 prefixEnd_147206 67188829534094479598239 := by
  unfold tailWord_147206
  simp only [CollatzResearch.WordTrace]
  refine ⟨167782622022039925885921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3579362603136851752232981 167782622022039925885921)
  ·
    refine ⟨125836966516529944414441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167782622022039925885921 125836966516529944414441)
    ·
      refine ⟨94377724887397458310831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125836966516529944414441 94377724887397458310831)
      ·
        refine ⟨141566587331096187466247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94377724887397458310831 141566587331096187466247)
        ·
          refine ⟨212349880996644281199371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141566587331096187466247 212349880996644281199371)
          ·
            refine ⟨318524821494966421799057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212349880996644281199371 318524821494966421799057)
            ·
              refine ⟨238893616121224816349293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318524821494966421799057 238893616121224816349293)
              ·
                refine ⟨89585106045459306130985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238893616121224816349293 89585106045459306130985)
                ·
                  refine ⟨67188829534094479598239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89585106045459306130985 67188829534094479598239)
                  ·
                    rfl

theorem cell20_147206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_147206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147206 prefixEnd_147206 := by exact prefixLift 147206
  have htrace : WordTrace (prefixWord ++ tailWord_147206) baseStart_147206 baseEnd_147206 := by
    simpa [prefixWord, tailWord_147206, baseEnd_147206] using wordTrace_append hprefix tailTrace_147206
  have hstable : (prefixWord ++ tailWord_147206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147206).length < 2 ^ (prefixWord ++ tailWord_147206).sum := by decide
  have hdescent : baseEnd_147206 < baseStart_147206 := by decide
  rcases family_descends (prefixWord ++ tailWord_147206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147232 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_147232 : Nat := 118140960795 + 147232 * 2 ^ 59
def prefixEnd_147232 : Nat := 4983230072969 + 3 ^ 40 * 147232 * 2
def baseEnd_147232 : Nat := 67200696642553944731465

theorem tailTrace_147232 : CollatzResearch.WordTrace tailWord_147232 prefixEnd_147232 67200696642553944731465 := by
  unfold tailWord_147232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684996101305542034397975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3579994801740722712530633 2684996101305542034397975)
  ·
    refine ⟨4027494151958313051596963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2684996101305542034397975 4027494151958313051596963)
    ·
      refine ⟨6041241227937469577395445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4027494151958313051596963 6041241227937469577395445)
      ·
        refine ⟨566366365119137772880823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6041241227937469577395445 566366365119137772880823)
        ·
          refine ⟨849549547678706659321235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566366365119137772880823 849549547678706659321235)
          ·
            refine ⟨1274324321518059988981853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849549547678706659321235 1274324321518059988981853)
            ·
              refine ⟨477871620569272495868195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1274324321518059988981853 477871620569272495868195)
              ·
                refine ⟨716807430853908743802293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477871620569272495868195 716807430853908743802293)
                ·
                  refine ⟨67200696642553944731465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716807430853908743802293 67200696642553944731465)
                  ·
                    rfl

theorem cell20_147232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_147232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147232 prefixEnd_147232 := by exact prefixLift 147232
  have htrace : WordTrace (prefixWord ++ tailWord_147232) baseStart_147232 baseEnd_147232 := by
    simpa [prefixWord, tailWord_147232, baseEnd_147232] using wordTrace_append hprefix tailTrace_147232
  have hstable : (prefixWord ++ tailWord_147232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147232).length < 2 ^ (prefixWord ++ tailWord_147232).sum := by decide
  have hdescent : baseEnd_147232 < baseStart_147232 := by decide
  rcases family_descends (prefixWord ++ tailWord_147232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147263 : List Nat := [1, 1, 2, 2, 6, 1, 1, 6]
def baseStart_147263 : Nat := 118140960795 + 147263 * 2 ^ 59
def prefixEnd_147263 : Nat := 4983230072969 + 3 ^ 40 * 147263 * 2
def baseEnd_147263 : Nat := 22404948629085204899335

theorem tailTrace_147263 : CollatzResearch.WordTrace tailWord_147263 prefixEnd_147263 22404948629085204899335 := by
  unfold tailWord_147263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371122865498776363174443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3580748576999184242116295 5371122865498776363174443)
  ·
    refine ⟨8056684298248164544761665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5371122865498776363174443 8056684298248164544761665)
    ·
      refine ⟨6042513223686123408571249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8056684298248164544761665 6042513223686123408571249)
      ·
        refine ⟨4531884917764592556428437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6042513223686123408571249 4531884917764592556428437)
        ·
          refine ⟨212432105520215276082583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4531884917764592556428437 212432105520215276082583)
          ·
            refine ⟨318648158280322914123875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212432105520215276082583 318648158280322914123875)
            ·
              refine ⟨477972237420484371185813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318648158280322914123875 477972237420484371185813)
              ·
                refine ⟨22404948629085204899335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 477972237420484371185813 22404948629085204899335)
                ·
                  rfl

theorem cell20_147263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_147263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147263 prefixEnd_147263 := by exact prefixLift 147263
  have htrace : WordTrace (prefixWord ++ tailWord_147263) baseStart_147263 baseEnd_147263 := by
    simpa [prefixWord, tailWord_147263, baseEnd_147263] using wordTrace_append hprefix tailTrace_147263
  have hstable : (prefixWord ++ tailWord_147263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147263).length < 2 ^ (prefixWord ++ tailWord_147263).sum := by decide
  have hdescent : baseEnd_147263 < baseStart_147263 := by decide
  rcases family_descends (prefixWord ++ tailWord_147263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147322 : List Nat := [3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_147322 : Nat := 118140960795 + 147322 * 2 ^ 59
def prefixEnd_147322 : Nat := 4983230072969 + 3 ^ 40 * 147322 * 2
def baseEnd_147322 : Nat := 22413925031637877243699

theorem tailTrace_147322 : CollatzResearch.WordTrace tailWord_147322 prefixEnd_147322 22413925031637877243699 := by
  unfold tailWord_147322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343318693071257359893055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3582183181523352959714813 1343318693071257359893055)
  ·
    refine ⟨2014978039606886039839583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343318693071257359893055 2014978039606886039839583)
    ·
      refine ⟨3022467059410329059759375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014978039606886039839583 3022467059410329059759375)
      ·
        refine ⟨4533700589115493589639063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3022467059410329059759375 4533700589115493589639063)
        ·
          refine ⟨6800550883673240384458595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4533700589115493589639063 6800550883673240384458595)
          ·
            refine ⟨10200826325509860576687893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6800550883673240384458595 10200826325509860576687893)
            ·
              refine ⟨478163734008274714532245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10200826325509860576687893 478163734008274714532245)
              ·
                refine ⟨22413925031637877243699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 478163734008274714532245 22413925031637877243699)
                ·
                  rfl

theorem cell20_147322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_147322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147322 prefixEnd_147322 := by exact prefixLift 147322
  have htrace : WordTrace (prefixWord ++ tailWord_147322) baseStart_147322 baseEnd_147322 := by
    simpa [prefixWord, tailWord_147322, baseEnd_147322] using wordTrace_append hprefix tailTrace_147322
  have hstable : (prefixWord ++ tailWord_147322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147322).length < 2 ^ (prefixWord ++ tailWord_147322).sum := by decide
  have hdescent : baseEnd_147322 < baseStart_147322 := by decide
  rcases family_descends (prefixWord ++ tailWord_147322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147356 : List Nat := [2, 2, 3, 3, 1, 3, 1, 5]
def baseStart_147356 : Nat := 118140960795 + 147356 * 2 ^ 59
def prefixEnd_147356 : Nat := 4983230072969 + 3 ^ 40 * 147356 * 2
def baseEnd_147356 : Nat := 22419097873786874865875

theorem tailTrace_147356 : CollatzResearch.WordTrace tailWord_147356 prefixEnd_147356 22419097873786874865875 := by
  unfold tailWord_147356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687257427080926623154961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3583009902774568830873281 2687257427080926623154961)
  ·
    refine ⟨2015443070310694967366221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2687257427080926623154961 2015443070310694967366221)
    ·
      refine ⟨755791151366510612762333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2015443070310694967366221 755791151366510612762333)
      ·
        refine ⟨283421681762441479785875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 755791151366510612762333 283421681762441479785875)
        ·
          refine ⟨425132522643662219678813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283421681762441479785875 425132522643662219678813)
          ·
            refine ⟨159424695991373332379555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 425132522643662219678813 159424695991373332379555)
            ·
              refine ⟨239137043987059998569333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159424695991373332379555 239137043987059998569333)
              ·
                refine ⟨22419097873786874865875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239137043987059998569333 22419097873786874865875)
                ·
                  rfl

theorem cell20_147356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_147356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147356 prefixEnd_147356 := by exact prefixLift 147356
  have htrace : WordTrace (prefixWord ++ tailWord_147356) baseStart_147356 baseEnd_147356 := by
    simpa [prefixWord, tailWord_147356, baseEnd_147356] using wordTrace_append hprefix tailTrace_147356
  have hstable : (prefixWord ++ tailWord_147356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147356).length < 2 ^ (prefixWord ++ tailWord_147356).sum := by decide
  have hdescent : baseEnd_147356 < baseStart_147356 := by decide
  rcases family_descends (prefixWord ++ tailWord_147356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147408 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 2]
def baseStart_147408 : Nat := 118140960795 + 147408 * 2 ^ 59
def prefixEnd_147408 : Nat := 4983230072969 + 3 ^ 40 * 147408 * 2
def baseEnd_147408 : Nat := 67281027838279554864079

theorem tailTrace_147408 : CollatzResearch.WordTrace tailWord_147408 prefixEnd_147408 67281027838279554864079 := by
  unfold tailWord_147408
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688205724986733063601439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3584274299982310751468585 2688205724986733063601439)
  ·
    refine ⟨4032308587480099595402159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688205724986733063601439 4032308587480099595402159)
    ·
      refine ⟨6048462881220149393103239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4032308587480099595402159 6048462881220149393103239)
      ·
        refine ⟨9072694321830224089654859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048462881220149393103239 9072694321830224089654859)
        ·
          refine ⟨13609041482745336134482289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072694321830224089654859 13609041482745336134482289)
          ·
            refine ⟨10206781112059002100861717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13609041482745336134482289 10206781112059002100861717)
            ·
              refine ⟨478442864627765723477893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10206781112059002100861717 478442864627765723477893)
              ·
                refine ⟨89708037117706073152105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478442864627765723477893 89708037117706073152105)
                ·
                  refine ⟨67281027838279554864079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89708037117706073152105 67281027838279554864079)
                  ·
                    rfl

theorem cell20_147408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_147408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147408 prefixEnd_147408 := by exact prefixLift 147408
  have htrace : WordTrace (prefixWord ++ tailWord_147408) baseStart_147408 baseEnd_147408 := by
    simpa [prefixWord, tailWord_147408, baseEnd_147408] using wordTrace_append hprefix tailTrace_147408
  have hstable : (prefixWord ++ tailWord_147408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147408).length < 2 ^ (prefixWord ++ tailWord_147408).sum := by decide
  have hdescent : baseEnd_147408 < baseStart_147408 := by decide
  rcases family_descends (prefixWord ++ tailWord_147408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147418 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_147418 : Nat := 118140960795 + 147418 * 2 ^ 59
def prefixEnd_147418 : Nat := 4983230072969 + 3 ^ 40 * 147418 * 2
def baseEnd_147418 : Nat := 67285592110763964530705

theorem tailTrace_147418 : CollatzResearch.WordTrace tailWord_147418 prefixEnd_147418 67285592110763964530705 := by
  unfold tailWord_147418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344194044984309458766727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3584517453291491890044605 1344194044984309458766727)
  ·
    refine ⟨2016291067476464188150091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1344194044984309458766727 2016291067476464188150091)
    ·
      refine ⟨3024436601214696282225137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016291067476464188150091 3024436601214696282225137)
      ·
        refine ⟨2268327450911022211668853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3024436601214696282225137 2268327450911022211668853)
        ·
          refine ⟨212655698522908332343955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2268327450911022211668853 212655698522908332343955)
          ·
            refine ⟨318983547784362498515933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212655698522908332343955 318983547784362498515933)
            ·
              refine ⟨119618830419135936943475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318983547784362498515933 119618830419135936943475)
              ·
                refine ⟨179428245628703905415213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119618830419135936943475 179428245628703905415213)
                ·
                  refine ⟨67285592110763964530705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179428245628703905415213 67285592110763964530705)
                  ·
                    rfl

theorem cell20_147418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_147418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147418 prefixEnd_147418 := by exact prefixLift 147418
  have htrace : WordTrace (prefixWord ++ tailWord_147418) baseStart_147418 baseEnd_147418 := by
    simpa [prefixWord, tailWord_147418, baseEnd_147418] using wordTrace_append hprefix tailTrace_147418
  have hstable : (prefixWord ++ tailWord_147418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147418).length < 2 ^ (prefixWord ++ tailWord_147418).sum := by decide
  have hdescent : baseEnd_147418 < baseStart_147418 := by decide
  rcases family_descends (prefixWord ++ tailWord_147418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147469 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 3]
def baseStart_147469 : Nat := 118140960795 + 147469 * 2 ^ 59
def prefixEnd_147469 : Nat := 4983230072969 + 3 ^ 40 * 147469 * 2
def baseEnd_147469 : Nat := 67308869900434453830497

theorem tailTrace_147469 : CollatzResearch.WordTrace tailWord_147469 prefixEnd_147469 67308869900434453830497 := by
  unfold tailWord_147469
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378636302752473545173461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3585757535168315696782307 5378636302752473545173461)
  ·
    refine ⟨126061788345761098715003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5378636302752473545173461 126061788345761098715003)
    ·
      refine ⟨189092682518641648072505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126061788345761098715003 189092682518641648072505)
      ·
        refine ⟨141819511888981236054379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189092682518641648072505 141819511888981236054379)
        ·
          refine ⟨212729267833471854081569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141819511888981236054379 212729267833471854081569)
          ·
            refine ⟨159546950875103890561177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212729267833471854081569 159546950875103890561177)
            ·
              refine ⟨119660213156327917920883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159546950875103890561177 119660213156327917920883)
              ·
                refine ⟨179490319734491876881325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119660213156327917920883 179490319734491876881325)
                ·
                  refine ⟨67308869900434453830497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179490319734491876881325 67308869900434453830497)
                  ·
                    rfl

theorem cell20_147469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_147469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147469 prefixEnd_147469 := by exact prefixLift 147469
  have htrace : WordTrace (prefixWord ++ tailWord_147469) baseStart_147469 baseEnd_147469 := by
    simpa [prefixWord, tailWord_147469, baseEnd_147469] using wordTrace_append hprefix tailTrace_147469
  have hstable : (prefixWord ++ tailWord_147469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147469).length < 2 ^ (prefixWord ++ tailWord_147469).sum := by decide
  have hdescent : baseEnd_147469 < baseStart_147469 := by decide
  rcases family_descends (prefixWord ++ tailWord_147469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147477 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_147477 : Nat := 118140960795 + 147477 * 2 ^ 59
def prefixEnd_147477 : Nat := 4983230072969 + 3 ^ 40 * 147477 * 2
def baseEnd_147477 : Nat := 67312521318421981563797

theorem tailTrace_147477 : CollatzResearch.WordTrace tailWord_147477 prefixEnd_147477 67312521318421981563797 := by
  unfold tailWord_147477
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378928086723490911464685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3585952057815660607643123 5378928086723490911464685)
  ·
    refine ⟨2017098032521309091799257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5378928086723490911464685 2017098032521309091799257)
    ·
      refine ⟨1512823524390981818849443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2017098032521309091799257 1512823524390981818849443)
      ·
        refine ⟨2269235286586472728274165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512823524390981818849443 2269235286586472728274165)
        ·
          refine ⟨212740808117481818275703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2269235286586472728274165 212740808117481818275703)
          ·
            refine ⟨319111212176222727413555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212740808117481818275703 319111212176222727413555)
            ·
              refine ⟨478666818264334091120333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319111212176222727413555 478666818264334091120333)
              ·
                refine ⟨179500056849125284170125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478666818264334091120333 179500056849125284170125)
                ·
                  refine ⟨67312521318421981563797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179500056849125284170125 67312521318421981563797)
                  ·
                    rfl

theorem cell20_147477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_147477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147477 prefixEnd_147477 := by exact prefixLift 147477
  have htrace : WordTrace (prefixWord ++ tailWord_147477) baseStart_147477 baseEnd_147477 := by
    simpa [prefixWord, tailWord_147477, baseEnd_147477] using wordTrace_append hprefix tailTrace_147477
  have hstable : (prefixWord ++ tailWord_147477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147477).length < 2 ^ (prefixWord ++ tailWord_147477).sum := by decide
  have hdescent : baseEnd_147477 < baseStart_147477 := by decide
  rcases family_descends (prefixWord ++ tailWord_147477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147508 : List Nat := [2, 5, 1, 2, 3, 7]
def baseStart_147508 : Nat := 118140960795 + 147508 * 2 ^ 59
def prefixEnd_147508 : Nat := 4983230072969 + 3 ^ 40 * 147508 * 2
def baseEnd_147508 : Nat := 2493580391226801908531

theorem tailTrace_147508 : CollatzResearch.WordTrace tailWord_147508 prefixEnd_147508 2493580391226801908531 := by
  unfold tailWord_147508
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690029374805591602921589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3586705833074122137228785 2690029374805591602921589)
  ·
    refine ⟨252190253888024212773899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2690029374805591602921589 252190253888024212773899)
    ·
      refine ⟨378285380832036319160849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252190253888024212773899 378285380832036319160849)
      ·
        refine ⟨283714035624027239370637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378285380832036319160849 283714035624027239370637)
        ·
          refine ⟨106392763359010214763989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283714035624027239370637 106392763359010214763989)
          ·
            refine ⟨2493580391226801908531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 106392763359010214763989 2493580391226801908531)
            ·
              rfl

theorem cell20_147508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 7].length) (baseStart_147508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147508 prefixEnd_147508 := by exact prefixLift 147508
  have htrace : WordTrace (prefixWord ++ tailWord_147508) baseStart_147508 baseEnd_147508 := by
    simpa [prefixWord, tailWord_147508, baseEnd_147508] using wordTrace_append hprefix tailTrace_147508
  have hstable : (prefixWord ++ tailWord_147508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147508).length < 2 ^ (prefixWord ++ tailWord_147508).sum := by decide
  have hdescent : baseEnd_147508 < baseStart_147508 := by decide
  rcases family_descends (prefixWord ++ tailWord_147508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147512 : List Nat := [2, 1, 2, 1, 6, 8]
def baseStart_147512 : Nat := 118140960795 + 147512 * 2 ^ 59
def prefixEnd_147512 : Nat := 4983230072969 + 3 ^ 40 * 147512 * 2
def baseEnd_147512 : Nat := 2493648010078422792481

theorem tailTrace_147512 : CollatzResearch.WordTrace tailWord_147512 prefixEnd_147512 2493648010078422792481 := by
  unfold tailWord_147512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690102320798345944494395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3586803094397794592659193 2690102320798345944494395)
  ·
    refine ⟨4035153481197518916741593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2690102320798345944494395 4035153481197518916741593)
    ·
      refine ⟨3026365110898139187556195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4035153481197518916741593 3026365110898139187556195)
      ·
        refine ⟨4539547666347208781334293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026365110898139187556195 4539547666347208781334293)
        ·
          refine ⟨212791296860025411625045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4539547666347208781334293 212791296860025411625045)
          ·
            refine ⟨2493648010078422792481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 212791296860025411625045 2493648010078422792481)
            ·
              rfl

theorem cell20_147512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 8].length) (baseStart_147512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147512 prefixEnd_147512 := by exact prefixLift 147512
  have htrace : WordTrace (prefixWord ++ tailWord_147512) baseStart_147512 baseEnd_147512 := by
    simpa [prefixWord, tailWord_147512, baseEnd_147512] using wordTrace_append hprefix tailTrace_147512
  have hstable : (prefixWord ++ tailWord_147512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147512).length < 2 ^ (prefixWord ++ tailWord_147512).sum := by decide
  have hdescent : baseEnd_147512 < baseStart_147512 := by decide
  rcases family_descends (prefixWord ++ tailWord_147512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147518 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_147518 : Nat := 118140960795 + 147518 * 2 ^ 59
def prefixEnd_147518 : Nat := 4983230072969 + 3 ^ 40 * 147518 * 2
def baseEnd_147518 : Nat := 67331234835608061196963

theorem tailTrace_147518 : CollatzResearch.WordTrace tailWord_147518 prefixEnd_147518 67331234835608061196963 := by
  unfold tailWord_147518
  simp only [CollatzResearch.WordTrace]
  refine ⟨672552934946869364213401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3586948986383303275804805 672552934946869364213401)
  ·
    refine ⟨504414701210152023160051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 672552934946869364213401 504414701210152023160051)
    ·
      refine ⟨756622051815228034740077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504414701210152023160051 756622051815228034740077)
      ·
        refine ⟨283733269430710513027529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 756622051815228034740077 283733269430710513027529)
        ·
          refine ⟨212799952073032884770647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283733269430710513027529 212799952073032884770647)
          ·
            refine ⟨319199928109549327155971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212799952073032884770647 319199928109549327155971)
            ·
              refine ⟨478799892164323990733957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319199928109549327155971 478799892164323990733957)
              ·
                refine ⟨89774979780810748262617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478799892164323990733957 89774979780810748262617)
                ·
                  refine ⟨67331234835608061196963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89774979780810748262617 67331234835608061196963)
                  ·
                    rfl

theorem cell20_147518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_147518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147518 prefixEnd_147518 := by exact prefixLift 147518
  have htrace : WordTrace (prefixWord ++ tailWord_147518) baseStart_147518 baseEnd_147518 := by
    simpa [prefixWord, tailWord_147518, baseEnd_147518] using wordTrace_append hprefix tailTrace_147518
  have hstable : (prefixWord ++ tailWord_147518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147518).length < 2 ^ (prefixWord ++ tailWord_147518).sum := by decide
  have hdescent : baseEnd_147518 < baseStart_147518 := by decide
  rcases family_descends (prefixWord ++ tailWord_147518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147519 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_147519 : Nat := 118140960795 + 147519 * 2 ^ 59
def prefixEnd_147519 : Nat := 4983230072969 + 3 ^ 40 * 147519 * 2
def baseEnd_147519 : Nat := 67331691262856502163625

theorem tailTrace_147519 : CollatzResearch.WordTrace tailWord_147519 prefixEnd_147519 67331691262856502163625 := by
  unfold tailWord_147519
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380459952571332084493611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3586973301714221389662407 5380459952571332084493611)
  ·
    refine ⟨8070689928856998126740417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5380459952571332084493611 8070689928856998126740417)
    ·
      refine ⟨6053017446642748595055313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8070689928856998126740417 6053017446642748595055313)
      ·
        refine ⟨4539763084982061446291485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6053017446642748595055313 4539763084982061446291485)
        ·
          refine ⟨1702411156868273042359307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4539763084982061446291485 1702411156868273042359307)
          ·
            refine ⟨2553616735302409563538961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702411156868273042359307 2553616735302409563538961)
            ·
              refine ⟨1915212551476807172654221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2553616735302409563538961 1915212551476807172654221)
              ·
                refine ⟨718204706803802689745333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1915212551476807172654221 718204706803802689745333)
                ·
                  refine ⟨67331691262856502163625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 718204706803802689745333 67331691262856502163625)
                  ·
                    rfl

theorem cell20_147519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_147519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147519 prefixEnd_147519 := by exact prefixLift 147519
  have htrace : WordTrace (prefixWord ++ tailWord_147519) baseStart_147519 baseEnd_147519 := by
    simpa [prefixWord, tailWord_147519, baseEnd_147519] using wordTrace_append hprefix tailTrace_147519
  have hstable : (prefixWord ++ tailWord_147519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147519).length < 2 ^ (prefixWord ++ tailWord_147519).sum := by decide
  have hdescent : baseEnd_147519 < baseStart_147519 := by decide
  rcases family_descends (prefixWord ++ tailWord_147519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147581 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_147581 : Nat := 118140960795 + 147581 * 2 ^ 59
def prefixEnd_147581 : Nat := 4983230072969 + 3 ^ 40 * 147581 * 2
def baseEnd_147581 : Nat := 67359989752259842096705

theorem tailTrace_147581 : CollatzResearch.WordTrace tailWord_147581 prefixEnd_147581 67359989752259842096705 := by
  unfold tailWord_147581
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382721278346716673250597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3588480852231144448833731 5382721278346716673250597)
  ·
    refine ⟨1009260239690009376234487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5382721278346716673250597 1009260239690009376234487)
    ·
      refine ⟨1513890359535014064351731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009260239690009376234487 1513890359535014064351731)
      ·
        refine ⟨2270835539302521096527597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513890359535014064351731 2270835539302521096527597)
        ·
          refine ⟨851563327238445411197849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2270835539302521096527597 851563327238445411197849)
          ·
            refine ⟨638672495428834058398387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 851563327238445411197849 638672495428834058398387)
            ·
              refine ⟨958008743143251087597581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638672495428834058398387 958008743143251087597581)
              ·
                refine ⟨359253278678719157849093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 958008743143251087597581 359253278678719157849093)
                ·
                  refine ⟨67359989752259842096705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359253278678719157849093 67359989752259842096705)
                  ·
                    rfl

theorem cell20_147581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_147581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147581 prefixEnd_147581 := by exact prefixLift 147581
  have htrace : WordTrace (prefixWord ++ tailWord_147581) baseStart_147581 baseEnd_147581 := by
    simpa [prefixWord, tailWord_147581, baseEnd_147581] using wordTrace_append hprefix tailTrace_147581
  have hstable : (prefixWord ++ tailWord_147581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147581).length < 2 ^ (prefixWord ++ tailWord_147581).sum := by decide
  have hdescent : baseEnd_147581 < baseStart_147581 := by decide
  rcases family_descends (prefixWord ++ tailWord_147581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147588 : List Nat := [2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_147588 : Nat := 118140960795 + 147588 * 2 ^ 59
def prefixEnd_147588 : Nat := 4983230072969 + 3 ^ 40 * 147588 * 2
def baseEnd_147588 : Nat := 22454394914332976287781

theorem tailTrace_147588 : CollatzResearch.WordTrace tailWord_147588 prefixEnd_147588 22454394914332976287781 := by
  unfold tailWord_147588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691488294660678434377709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3588651059547571245836945 2691488294660678434377709)
  ·
    refine ⟨1009308110497754412891641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2691488294660678434377709 1009308110497754412891641)
    ·
      refine ⟨756981082873315809668731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1009308110497754412891641 756981082873315809668731)
      ·
        refine ⟨1135471624309973714503097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756981082873315809668731 1135471624309973714503097)
        ·
          refine ⟨851603718232480285877323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135471624309973714503097 851603718232480285877323)
          ·
            refine ⟨1277405577348720428815985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851603718232480285877323 1277405577348720428815985)
            ·
              refine ⟨958054183011540321611989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277405577348720428815985 958054183011540321611989)
              ·
                refine ⟨22454394914332976287781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 958054183011540321611989 22454394914332976287781)
                ·
                  rfl

theorem cell20_147588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_147588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147588 prefixEnd_147588 := by exact prefixLift 147588
  have htrace : WordTrace (prefixWord ++ tailWord_147588) baseStart_147588 baseEnd_147588 := by
    simpa [prefixWord, tailWord_147588, baseEnd_147588] using wordTrace_append hprefix tailTrace_147588
  have hstable : (prefixWord ++ tailWord_147588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147588).length < 2 ^ (prefixWord ++ tailWord_147588).sum := by decide
  have hdescent : baseEnd_147588 < baseStart_147588 := by decide
  rcases family_descends (prefixWord ++ tailWord_147588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147615 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 2]
def baseStart_147615 : Nat := 118140960795 + 147615 * 2 ^ 59
def prefixEnd_147615 : Nat := 4983230072969 + 3 ^ 40 * 147615 * 2
def baseEnd_147615 : Nat := 67375508278706834963233

theorem tailTrace_147615 : CollatzResearch.WordTrace tailWord_147615 prefixEnd_147615 67375508278706834963233 := by
  unfold tailWord_147615
  simp only [CollatzResearch.WordTrace]
  refine ⟨5383961360223540479988299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3589307573482360319992199 5383961360223540479988299)
  ·
    refine ⟨8075942040335310719982449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5383961360223540479988299 8075942040335310719982449)
    ·
      refine ⟨6056956530251483039986837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8075942040335310719982449 6056956530251483039986837)
      ·
        refine ⟨283919837355538267499383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6056956530251483039986837 283919837355538267499383)
        ·
          refine ⟨425879756033307401249075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283919837355538267499383 425879756033307401249075)
          ·
            refine ⟨638819634049961101873613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425879756033307401249075 638819634049961101873613)
            ·
              refine ⟨239557362768735413202605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 638819634049961101873613 239557362768735413202605)
              ·
                refine ⟨89834011038275779950977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239557362768735413202605 89834011038275779950977)
                ·
                  refine ⟨67375508278706834963233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89834011038275779950977 67375508278706834963233)
                  ·
                    rfl

theorem cell20_147615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 2].length) (baseStart_147615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147615 prefixEnd_147615 := by exact prefixLift 147615
  have htrace : WordTrace (prefixWord ++ tailWord_147615) baseStart_147615 baseEnd_147615 := by
    simpa [prefixWord, tailWord_147615, baseEnd_147615] using wordTrace_append hprefix tailTrace_147615
  have hstable : (prefixWord ++ tailWord_147615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147615).length < 2 ^ (prefixWord ++ tailWord_147615).sum := by decide
  have hdescent : baseEnd_147615 < baseStart_147615 := by decide
  rcases family_descends (prefixWord ++ tailWord_147615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147688 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_147688 : Nat := 118140960795 + 147688 * 2 ^ 59
def prefixEnd_147688 : Nat := 4983230072969 + 3 ^ 40 * 147688 * 2
def baseEnd_147688 : Nat := 67408827467843025529601

theorem tailTrace_147688 : CollatzResearch.WordTrace tailWord_147688 prefixEnd_147688 67408827467843025529601 := by
  unfold tailWord_147688
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693311944479536973697859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3591082592639382631597145 2693311944479536973697859)
  ·
    refine ⟨4039967916719305460546789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693311944479536973697859 4039967916719305460546789)
    ·
      refine ⟨757493984384869773852523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4039967916719305460546789 757493984384869773852523)
      ·
        refine ⟨1136240976577304660778785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757493984384869773852523 1136240976577304660778785)
        ·
          refine ⟨852180732432978495584089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136240976577304660778785 852180732432978495584089)
          ·
            refine ⟨639135549324733871688067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852180732432978495584089 639135549324733871688067)
            ·
              refine ⟨958703323987100807532101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639135549324733871688067 958703323987100807532101)
              ·
                refine ⟨179756873247581401412269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 958703323987100807532101 179756873247581401412269)
                ·
                  refine ⟨67408827467843025529601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179756873247581401412269 67408827467843025529601)
                  ·
                    rfl

theorem cell20_147688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_147688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147688 prefixEnd_147688 := by exact prefixLift 147688
  have htrace : WordTrace (prefixWord ++ tailWord_147688) baseStart_147688 baseEnd_147688 := by
    simpa [prefixWord, tailWord_147688, baseEnd_147688] using wordTrace_append hprefix tailTrace_147688
  have hstable : (prefixWord ++ tailWord_147688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147688).length < 2 ^ (prefixWord ++ tailWord_147688).sum := by decide
  have hdescent : baseEnd_147688 < baseStart_147688 := by decide
  rcases family_descends (prefixWord ++ tailWord_147688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147743 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 3]
def baseStart_147743 : Nat := 118140960795 + 147743 * 2 ^ 59
def prefixEnd_147743 : Nat := 4983230072969 + 3 ^ 40 * 147743 * 2
def baseEnd_147743 : Nat := 67433930966507278696043

theorem tailTrace_147743 : CollatzResearch.WordTrace tailWord_147743 prefixEnd_147743 67433930966507278696043 := by
  unfold tailWord_147743
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388629903759818340647883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3592419935839878893765255 5388629903759818340647883)
  ·
    refine ⟨8082944855639727510971825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5388629903759818340647883 8082944855639727510971825)
    ·
      refine ⟨6062208641729795633228869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8082944855639727510971825 6062208641729795633228869)
      ·
        refine ⟨1136664120324336681230413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6062208641729795633228869 1136664120324336681230413)
        ·
          refine ⟨426249045121626255461405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1136664120324336681230413 426249045121626255461405)
          ·
            refine ⟨159843391920609845798027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 426249045121626255461405 159843391920609845798027)
            ·
              refine ⟨239765087880914768697041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159843391920609845798027 239765087880914768697041)
              ·
                refine ⟨179823815910686076522781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239765087880914768697041 179823815910686076522781)
                ·
                  refine ⟨67433930966507278696043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179823815910686076522781 67433930966507278696043)
                  ·
                    rfl

theorem cell20_147743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_147743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147743 prefixEnd_147743 := by exact prefixLift 147743
  have htrace : WordTrace (prefixWord ++ tailWord_147743) baseStart_147743 baseEnd_147743 := by
    simpa [prefixWord, tailWord_147743, baseEnd_147743] using wordTrace_append hprefix tailTrace_147743
  have hstable : (prefixWord ++ tailWord_147743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147743).length < 2 ^ (prefixWord ++ tailWord_147743).sum := by decide
  have hdescent : baseEnd_147743 < baseStart_147743 := by decide
  rcases family_descends (prefixWord ++ tailWord_147743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147747 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_147747 : Nat := 118140960795 + 147747 * 2 ^ 59
def prefixEnd_147747 : Nat := 4983230072969 + 3 ^ 40 * 147747 * 2
def baseEnd_147747 : Nat := 67435756675501042562693

theorem tailTrace_147747 : CollatzResearch.WordTrace tailWord_147747 prefixEnd_147747 67435756675501042562693 := by
  unfold tailWord_147747
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388775795745327023793495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3592517197163551349195663 5388775795745327023793495)
  ·
    refine ⟨8083163693617990535690243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5388775795745327023793495 8083163693617990535690243)
    ·
      refine ⟨12124745540426985803535365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8083163693617990535690243 12124745540426985803535365)
      ·
        refine ⟨2273389788830059838162881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12124745540426985803535365 2273389788830059838162881)
        ·
          refine ⟨1705042341622544878622161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273389788830059838162881 1705042341622544878622161)
          ·
            refine ⟨1278781756216908658966621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1705042341622544878622161 1278781756216908658966621)
            ·
              refine ⟨479543158581340747112483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278781756216908658966621 479543158581340747112483)
              ·
                refine ⟨719314737872011120668725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479543158581340747112483 719314737872011120668725)
                ·
                  refine ⟨67435756675501042562693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 719314737872011120668725 67435756675501042562693)
                  ·
                    rfl

theorem cell20_147747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_147747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147747 prefixEnd_147747 := by exact prefixLift 147747
  have htrace : WordTrace (prefixWord ++ tailWord_147747) baseStart_147747 baseEnd_147747 := by
    simpa [prefixWord, tailWord_147747, baseEnd_147747] using wordTrace_append hprefix tailTrace_147747
  have hstable : (prefixWord ++ tailWord_147747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147747).length < 2 ^ (prefixWord ++ tailWord_147747).sum := by decide
  have hdescent : baseEnd_147747 < baseStart_147747 := by decide
  rcases family_descends (prefixWord ++ tailWord_147747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147774 : List Nat := [4, 2, 1, 2, 1, 4, 2, 4]
def baseStart_147774 : Nat := 118140960795 + 147774 * 2 ^ 59
def prefixEnd_147774 : Nat := 4983230072969 + 3 ^ 40 * 147774 * 2
def baseEnd_147774 : Nat := 22482693403736316220861

theorem tailTrace_147774 : CollatzResearch.WordTrace tailWord_147774 prefixEnd_147774 22482693403736316220861 := by
  unfold tailWord_147774
  simp only [CollatzResearch.WordTrace]
  refine ⟨673720070830938829378297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3593173711098340423350917 673720070830938829378297)
  ·
    refine ⟨505290053123204122033723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 673720070830938829378297 505290053123204122033723)
    ·
      refine ⟨757935079684806183050585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505290053123204122033723 757935079684806183050585)
      ·
        refine ⟨568451309763604637287939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 757935079684806183050585 568451309763604637287939)
        ·
          refine ⟨852676964645406955931909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568451309763604637287939 852676964645406955931909)
          ·
            refine ⟨159876930871013804237233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 852676964645406955931909 159876930871013804237233)
            ·
              refine ⟨119907698153260353177925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159876930871013804237233 119907698153260353177925)
              ·
                refine ⟨22482693403736316220861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119907698153260353177925 22482693403736316220861)
                ·
                  rfl

theorem cell20_147774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_147774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147774 prefixEnd_147774 := by exact prefixLift 147774
  have htrace : WordTrace (prefixWord ++ tailWord_147774) baseStart_147774 baseEnd_147774 := by
    simpa [prefixWord, tailWord_147774, baseEnd_147774] using wordTrace_append hprefix tailTrace_147774
  have hstable : (prefixWord ++ tailWord_147774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147774).length < 2 ^ (prefixWord ++ tailWord_147774).sum := by decide
  have hdescent : baseEnd_147774 < baseStart_147774 := by decide
  rcases family_descends (prefixWord ++ tailWord_147774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147816 : List Nat := [2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_147816 : Nat := 118140960795 + 147816 * 2 ^ 59
def prefixEnd_147816 : Nat := 4983230072969 + 3 ^ 40 * 147816 * 2
def baseEnd_147816 : Nat := 22489083385214489754137

theorem tailTrace_147816 : CollatzResearch.WordTrace tailWord_147816 prefixEnd_147816 22489083385214489754137 := by
  unfold tailWord_147816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695646216247675904027651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3594194954996901205370201 2695646216247675904027651)
  ·
    refine ⟨4043469324371513856041477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2695646216247675904027651 4043469324371513856041477)
    ·
      refine ⟨758150498319658848007777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4043469324371513856041477 758150498319658848007777)
      ·
        refine ⟨568612873739744136005833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758150498319658848007777 568612873739744136005833)
        ·
          refine ⟨426459655304808102004375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568612873739744136005833 426459655304808102004375)
          ·
            refine ⟨639689482957212153006563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426459655304808102004375 639689482957212153006563)
            ·
              refine ⟨959534224435818229509845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639689482957212153006563 959534224435818229509845)
              ·
                refine ⟨22489083385214489754137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 959534224435818229509845 22489083385214489754137)
                ·
                  rfl

theorem cell20_147816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_147816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147816 prefixEnd_147816 := by exact prefixLift 147816
  have htrace : WordTrace (prefixWord ++ tailWord_147816) baseStart_147816 baseEnd_147816 := by
    simpa [prefixWord, tailWord_147816, baseEnd_147816] using wordTrace_append hprefix tailTrace_147816
  have hstable : (prefixWord ++ tailWord_147816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147816).length < 2 ^ (prefixWord ++ tailWord_147816).sum := by decide
  have hdescent : baseEnd_147816 < baseStart_147816 := by decide
  rcases family_descends (prefixWord ++ tailWord_147816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147854 : List Nat := [4, 1, 1, 4, 1, 9]
def baseStart_147854 : Nat := 118140960795 + 147854 * 2 ^ 59
def prefixEnd_147854 : Nat := 4983230072969 + 3 ^ 40 * 147854 * 2
def baseEnd_147854 : Nat := 2499429421892008370207

theorem tailTrace_147854 : CollatzResearch.WordTrace tailWord_147854 prefixEnd_147854 2499429421892008370207 := by
  unfold tailWord_147854
  simp only [CollatzResearch.WordTrace]
  refine ⟨674084800794710537242327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3595118937571789531959077 674084800794710537242327)
  ·
    refine ⟨1011127201192065805863491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674084800794710537242327 1011127201192065805863491)
    ·
      refine ⟨1516690801788098708795237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011127201192065805863491 1516690801788098708795237)
      ·
        refine ⟨284379525335268507899107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1516690801788098708795237 284379525335268507899107)
        ·
          refine ⟨426569288002902761848661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284379525335268507899107 426569288002902761848661)
          ·
            refine ⟨2499429421892008370207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 426569288002902761848661 2499429421892008370207)
            ·
              rfl

theorem cell20_147854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 9].length) (baseStart_147854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147854 prefixEnd_147854 := by exact prefixLift 147854
  have htrace : WordTrace (prefixWord ++ tailWord_147854) baseStart_147854 baseEnd_147854 := by
    simpa [prefixWord, tailWord_147854, baseEnd_147854] using wordTrace_append hprefix tailTrace_147854
  have hstable : (prefixWord ++ tailWord_147854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147854).length < 2 ^ (prefixWord ++ tailWord_147854).sum := by decide
  have hdescent : baseEnd_147854 < baseStart_147854 := by decide
  rcases family_descends (prefixWord ++ tailWord_147854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147902 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_147902 : Nat := 118140960795 + 147902 * 2 ^ 59
def prefixEnd_147902 : Nat := 4983230072969 + 3 ^ 40 * 147902 * 2
def baseEnd_147902 : Nat := 67506502899009392395393

theorem tailTrace_147902 : CollatzResearch.WordTrace tailWord_147902 prefixEnd_147902 67506502899009392395393 := by
  unfold tailWord_147902
  simp only [CollatzResearch.WordTrace]
  refine ⟨674303638772973561960745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3596286073455858997123973 674303638772973561960745)
  ·
    refine ⟨505727729079730171470559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 674303638772973561960745 505727729079730171470559)
    ·
      refine ⟨758591593619595257205839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505727729079730171470559 758591593619595257205839)
      ·
        refine ⟨1137887390429392885808759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758591593619595257205839 1137887390429392885808759)
        ·
          refine ⟨1706831085644089328713139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137887390429392885808759 1706831085644089328713139)
          ·
            refine ⟨2560246628466133993069709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706831085644089328713139 2560246628466133993069709)
            ·
              refine ⟨960092485674800247401141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2560246628466133993069709 960092485674800247401141)
              ·
                refine ⟨90008670532012523193857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 960092485674800247401141 90008670532012523193857)
                ·
                  refine ⟨67506502899009392395393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90008670532012523193857 67506502899009392395393)
                  ·
                    rfl

theorem cell20_147902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_147902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147902 prefixEnd_147902 := by exact prefixLift 147902
  have htrace : WordTrace (prefixWord ++ tailWord_147902) baseStart_147902 baseEnd_147902 := by
    simpa [prefixWord, tailWord_147902, baseEnd_147902] using wordTrace_append hprefix tailTrace_147902
  have hstable : (prefixWord ++ tailWord_147902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147902).length < 2 ^ (prefixWord ++ tailWord_147902).sum := by decide
  have hdescent : baseEnd_147902 < baseStart_147902 := by decide
  rcases family_descends (prefixWord ++ tailWord_147902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147916 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_147916 : Nat := 118140960795 + 147916 * 2 ^ 59
def prefixEnd_147916 : Nat := 4983230072969 + 3 ^ 40 * 147916 * 2
def baseEnd_147916 : Nat := 67512892880487565928669

theorem tailTrace_147916 : CollatzResearch.WordTrace tailWord_147916 prefixEnd_147916 67512892880487565928669 := by
  unfold tailWord_147916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697469866066534443347801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3596626488088712591130401 2697469866066534443347801)
  ·
    refine ⟨2023102399549900832510851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2697469866066534443347801 2023102399549900832510851)
    ·
      refine ⟨3034653599324851248766277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023102399549900832510851 3034653599324851248766277)
      ·
        refine ⟨568997549873409609143677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3034653599324851248766277 568997549873409609143677)
        ·
          refine ⟨213374081202528603428879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 568997549873409609143677 213374081202528603428879)
          ·
            refine ⟨320061121803792905143319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213374081202528603428879 320061121803792905143319)
            ·
              refine ⟨480091682705689357714979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320061121803792905143319 480091682705689357714979)
              ·
                refine ⟨720137524058534036572469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480091682705689357714979 720137524058534036572469)
                ·
                  refine ⟨67512892880487565928669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720137524058534036572469 67512892880487565928669)
                  ·
                    rfl

theorem cell20_147916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_147916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147916 prefixEnd_147916 := by exact prefixLift 147916
  have htrace : WordTrace (prefixWord ++ tailWord_147916) baseStart_147916 baseEnd_147916 := by
    simpa [prefixWord, tailWord_147916, baseEnd_147916] using wordTrace_append hprefix tailTrace_147916
  have hstable : (prefixWord ++ tailWord_147916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147916).length < 2 ^ (prefixWord ++ tailWord_147916).sum := by decide
  have hdescent : baseEnd_147916 < baseStart_147916 := by decide
  rcases family_descends (prefixWord ++ tailWord_147916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147933 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 3]
def baseStart_147933 : Nat := 118140960795 + 147933 * 2 ^ 59
def prefixEnd_147933 : Nat := 4983230072969 + 3 ^ 40 * 147933 * 2
def baseEnd_147933 : Nat := 67520652143711062361933

theorem tailTrace_147933 : CollatzResearch.WordTrace tailWord_147933 prefixEnd_147933 67520652143711062361933 := by
  unfold tailWord_147933
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395559773071480790064453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3597039848714320526709635 5395559773071480790064453)
  ·
    refine ⟨1011667457450902648137085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5395559773071480790064453 1011667457450902648137085)
    ·
      refine ⟨379375296544088493051407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1011667457450902648137085 379375296544088493051407)
      ·
        refine ⟨569062944816132739577111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379375296544088493051407 569062944816132739577111)
        ·
          refine ⟨853594417224199109365667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569062944816132739577111 853594417224199109365667)
          ·
            refine ⟨1280391625836298664048501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853594417224199109365667 1280391625836298664048501)
            ·
              refine ⟨120036714922152999754547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1280391625836298664048501 120036714922152999754547)
              ·
                refine ⟨180055072383229499631821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120036714922152999754547 180055072383229499631821)
                ·
                  refine ⟨67520652143711062361933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180055072383229499631821 67520652143711062361933)
                  ·
                    rfl

theorem cell20_147933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_147933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147933 prefixEnd_147933 := by exact prefixLift 147933
  have htrace : WordTrace (prefixWord ++ tailWord_147933) baseStart_147933 baseEnd_147933 := by
    simpa [prefixWord, tailWord_147933, baseEnd_147933] using wordTrace_append hprefix tailTrace_147933
  have hstable : (prefixWord ++ tailWord_147933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147933).length < 2 ^ (prefixWord ++ tailWord_147933).sum := by decide
  have hdescent : baseEnd_147933 < baseStart_147933 := by decide
  rcases family_descends (prefixWord ++ tailWord_147933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147974 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_147974 : Nat := 118140960795 + 147974 * 2 ^ 59
def prefixEnd_147974 : Nat := 4983230072969 + 3 ^ 40 * 147974 * 2
def baseEnd_147974 : Nat := 67539365660897141995099

theorem tailTrace_147974 : CollatzResearch.WordTrace tailWord_147974 prefixEnd_147974 67539365660897141995099 := by
  unfold tailWord_147974
  simp only [CollatzResearch.WordTrace]
  refine ⟨168657973935092024759593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3598036777281963194871317 168657973935092024759593)
  ·
    refine ⟨126493480451319018569695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168657973935092024759593 126493480451319018569695)
    ·
      refine ⟨189740220676978527854543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126493480451319018569695 189740220676978527854543)
      ·
        refine ⟨284610331015467791781815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189740220676978527854543 284610331015467791781815)
        ·
          refine ⟨426915496523201687672723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284610331015467791781815 426915496523201687672723)
          ·
            refine ⟨640373244784802531509085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426915496523201687672723 640373244784802531509085)
            ·
              refine ⟨240139966794300949315907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 640373244784802531509085 240139966794300949315907)
              ·
                refine ⟨360209950191451423973861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240139966794300949315907 360209950191451423973861)
                ·
                  refine ⟨67539365660897141995099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360209950191451423973861 67539365660897141995099)
                  ·
                    rfl

theorem cell20_147974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_147974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147974 prefixEnd_147974 := by exact prefixLift 147974
  have htrace : WordTrace (prefixWord ++ tailWord_147974) baseStart_147974 baseEnd_147974 := by
    simpa [prefixWord, tailWord_147974, baseEnd_147974] using wordTrace_append hprefix tailTrace_147974
  have hstable : (prefixWord ++ tailWord_147974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147974).length < 2 ^ (prefixWord ++ tailWord_147974).sum := by decide
  have hdescent : baseEnd_147974 < baseStart_147974 := by decide
  rcases family_descends (prefixWord ++ tailWord_147974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147988 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_147988 : Nat := 118140960795 + 147988 * 2 ^ 59
def prefixEnd_147988 : Nat := 4983230072969 + 3 ^ 40 * 147988 * 2
def baseEnd_147988 : Nat := 67545755642375315528375

theorem tailTrace_147988 : CollatzResearch.WordTrace tailWord_147988 prefixEnd_147988 67545755642375315528375 := by
  unfold tailWord_147988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698782893936112591658309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3598377191914816788877745 2698782893936112591658309)
  ·
    refine ⟨506021792613021110935933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2698782893936112591658309 506021792613021110935933)
    ·
      refine ⟨189758172229882916600975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 506021792613021110935933 189758172229882916600975)
      ·
        refine ⟨284637258344824374901463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189758172229882916600975 284637258344824374901463)
        ·
          refine ⟨426955887517236562352195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284637258344824374901463 426955887517236562352195)
          ·
            refine ⟨640433831275854843528293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426955887517236562352195 640433831275854843528293)
            ·
              refine ⟨120081343364222783161555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 640433831275854843528293 120081343364222783161555)
              ·
                refine ⟨180122015046334174742333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120081343364222783161555 180122015046334174742333)
                ·
                  refine ⟨67545755642375315528375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180122015046334174742333 67545755642375315528375)
                  ·
                    rfl

theorem cell20_147988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_147988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147988 prefixEnd_147988 := by exact prefixLift 147988
  have htrace : WordTrace (prefixWord ++ tailWord_147988) baseStart_147988 baseEnd_147988 := by
    simpa [prefixWord, tailWord_147988, baseEnd_147988] using wordTrace_append hprefix tailTrace_147988
  have hstable : (prefixWord ++ tailWord_147988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147988).length < 2 ^ (prefixWord ++ tailWord_147988).sum := by decide
  have hdescent : baseEnd_147988 < baseStart_147988 := by decide
  rcases family_descends (prefixWord ++ tailWord_147988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147992 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_147992 : Nat := 118140960795 + 147992 * 2 ^ 59
def prefixEnd_147992 : Nat := 4983230072969 + 3 ^ 40 * 147992 * 2
def baseEnd_147992 : Nat := 67547581351369079395025

theorem tailTrace_147992 : CollatzResearch.WordTrace tailWord_147992 prefixEnd_147992 67547581351369079395025 := by
  unfold tailWord_147992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698855839928866933231115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3598474453238489244308153 2698855839928866933231115)
  ·
    refine ⟨4048283759893300399846673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2698855839928866933231115 4048283759893300399846673)
    ·
      refine ⟨3036212819919975299885005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4048283759893300399846673 3036212819919975299885005)
      ·
        refine ⟨1138579807469990737456877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3036212819919975299885005 1138579807469990737456877)
        ·
          refine ⟨426967427801246526546329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1138579807469990737456877 426967427801246526546329)
          ·
            refine ⟨320225570850934894909747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426967427801246526546329 320225570850934894909747)
            ·
              refine ⟨480338356276402342364621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320225570850934894909747 480338356276402342364621)
              ·
                refine ⟨180126883603650878386733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480338356276402342364621 180126883603650878386733)
                ·
                  refine ⟨67547581351369079395025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180126883603650878386733 67547581351369079395025)
                  ·
                    rfl

theorem cell20_147992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_147992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_147992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_147992 prefixEnd_147992 := by exact prefixLift 147992
  have htrace : WordTrace (prefixWord ++ tailWord_147992) baseStart_147992 baseEnd_147992 := by
    simpa [prefixWord, tailWord_147992, baseEnd_147992] using wordTrace_append hprefix tailTrace_147992
  have hstable : (prefixWord ++ tailWord_147992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147992).length < 2 ^ (prefixWord ++ tailWord_147992).sum := by decide
  have hdescent : baseEnd_147992 < baseStart_147992 := by decide
  rcases family_descends (prefixWord ++ tailWord_147992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148033 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 2]
def baseStart_148033 : Nat := 118140960795 + 148033 * 2 ^ 59
def prefixEnd_148033 : Nat := 4983230072969 + 3 ^ 40 * 148033 * 2
def baseEnd_148033 : Nat := 67566294868555159028191

theorem tailTrace_148033 : CollatzResearch.WordTrace tailWord_148033 prefixEnd_148033 67566294868555159028191 := by
  unfold tailWord_148033
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399207072709197868704753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3599471381806131912469835 5399207072709197868704753)
  ·
    refine ⟨4049405304531898401528565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5399207072709197868704753 4049405304531898401528565)
    ·
      refine ⟨379631747299865475143303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4049405304531898401528565 379631747299865475143303)
      ·
        refine ⟨569447620949798212714955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379631747299865475143303 569447620949798212714955)
        ·
          refine ⟨854171431424697319072433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569447620949798212714955 854171431424697319072433)
          ·
            refine ⟨640628573568522989304325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854171431424697319072433 640628573568522989304325)
            ·
              refine ⟨120117857544098060494561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 640628573568522989304325 120117857544098060494561)
              ·
                refine ⟨90088393158073545370921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120117857544098060494561 90088393158073545370921)
                ·
                  refine ⟨67566294868555159028191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90088393158073545370921 67566294868555159028191)
                  ·
                    rfl

theorem cell20_148033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_148033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148033 prefixEnd_148033 := by exact prefixLift 148033
  have htrace : WordTrace (prefixWord ++ tailWord_148033) baseStart_148033 baseEnd_148033 := by
    simpa [prefixWord, tailWord_148033, baseEnd_148033] using wordTrace_append hprefix tailTrace_148033
  have hstable : (prefixWord ++ tailWord_148033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148033).length < 2 ^ (prefixWord ++ tailWord_148033).sum := by decide
  have hdescent : baseEnd_148033 < baseStart_148033 := by decide
  rcases family_descends (prefixWord ++ tailWord_148033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148036 : List Nat := [2, 3, 5, 1, 2, 1, 1, 5]
def baseStart_148036 : Nat := 118140960795 + 148036 * 2 ^ 59
def prefixEnd_148036 : Nat := 4983230072969 + 3 ^ 40 * 148036 * 2
def baseEnd_148036 : Nat := 22522554716766827309393

theorem tailTrace_148036 : CollatzResearch.WordTrace tailWord_148036 prefixEnd_148036 22522554716766827309393 := by
  unfold tailWord_148036
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699658245849164690531981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3599544327798886254042641 2699658245849164690531981)
  ·
    refine ⟨1012371842193436758949493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2699658245849164690531981 1012371842193436758949493)
    ·
      refine ⟨94909860205634696151515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1012371842193436758949493 94909860205634696151515)
      ·
        refine ⟨142364790308452044227273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94909860205634696151515 142364790308452044227273)
        ·
          refine ⟨106773592731339033170455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142364790308452044227273 106773592731339033170455)
          ·
            refine ⟨160160389097008549755683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106773592731339033170455 160160389097008549755683)
            ·
              refine ⟨240240583645512824633525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160160389097008549755683 240240583645512824633525)
              ·
                refine ⟨22522554716766827309393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240240583645512824633525 22522554716766827309393)
                ·
                  rfl

theorem cell20_148036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_148036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148036 prefixEnd_148036 := by exact prefixLift 148036
  have htrace : WordTrace (prefixWord ++ tailWord_148036) baseStart_148036 baseEnd_148036 := by
    simpa [prefixWord, tailWord_148036, baseEnd_148036] using wordTrace_append hprefix tailTrace_148036
  have hstable : (prefixWord ++ tailWord_148036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148036).length < 2 ^ (prefixWord ++ tailWord_148036).sum := by decide
  have hdescent : baseEnd_148036 < baseStart_148036 := by decide
  rcases family_descends (prefixWord ++ tailWord_148036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148082 : List Nat := [3, 2, 1, 2, 4, 1, 7]
def baseStart_148082 : Nat := 118140960795 + 148082 * 2 ^ 59
def prefixEnd_148082 : Nat := 4983230072969 + 3 ^ 40 * 148082 * 2
def baseEnd_148082 : Nat := 7509851089303196266073

theorem tailTrace_148082 : CollatzResearch.WordTrace tailWord_148082 prefixEnd_148082 7509851089303196266073 := by
  unfold tailWord_148082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350248562382919809309625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3600662833021119491492333 1350248562382919809309625)
  ·
    refine ⟨1012686421787189856982219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1350248562382919809309625 1012686421787189856982219)
    ·
      refine ⟨1519029632680784785473329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1012686421787189856982219 1519029632680784785473329)
      ·
        refine ⟨1139272224510588589104997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1519029632680784785473329 1139272224510588589104997)
        ·
          refine ⟨213613542095735360457187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1139272224510588589104997 213613542095735360457187)
          ·
            refine ⟨320420313143603040685781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213613542095735360457187 320420313143603040685781)
            ·
              refine ⟨7509851089303196266073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 320420313143603040685781 7509851089303196266073)
              ·
                rfl

theorem cell20_148082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 7].length) (baseStart_148082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148082 prefixEnd_148082 := by exact prefixLift 148082
  have htrace : WordTrace (prefixWord ++ tailWord_148082) baseStart_148082 baseEnd_148082 := by
    simpa [prefixWord, tailWord_148082, baseEnd_148082] using wordTrace_append hprefix tailTrace_148082
  have hstable : (prefixWord ++ tailWord_148082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148082).length < 2 ^ (prefixWord ++ tailWord_148082).sum := by decide
  have hdescent : baseEnd_148082 < baseStart_148082 := by decide
  rcases family_descends (prefixWord ++ tailWord_148082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148089 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_148089 : Nat := 118140960795 + 148089 * 2 ^ 59
def prefixEnd_148089 : Nat := 4983230072969 + 3 ^ 40 * 148089 * 2
def baseEnd_148089 : Nat := 67591854794467853161295

theorem tailTrace_148089 : CollatzResearch.WordTrace tailWord_148089 prefixEnd_148089 67591854794467853161295 := by
  unfold tailWord_148089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401249560506319432743321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3600833040337546288495547 5401249560506319432743321)
  ·
    refine ⟨4050937170379739574557491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5401249560506319432743321 4050937170379739574557491)
    ·
      refine ⟨6076405755569609361836237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050937170379739574557491 6076405755569609361836237)
      ·
        refine ⟨2278652158338603510688589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6076405755569609361836237 2278652158338603510688589)
        ·
          refine ⟨854494559376976316508221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2278652158338603510688589 854494559376976316508221)
          ·
            refine ⟨320435459766366118690583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 854494559376976316508221 320435459766366118690583)
            ·
              refine ⟨480653189649549178035875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320435459766366118690583 480653189649549178035875)
              ·
                refine ⟨720979784474323767053813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480653189649549178035875 720979784474323767053813)
                ·
                  refine ⟨67591854794467853161295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720979784474323767053813 67591854794467853161295)
                  ·
                    rfl

theorem cell20_148089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_148089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148089 prefixEnd_148089 := by exact prefixLift 148089
  have htrace : WordTrace (prefixWord ++ tailWord_148089) baseStart_148089 baseEnd_148089 := by
    simpa [prefixWord, tailWord_148089, baseEnd_148089] using wordTrace_append hprefix tailTrace_148089
  have hstable : (prefixWord ++ tailWord_148089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148089).length < 2 ^ (prefixWord ++ tailWord_148089).sum := by decide
  have hdescent : baseEnd_148089 < baseStart_148089 := by decide
  rcases family_descends (prefixWord ++ tailWord_148089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148096 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_148096 : Nat := 118140960795 + 148096 * 2 ^ 59
def prefixEnd_148096 : Nat := 4983230072969 + 3 ^ 40 * 148096 * 2
def baseEnd_148096 : Nat := 67595049785206939927933

theorem tailTrace_148096 : CollatzResearch.WordTrace tailWord_148096 prefixEnd_148096 67595049785206939927933 := by
  unfold tailWord_148096
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700752435740479814124071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3601003247653973085498761 2700752435740479814124071)
  ·
    refine ⟨4051128653610719721186107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2700752435740479814124071 4051128653610719721186107)
    ·
      refine ⟨6076692980416079581779161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051128653610719721186107 6076692980416079581779161)
      ·
        refine ⟨4557519735312059686334371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6076692980416079581779161 4557519735312059686334371)
        ·
          refine ⟨6836279602968089529501557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557519735312059686334371 6836279602968089529501557)
          ·
            refine ⟨640901212778258393390771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6836279602968089529501557 640901212778258393390771)
            ·
              refine ⟨961351819167387590086157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640901212778258393390771 961351819167387590086157)
              ·
                refine ⟨360506932187770346282309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 961351819167387590086157 360506932187770346282309)
                ·
                  refine ⟨67595049785206939927933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360506932187770346282309 67595049785206939927933)
                  ·
                    rfl

theorem cell20_148096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_148096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148096 prefixEnd_148096 := by exact prefixLift 148096
  have htrace : WordTrace (prefixWord ++ tailWord_148096) baseStart_148096 baseEnd_148096 := by
    simpa [prefixWord, tailWord_148096, baseEnd_148096] using wordTrace_append hprefix tailTrace_148096
  have hstable : (prefixWord ++ tailWord_148096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148096).length < 2 ^ (prefixWord ++ tailWord_148096).sum := by decide
  have hdescent : baseEnd_148096 < baseStart_148096 := by decide
  rcases family_descends (prefixWord ++ tailWord_148096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148098 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_148098 : Nat := 118140960795 + 148098 * 2 ^ 59
def prefixEnd_148098 : Nat := 4983230072969 + 3 ^ 40 * 148098 * 2
def baseEnd_148098 : Nat := 67595962639703821861259

theorem tailTrace_148098 : CollatzResearch.WordTrace tailWord_148098 prefixEnd_148098 67595962639703821861259 := by
  unfold tailWord_148098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350394454368428492455237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3601051878315809313213965 1350394454368428492455237)
  ·
    refine ⟨253198960194080342335357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1350394454368428492455237 253198960194080342335357)
    ·
      refine ⟨94949610072780128375759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253198960194080342335357 94949610072780128375759)
      ·
        refine ⟨142424415109170192563639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94949610072780128375759 142424415109170192563639)
        ·
          refine ⟨213636622663755288845459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142424415109170192563639 213636622663755288845459)
          ·
            refine ⟨320454933995632933268189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213636622663755288845459 320454933995632933268189)
            ·
              refine ⟨120170600248362349975571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320454933995632933268189 120170600248362349975571)
              ·
                refine ⟨180255900372543524963357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120170600248362349975571 180255900372543524963357)
                ·
                  refine ⟨67595962639703821861259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180255900372543524963357 67595962639703821861259)
                  ·
                    rfl

theorem cell20_148098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_148098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148098 prefixEnd_148098 := by exact prefixLift 148098
  have htrace : WordTrace (prefixWord ++ tailWord_148098) baseStart_148098 baseEnd_148098 := by
    simpa [prefixWord, tailWord_148098, baseEnd_148098] using wordTrace_append hprefix tailTrace_148098
  have hstable : (prefixWord ++ tailWord_148098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148098).length < 2 ^ (prefixWord ++ tailWord_148098).sum := by decide
  have hdescent : baseEnd_148098 < baseStart_148098 := by decide
  rcases family_descends (prefixWord ++ tailWord_148098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148103 : List Nat := [1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_148103 : Nat := 118140960795 + 148103 * 2 ^ 59
def prefixEnd_148103 : Nat := 4983230072969 + 3 ^ 40 * 148103 * 2
def baseEnd_148103 : Nat := 22532748258648675564857

theorem tailTrace_148103 : CollatzResearch.WordTrace tailWord_148103 prefixEnd_148103 22532748258648675564857 := by
  unfold tailWord_148103
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401760182455599823752963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3601173454970399882501975 5401760182455599823752963)
  ·
    refine ⟨8102640273683399735629445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5401760182455599823752963 8102640273683399735629445)
    ·
      refine ⟨1519245051315637450430521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8102640273683399735629445 1519245051315637450430521)
      ·
        refine ⟨1139433788486728087822891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1519245051315637450430521 1139433788486728087822891)
        ·
          refine ⟨1709150682730092131734337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139433788486728087822891 1709150682730092131734337)
          ·
            refine ⟨1281863012047569098800753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709150682730092131734337 1281863012047569098800753)
            ·
              refine ⟨961397259035676824100565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281863012047569098800753 961397259035676824100565)
              ·
                refine ⟨22532748258648675564857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 961397259035676824100565 22532748258648675564857)
                ·
                  rfl

theorem cell20_148103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_148103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148103 prefixEnd_148103 := by exact prefixLift 148103
  have htrace : WordTrace (prefixWord ++ tailWord_148103) baseStart_148103 baseEnd_148103 := by
    simpa [prefixWord, tailWord_148103, baseEnd_148103] using wordTrace_append hprefix tailTrace_148103
  have hstable : (prefixWord ++ tailWord_148103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148103).length < 2 ^ (prefixWord ++ tailWord_148103).sum := by decide
  have hdescent : baseEnd_148103 < baseStart_148103 := by decide
  rcases family_descends (prefixWord ++ tailWord_148103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148116 : List Nat := [2, 4, 2, 2, 1, 3, 2, 4]
def baseStart_148116 : Nat := 118140960795 + 148116 * 2 ^ 59
def prefixEnd_148116 : Nat := 4983230072969 + 3 ^ 40 * 148116 * 2
def baseEnd_148116 : Nat := 22534726110058586420395

theorem tailTrace_148116 : CollatzResearch.WordTrace tailWord_148116 prefixEnd_148116 22534726110058586420395 := by
  unfold tailWord_148116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701117165704251521988101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3601489554272335362650801 2701117165704251521988101)
  ·
    refine ⟨506459468569547160372769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2701117165704251521988101 506459468569547160372769)
    ·
      refine ⟨379844601427160370279577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 506459468569547160372769 379844601427160370279577)
      ·
        refine ⟨284883451070370277709683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379844601427160370279577 284883451070370277709683)
        ·
          refine ⟨427325176605555416564525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284883451070370277709683 427325176605555416564525)
          ·
            refine ⟨160246941227083281211697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427325176605555416564525 160246941227083281211697)
            ·
              refine ⟨120185205920312460908773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160246941227083281211697 120185205920312460908773)
              ·
                refine ⟨22534726110058586420395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120185205920312460908773 22534726110058586420395)
                ·
                  rfl

theorem cell20_148116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_148116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148116 prefixEnd_148116 := by exact prefixLift 148116
  have htrace : WordTrace (prefixWord ++ tailWord_148116) baseStart_148116 baseEnd_148116 := by
    simpa [prefixWord, tailWord_148116, baseEnd_148116] using wordTrace_append hprefix tailTrace_148116
  have hstable : (prefixWord ++ tailWord_148116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148116).length < 2 ^ (prefixWord ++ tailWord_148116).sum := by decide
  have hdescent : baseEnd_148116 < baseStart_148116 := by decide
  rcases family_descends (prefixWord ++ tailWord_148116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148158 : List Nat := [4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_148158 : Nat := 118140960795 + 148158 * 2 ^ 59
def prefixEnd_148158 : Nat := 4983230072969 + 3 ^ 40 * 148158 * 2
def baseEnd_148158 : Nat := 22541116091536759953671

theorem tailTrace_148158 : CollatzResearch.WordTrace tailWord_148158 prefixEnd_148158 22541116091536759953671 := by
  unfold tailWord_148158
  simp only [CollatzResearch.WordTrace]
  refine ⟨675470774657043027125641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3602510798170896144670085 675470774657043027125641)
  ·
    refine ⟨506603080992782270344231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 675470774657043027125641 506603080992782270344231)
    ·
      refine ⟨759904621489173405516347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506603080992782270344231 759904621489173405516347)
      ·
        refine ⟨1139856932233760108274521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759904621489173405516347 1139856932233760108274521)
        ·
          refine ⟨854892699175320081205891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1139856932233760108274521 854892699175320081205891)
          ·
            refine ⟨1282339048762980121808837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854892699175320081205891 1282339048762980121808837)
            ·
              refine ⟨240438571643058772839157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1282339048762980121808837 240438571643058772839157)
              ·
                refine ⟨22541116091536759953671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240438571643058772839157 22541116091536759953671)
                ·
                  rfl

theorem cell20_148158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_148158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148158 prefixEnd_148158 := by exact prefixLift 148158
  have htrace : WordTrace (prefixWord ++ tailWord_148158) baseStart_148158 baseEnd_148158 := by
    simpa [prefixWord, tailWord_148158, baseEnd_148158] using wordTrace_append hprefix tailTrace_148158
  have hstable : (prefixWord ++ tailWord_148158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148158).length < 2 ^ (prefixWord ++ tailWord_148158).sum := by decide
  have hdescent : baseEnd_148158 < baseStart_148158 := by decide
  rcases family_descends (prefixWord ++ tailWord_148158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148206 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_148206 : Nat := 118140960795 + 148206 * 2 ^ 59
def prefixEnd_148206 : Nat := 4983230072969 + 3 ^ 40 * 148206 * 2
def baseEnd_148206 : Nat := 67645256782535446260817

theorem tailTrace_148206 : CollatzResearch.WordTrace tailWord_148206 prefixEnd_148206 67645256782535446260817 := by
  unfold tailWord_148206
  simp only [CollatzResearch.WordTrace]
  refine ⟨675689612635306051844059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3603677934054965609834981 675689612635306051844059)
  ·
    refine ⟨1013534418952959077766089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 675689612635306051844059 1013534418952959077766089)
    ·
      refine ⟨760150814214719308324567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013534418952959077766089 760150814214719308324567)
      ·
        refine ⟨1140226221322078962486851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760150814214719308324567 1140226221322078962486851)
        ·
          refine ⟨1710339331983118443730277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140226221322078962486851 1710339331983118443730277)
          ·
            refine ⟨320688624746834708199427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1710339331983118443730277 320688624746834708199427)
            ·
              refine ⟨481032937120252062299141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320688624746834708199427 481032937120252062299141)
              ·
                refine ⟨90193675710047261681089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481032937120252062299141 90193675710047261681089)
                ·
                  refine ⟨67645256782535446260817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90193675710047261681089 67645256782535446260817)
                  ·
                    rfl

theorem cell20_148206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_148206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148206 prefixEnd_148206 := by exact prefixLift 148206
  have htrace : WordTrace (prefixWord ++ tailWord_148206) baseStart_148206 baseEnd_148206 := by
    simpa [prefixWord, tailWord_148206, baseEnd_148206] using wordTrace_append hprefix tailTrace_148206
  have hstable : (prefixWord ++ tailWord_148206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148206).length < 2 ^ (prefixWord ++ tailWord_148206).sum := by decide
  have hdescent : baseEnd_148206 < baseStart_148206 := by decide
  rcases family_descends (prefixWord ++ tailWord_148206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148234 : List Nat := [3, 1, 2, 2, 1, 2, 5, 4]
def baseStart_148234 : Nat := 118140960795 + 148234 * 2 ^ 59
def prefixEnd_148234 : Nat := 4983230072969 + 3 ^ 40 * 148234 * 2
def baseEnd_148234 : Nat := 22552678915163931109123

theorem tailTrace_148234 : CollatzResearch.WordTrace tailWord_148234 prefixEnd_148234 22552678915163931109123 := by
  unfold tailWord_148234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351634536245252299192939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3604358763320672797847837 1351634536245252299192939)
  ·
    refine ⟨2027451804367878448789409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1351634536245252299192939 2027451804367878448789409)
    ·
      refine ⟨1520588853275908836592057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027451804367878448789409 1520588853275908836592057)
      ·
        refine ⟨1140441639956931627444043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520588853275908836592057 1140441639956931627444043)
        ·
          refine ⟨1710662459935397441166065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140441639956931627444043 1710662459935397441166065)
          ·
            refine ⟨1282996844951548080874549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710662459935397441166065 1282996844951548080874549)
            ·
              refine ⟨120280954214207632581989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1282996844951548080874549 120280954214207632581989)
              ·
                refine ⟨22552678915163931109123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120280954214207632581989 22552678915163931109123)
                ·
                  rfl

theorem cell20_148234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_148234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148234 prefixEnd_148234 := by exact prefixLift 148234
  have htrace : WordTrace (prefixWord ++ tailWord_148234) baseStart_148234 baseEnd_148234 := by
    simpa [prefixWord, tailWord_148234, baseEnd_148234] using wordTrace_append hprefix tailTrace_148234
  have hstable : (prefixWord ++ tailWord_148234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148234).length < 2 ^ (prefixWord ++ tailWord_148234).sum := by decide
  have hdescent : baseEnd_148234 < baseStart_148234 := by decide
  rcases family_descends (prefixWord ++ tailWord_148234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148255 : List Nat := [1, 1, 2, 4, 2, 3, 7]
def baseStart_148255 : Nat := 118140960795 + 148255 * 2 ^ 59
def prefixEnd_148255 : Nat := 4983230072969 + 3 ^ 40 * 148255 * 2
def baseEnd_148255 : Nat := 7518624635301005958587

theorem tailTrace_148255 : CollatzResearch.WordTrace tailWord_148255 prefixEnd_148255 7518624635301005958587 := by
  unfold tailWord_148255
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407304077904929783286219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3604869385269953188857479 5407304077904929783286219)
  ·
    refine ⟨8110956116857394674929329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5407304077904929783286219 8110956116857394674929329)
    ·
      refine ⟨6083217087643046006196997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8110956116857394674929329 6083217087643046006196997)
      ·
        refine ⟨1140603203933071126161937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6083217087643046006196997 1140603203933071126161937)
        ·
          refine ⟨855452402949803344621453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140603203933071126161937 855452402949803344621453)
          ·
            refine ⟨320794651106176254233045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 855452402949803344621453 320794651106176254233045)
            ·
              refine ⟨7518624635301005958587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 320794651106176254233045 7518624635301005958587)
              ·
                rfl

theorem cell20_148255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_148255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148255 prefixEnd_148255 := by exact prefixLift 148255
  have htrace : WordTrace (prefixWord ++ tailWord_148255) baseStart_148255 baseEnd_148255 := by
    simpa [prefixWord, tailWord_148255, baseEnd_148255] using wordTrace_append hprefix tailTrace_148255
  have hstable : (prefixWord ++ tailWord_148255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148255).length < 2 ^ (prefixWord ++ tailWord_148255).sum := by decide
  have hdescent : baseEnd_148255 < baseStart_148255 := by decide
  rcases family_descends (prefixWord ++ tailWord_148255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148258 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_148258 : Nat := 118140960795 + 148258 * 2 ^ 59
def prefixEnd_148258 : Nat := 4983230072969 + 3 ^ 40 * 148258 * 2
def baseEnd_148258 : Nat := 67668990999454376527271

theorem tailTrace_148258 : CollatzResearch.WordTrace tailWord_148258 prefixEnd_148258 67668990999454376527271 := by
  unfold tailWord_148258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351853374223515323911357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3604942331262707530430285 1351853374223515323911357)
  ·
    refine ⟨506945015333818246466759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1351853374223515323911357 506945015333818246466759)
    ·
      refine ⟨760417523000727369700139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506945015333818246466759 760417523000727369700139)
      ·
        refine ⟨1140626284501091054550209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760417523000727369700139 1140626284501091054550209)
        ·
          refine ⟨855469713375818290912657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140626284501091054550209 855469713375818290912657)
          ·
            refine ⟨641602285031863718184493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855469713375818290912657 641602285031863718184493)
            ·
              refine ⟨240600856886948894319185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641602285031863718184493 240600856886948894319185)
              ·
                refine ⟨180450642665211670739389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240600856886948894319185 180450642665211670739389)
                ·
                  refine ⟨67668990999454376527271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180450642665211670739389 67668990999454376527271)
                  ·
                    rfl

theorem cell20_148258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_148258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148258 prefixEnd_148258 := by exact prefixLift 148258
  have htrace : WordTrace (prefixWord ++ tailWord_148258) baseStart_148258 baseEnd_148258 := by
    simpa [prefixWord, tailWord_148258, baseEnd_148258] using wordTrace_append hprefix tailTrace_148258
  have hstable : (prefixWord ++ tailWord_148258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148258).length < 2 ^ (prefixWord ++ tailWord_148258).sum := by decide
  have hdescent : baseEnd_148258 < baseStart_148258 := by decide
  rcases family_descends (prefixWord ++ tailWord_148258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148289 : List Nat := [1, 2, 5, 3, 1, 1, 1, 6]
def baseStart_148289 : Nat := 118140960795 + 148289 * 2 ^ 59
def prefixEnd_148289 : Nat := 4983230072969 + 3 ^ 40 * 148289 * 2
def baseEnd_148289 : Nat := 22561046748052015497937

theorem tailTrace_148289 : CollatzResearch.WordTrace tailWord_148289 prefixEnd_148289 22561046748052015497937 := by
  unfold tailWord_148289
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408544159781753590023921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3605696106521169060015947 5408544159781753590023921)
  ·
    refine ⟨4056408119836315192517941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5408544159781753590023921 4056408119836315192517941)
    ·
      refine ⟨380288261234654549298557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4056408119836315192517941 380288261234654549298557)
      ·
        refine ⟨142608097962995455986959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380288261234654549298557 142608097962995455986959)
        ·
          refine ⟨213912146944493183980439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142608097962995455986959 213912146944493183980439)
          ·
            refine ⟨320868220416739775970659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213912146944493183980439 320868220416739775970659)
            ·
              refine ⟨481302330625109663955989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320868220416739775970659 481302330625109663955989)
              ·
                refine ⟨22561046748052015497937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481302330625109663955989 22561046748052015497937)
                ·
                  rfl

theorem cell20_148289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_148289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148289 prefixEnd_148289 := by exact prefixLift 148289
  have htrace : WordTrace (prefixWord ++ tailWord_148289) baseStart_148289 baseEnd_148289 := by
    simpa [prefixWord, tailWord_148289, baseEnd_148289] using wordTrace_append hprefix tailTrace_148289
  have hstable : (prefixWord ++ tailWord_148289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148289).length < 2 ^ (prefixWord ++ tailWord_148289).sum := by decide
  have hdescent : baseEnd_148289 < baseStart_148289 := by decide
  rcases family_descends (prefixWord ++ tailWord_148289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148307 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_148307 : Nat := 118140960795 + 148307 * 2 ^ 59
def prefixEnd_148307 : Nat := 4983230072969 + 3 ^ 40 * 148307 * 2
def baseEnd_148307 : Nat := 67691355934627983893737

theorem tailTrace_148307 : CollatzResearch.WordTrace tailWord_148307 prefixEnd_148307 67691355934627983893737 := by
  unfold tailWord_148307
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409200673716542664179175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3606133782477695109452783 5409200673716542664179175)
  ·
    refine ⟨8113801010574813996268763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409200673716542664179175 8113801010574813996268763)
    ·
      refine ⟨12170701515862220994403145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8113801010574813996268763 12170701515862220994403145)
      ·
        refine ⟨9128026136896665745802359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12170701515862220994403145 9128026136896665745802359)
        ·
          refine ⟨13692039205344998618703539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9128026136896665745802359 13692039205344998618703539)
          ·
            refine ⟨20538058808017497928055309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13692039205344998618703539 20538058808017497928055309)
            ·
              refine ⟨7701772053006561723020741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20538058808017497928055309 7701772053006561723020741)
              ·
                refine ⟨1444082259938730323066389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7701772053006561723020741 1444082259938730323066389)
                ·
                  refine ⟨67691355934627983893737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1444082259938730323066389 67691355934627983893737)
                  ·
                    rfl

theorem cell20_148307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_148307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148307 prefixEnd_148307 := by exact prefixLift 148307
  have htrace : WordTrace (prefixWord ++ tailWord_148307) baseStart_148307 baseEnd_148307 := by
    simpa [prefixWord, tailWord_148307, baseEnd_148307] using wordTrace_append hprefix tailTrace_148307
  have hstable : (prefixWord ++ tailWord_148307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148307).length < 2 ^ (prefixWord ++ tailWord_148307).sum := by decide
  have hdescent : baseEnd_148307 < baseStart_148307 := by decide
  rcases family_descends (prefixWord ++ tailWord_148307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148320 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 2]
def baseStart_148320 : Nat := 118140960795 + 148320 * 2 ^ 59
def prefixEnd_148320 : Nat := 4983230072969 + 3 ^ 40 * 148320 * 2
def baseEnd_148320 : Nat := 67697289488857716460351

theorem tailTrace_148320 : CollatzResearch.WordTrace tailWord_148320 prefixEnd_148320 67697289488857716460351 := by
  unfold tailWord_148320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704837411334722942201207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3606449881779630589601609 2704837411334722942201207)
  ·
    refine ⟨4057256117002084413301811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2704837411334722942201207 4057256117002084413301811)
    ·
      refine ⟨6085884175503126619952717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4057256117002084413301811 6085884175503126619952717)
      ·
        refine ⟨2282206565813672482482269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6085884175503126619952717 2282206565813672482482269)
        ·
          refine ⟨855827462180127180930851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2282206565813672482482269 855827462180127180930851)
          ·
            refine ⟨1283741193270190771396277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855827462180127180930851 1283741193270190771396277)
            ·
              refine ⟨120350736869080384818401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1283741193270190771396277 120350736869080384818401)
              ·
                refine ⟨90263052651810288613801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120350736869080384818401 90263052651810288613801)
                ·
                  refine ⟨67697289488857716460351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90263052651810288613801 67697289488857716460351)
                  ·
                    rfl

theorem cell20_148320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_148320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148320 prefixEnd_148320 := by exact prefixLift 148320
  have htrace : WordTrace (prefixWord ++ tailWord_148320) baseStart_148320 baseEnd_148320 := by
    simpa [prefixWord, tailWord_148320, baseEnd_148320] using wordTrace_append hprefix tailTrace_148320
  have hstable : (prefixWord ++ tailWord_148320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148320).length < 2 ^ (prefixWord ++ tailWord_148320).sum := by decide
  have hdescent : baseEnd_148320 < baseStart_148320 := by decide
  rcases family_descends (prefixWord ++ tailWord_148320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148372 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_148372 : Nat := 118140960795 + 148372 * 2 ^ 59
def prefixEnd_148372 : Nat := 4983230072969 + 3 ^ 40 * 148372 * 2
def baseEnd_148372 : Nat := 67721023705776646726805

theorem tailTrace_148372 : CollatzResearch.WordTrace tailWord_148372 prefixEnd_148372 67721023705776646726805 := by
  unfold tailWord_148372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2705785709240529382647685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3607714278987372510196913 2705785709240529382647685)
  ·
    refine ⟨507334820482599259246441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2705785709240529382647685 507334820482599259246441)
    ·
      refine ⟨380501115361949444434831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 507334820482599259246441 380501115361949444434831)
      ·
        refine ⟨570751673042924166652247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380501115361949444434831 570751673042924166652247)
        ·
          refine ⟨856127509564386249978371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570751673042924166652247 856127509564386249978371)
          ·
            refine ⟨1284191264346579374967557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856127509564386249978371 1284191264346579374967557)
            ·
              refine ⟨240785862064983632806417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1284191264346579374967557 240785862064983632806417)
              ·
                refine ⟨180589396548737724604813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240785862064983632806417 180589396548737724604813)
                ·
                  refine ⟨67721023705776646726805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180589396548737724604813 67721023705776646726805)
                  ·
                    rfl

theorem cell20_148372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_148372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148372 prefixEnd_148372 := by exact prefixLift 148372
  have htrace : WordTrace (prefixWord ++ tailWord_148372) baseStart_148372 baseEnd_148372 := by
    simpa [prefixWord, tailWord_148372, baseEnd_148372] using wordTrace_append hprefix tailTrace_148372
  have hstable : (prefixWord ++ tailWord_148372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148372).length < 2 ^ (prefixWord ++ tailWord_148372).sum := by decide
  have hdescent : baseEnd_148372 < baseStart_148372 := by decide
  rcases family_descends (prefixWord ++ tailWord_148372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148386 : List Nat := [3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_148386 : Nat := 118140960795 + 148386 * 2 ^ 59
def prefixEnd_148386 : Nat := 4983230072969 + 3 ^ 40 * 148386 * 2
def baseEnd_148386 : Nat := 22575804562418273420027

theorem tailTrace_148386 : CollatzResearch.WordTrace tailWord_148386 prefixEnd_148386 22575804562418273420027 := by
  unfold tailWord_148386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353020510107584789076253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3608054693620226104203341 1353020510107584789076253)
  ·
    refine ⟨507382691290344295903595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1353020510107584789076253 507382691290344295903595)
    ·
      refine ⟨761074036935516443855393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507382691290344295903595 761074036935516443855393)
      ·
        refine ⟨570805527701637332891545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 761074036935516443855393 570805527701637332891545)
        ·
          refine ⟨428104145776227999668659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570805527701637332891545 428104145776227999668659)
          ·
            refine ⟨642156218664341999502989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428104145776227999668659 642156218664341999502989)
            ·
              refine ⟨240808581999128249813621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642156218664341999502989 240808581999128249813621)
              ·
                refine ⟨22575804562418273420027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240808581999128249813621 22575804562418273420027)
                ·
                  rfl

theorem cell20_148386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_148386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148386 prefixEnd_148386 := by exact prefixLift 148386
  have htrace : WordTrace (prefixWord ++ tailWord_148386) baseStart_148386 baseEnd_148386 := by
    simpa [prefixWord, tailWord_148386, baseEnd_148386] using wordTrace_append hprefix tailTrace_148386
  have hstable : (prefixWord ++ tailWord_148386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148386).length < 2 ^ (prefixWord ++ tailWord_148386).sum := by decide
  have hdescent : baseEnd_148386 < baseStart_148386 := by decide
  rcases family_descends (prefixWord ++ tailWord_148386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148431 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_148431 : Nat := 118140960795 + 148431 * 2 ^ 59
def prefixEnd_148431 : Nat := 4983230072969 + 3 ^ 40 * 148431 * 2
def baseEnd_148431 : Nat := 67747952913434663759897

theorem tailTrace_148431 : CollatzResearch.WordTrace tailWord_148431 prefixEnd_148431 67747952913434663759897 := by
  unfold tailWord_148431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413723325267311841693147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3609148883511541227795431 5413723325267311841693147)
  ·
    refine ⟨8120584987900967762539721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5413723325267311841693147 8120584987900967762539721)
    ·
      refine ⟨6090438740925725821904791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8120584987900967762539721 6090438740925725821904791)
      ·
        refine ⟨9135658111388588732857187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6090438740925725821904791 9135658111388588732857187)
        ·
          refine ⟨13703487167082883099285781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9135658111388588732857187 13703487167082883099285781)
          ·
            refine ⟨642350960957010145279021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13703487167082883099285781 642350960957010145279021)
            ·
              refine ⟨240881610358878804479633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642350960957010145279021 240881610358878804479633)
              ·
                refine ⟨180661207769159103359725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240881610358878804479633 180661207769159103359725)
                ·
                  refine ⟨67747952913434663759897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180661207769159103359725 67747952913434663759897)
                  ·
                    rfl

theorem cell20_148431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_148431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148431 prefixEnd_148431 := by exact prefixLift 148431
  have htrace : WordTrace (prefixWord ++ tailWord_148431) baseStart_148431 baseEnd_148431 := by
    simpa [prefixWord, tailWord_148431, baseEnd_148431] using wordTrace_append hprefix tailTrace_148431
  have hstable : (prefixWord ++ tailWord_148431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148431).length < 2 ^ (prefixWord ++ tailWord_148431).sum := by decide
  have hdescent : baseEnd_148431 < baseStart_148431 := by decide
  rcases family_descends (prefixWord ++ tailWord_148431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148434 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_148434 : Nat := 118140960795 + 148434 * 2 ^ 59
def prefixEnd_148434 : Nat := 4983230072969 + 3 ^ 40 * 148434 * 2
def baseEnd_148434 : Nat := 67749322195179986659885

theorem tailTrace_148434 : CollatzResearch.WordTrace tailWord_148434 prefixEnd_148434 67749322195179986659885 := by
  unfold tailWord_148434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353458186064110838513089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3609221829504295569368237 1353458186064110838513089)
  ·
    refine ⟨1015093639548083128884817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1353458186064110838513089 1015093639548083128884817)
    ·
      refine ⟨761320229661062346663613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1015093639548083128884817 761320229661062346663613)
      ·
        refine ⟨285495086122898379998855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 761320229661062346663613 285495086122898379998855)
        ·
          refine ⟨428242629184347569998283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285495086122898379998855 428242629184347569998283)
          ·
            refine ⟨642363943776521354997425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428242629184347569998283 642363943776521354997425)
            ·
              refine ⟨481772957832391016248069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642363943776521354997425 481772957832391016248069)
              ·
                refine ⟨90332429593573315546513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481772957832391016248069 90332429593573315546513)
                ·
                  refine ⟨67749322195179986659885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90332429593573315546513 67749322195179986659885)
                  ·
                    rfl

theorem cell20_148434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_148434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148434 prefixEnd_148434 := by exact prefixLift 148434
  have htrace : WordTrace (prefixWord ++ tailWord_148434) baseStart_148434 baseEnd_148434 := by
    simpa [prefixWord, tailWord_148434, baseEnd_148434] using wordTrace_append hprefix tailTrace_148434
  have hstable : (prefixWord ++ tailWord_148434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148434).length < 2 ^ (prefixWord ++ tailWord_148434).sum := by decide
  have hdescent : baseEnd_148434 < baseStart_148434 := by decide
  rcases family_descends (prefixWord ++ tailWord_148434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148462 : List Nat := [4, 1, 2, 1, 4, 1, 1, 6]
def baseStart_148462 : Nat := 118140960795 + 148462 * 2 ^ 59
def prefixEnd_148462 : Nat := 4983230072969 + 3 ^ 40 * 148462 * 2
def baseEnd_148462 : Nat := 22587367386045444575479

theorem tailTrace_148462 : CollatzResearch.WordTrace tailWord_148462 prefixEnd_148462 22587367386045444575479 := by
  unfold tailWord_148462
  simp only [CollatzResearch.WordTrace]
  refine ⟨676856748519375517008955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3609902658770002757381093 676856748519375517008955)
  ·
    refine ⟨1015285122779063275513433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676856748519375517008955 1015285122779063275513433)
    ·
      refine ⟨761463842084297456635075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1015285122779063275513433 761463842084297456635075)
      ·
        refine ⟨1142195763126446184952613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761463842084297456635075 1142195763126446184952613)
        ·
          refine ⟨214161705586208659678615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1142195763126446184952613 214161705586208659678615)
          ·
            refine ⟨321242558379312989517923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214161705586208659678615 321242558379312989517923)
            ·
              refine ⟨481863837568969484276885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321242558379312989517923 481863837568969484276885)
              ·
                refine ⟨22587367386045444575479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481863837568969484276885 22587367386045444575479)
                ·
                  rfl

theorem cell20_148462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_148462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148462 prefixEnd_148462 := by exact prefixLift 148462
  have htrace : WordTrace (prefixWord ++ tailWord_148462) baseStart_148462 baseEnd_148462 := by
    simpa [prefixWord, tailWord_148462, baseEnd_148462] using wordTrace_append hprefix tailTrace_148462
  have hstable : (prefixWord ++ tailWord_148462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148462).length < 2 ^ (prefixWord ++ tailWord_148462).sum := by decide
  have hdescent : baseEnd_148462 < baseStart_148462 := by decide
  rcases family_descends (prefixWord ++ tailWord_148462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148503 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 3]
def baseStart_148503 : Nat := 118140960795 + 148503 * 2 ^ 59
def prefixEnd_148503 : Nat := 4983230072969 + 3 ^ 40 * 148503 * 2
def baseEnd_148503 : Nat := 67780815675322413359603

theorem tailTrace_148503 : CollatzResearch.WordTrace tailWord_148503 prefixEnd_148503 67780815675322413359603 := by
  unfold tailWord_148503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416349381006468138314163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3610899587337645425542775 5416349381006468138314163)
  ·
    refine ⟨8124524071509702207471245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5416349381006468138314163 8124524071509702207471245)
    ·
      refine ⟨3046696526816138327801717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8124524071509702207471245 3046696526816138327801717)
      ·
        refine ⟨285627799389012968231411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3046696526816138327801717 285627799389012968231411)
        ·
          refine ⟨428441699083519452347117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285627799389012968231411 428441699083519452347117)
          ·
            refine ⟨160665637156319794630169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 428441699083519452347117 160665637156319794630169)
            ·
              refine ⟨120499227867239845972627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160665637156319794630169 120499227867239845972627)
              ·
                refine ⟨180748841800859768958941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120499227867239845972627 180748841800859768958941)
                ·
                  refine ⟨67780815675322413359603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180748841800859768958941 67780815675322413359603)
                  ·
                    rfl

theorem cell20_148503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_148503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148503 prefixEnd_148503 := by exact prefixLift 148503
  have htrace : WordTrace (prefixWord ++ tailWord_148503) baseStart_148503 baseEnd_148503 := by
    simpa [prefixWord, tailWord_148503, baseEnd_148503] using wordTrace_append hprefix tailTrace_148503
  have hstable : (prefixWord ++ tailWord_148503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148503).length < 2 ^ (prefixWord ++ tailWord_148503).sum := by decide
  have hdescent : baseEnd_148503 < baseStart_148503 := by decide
  rcases family_descends (prefixWord ++ tailWord_148503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148586 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_148586 : Nat := 118140960795 + 148586 * 2 ^ 59
def prefixEnd_148586 : Nat := 4983230072969 + 3 ^ 40 * 148586 * 2
def baseEnd_148586 : Nat := 67818699136943013592597

theorem tailTrace_148586 : CollatzResearch.WordTrace tailWord_148586 prefixEnd_148586 67818699136943013592597 := by
  unfold tailWord_148586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354844159926443328396403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3612917759803848875723741 1354844159926443328396403)
  ·
    refine ⟨2032266239889664992594605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354844159926443328396403 2032266239889664992594605)
    ·
      refine ⟨762099839958624372222977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2032266239889664992594605 762099839958624372222977)
      ·
        refine ⟨571574879968968279167233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 762099839958624372222977 571574879968968279167233)
        ·
          refine ⟨428681159976726209375425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571574879968968279167233 428681159976726209375425)
          ·
            refine ⟨321510869982544657031569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428681159976726209375425 321510869982544657031569)
            ·
              refine ⟨241133152486908492773677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321510869982544657031569 241133152486908492773677)
              ·
                refine ⟨90424932182590684790129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241133152486908492773677 90424932182590684790129)
                ·
                  refine ⟨67818699136943013592597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90424932182590684790129 67818699136943013592597)
                  ·
                    rfl

theorem cell20_148586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_148586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148586 prefixEnd_148586 := by exact prefixLift 148586
  have htrace : WordTrace (prefixWord ++ tailWord_148586) baseStart_148586 baseEnd_148586 := by
    simpa [prefixWord, tailWord_148586, baseEnd_148586] using wordTrace_append hprefix tailTrace_148586
  have hstable : (prefixWord ++ tailWord_148586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148586).length < 2 ^ (prefixWord ++ tailWord_148586).sum := by decide
  have hdescent : baseEnd_148586 < baseStart_148586 := by decide
  rcases family_descends (prefixWord ++ tailWord_148586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148604 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_148604 : Nat := 118140960795 + 148604 * 2 ^ 59
def prefixEnd_148604 : Nat := 4983230072969 + 3 ^ 40 * 148604 * 2
def baseEnd_148604 : Nat := 67826914827414950992523

theorem tailTrace_148604 : CollatzResearch.WordTrace tailWord_148604 prefixEnd_148604 67826914827414950992523 := by
  unfold tailWord_148604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710016576820281193870433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3613355435760374925160577 2710016576820281193870433)
  ·
    refine ⟨2032512432615210895402825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2710016576820281193870433 2032512432615210895402825)
    ·
      refine ⟨1524384324461408171552119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2032512432615210895402825 1524384324461408171552119)
      ·
        refine ⟨2286576486692112257328179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524384324461408171552119 2286576486692112257328179)
        ·
          refine ⟨3429864730038168385992269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286576486692112257328179 3429864730038168385992269)
          ·
            refine ⟨1286199273764313144747101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3429864730038168385992269 1286199273764313144747101)
            ·
              refine ⟨482324727661617429280163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1286199273764313144747101 482324727661617429280163)
              ·
                refine ⟨723487091492426143920245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482324727661617429280163 723487091492426143920245)
                ·
                  refine ⟨67826914827414950992523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723487091492426143920245 67826914827414950992523)
                  ·
                    rfl

theorem cell20_148604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_148604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148604 prefixEnd_148604 := by exact prefixLift 148604
  have htrace : WordTrace (prefixWord ++ tailWord_148604) baseStart_148604 baseEnd_148604 := by
    simpa [prefixWord, tailWord_148604, baseEnd_148604] using wordTrace_append hprefix tailTrace_148604
  have hstable : (prefixWord ++ tailWord_148604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148604).length < 2 ^ (prefixWord ++ tailWord_148604).sum := by decide
  have hdescent : baseEnd_148604 < baseStart_148604 := by decide
  rcases family_descends (prefixWord ++ tailWord_148604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148645 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 2]
def baseStart_148645 : Nat := 118140960795 + 148645 * 2 ^ 59
def prefixEnd_148645 : Nat := 4983230072969 + 3 ^ 40 * 148645 * 2
def baseEnd_148645 : Nat := 67845628344601030625689

theorem tailTrace_148645 : CollatzResearch.WordTrace tailWord_148645 prefixEnd_148645 67845628344601030625689 := by
  unfold tailWord_148645
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421528546492026389983389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3614352364328017593322259 5421528546492026389983389)
  ·
    refine ⟨2033073204934509896243771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5421528546492026389983389 2033073204934509896243771)
    ·
      refine ⟨3049609807401764844365657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033073204934509896243771 3049609807401764844365657)
      ·
        refine ⟨2287207355551323633274243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3049609807401764844365657 2287207355551323633274243)
        ·
          refine ⟨3430811033326985449911365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287207355551323633274243 3430811033326985449911365)
          ·
            refine ⟨643277068748809771858381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3430811033326985449911365 643277068748809771858381)
            ·
              refine ⟨241228900780803664446893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 643277068748809771858381 241228900780803664446893)
              ·
                refine ⟨90460837792801374167585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241228900780803664446893 90460837792801374167585)
                ·
                  refine ⟨67845628344601030625689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90460837792801374167585 67845628344601030625689)
                  ·
                    rfl

theorem cell20_148645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_148645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148645 prefixEnd_148645 := by exact prefixLift 148645
  have htrace : WordTrace (prefixWord ++ tailWord_148645) baseStart_148645 baseEnd_148645 := by
    simpa [prefixWord, tailWord_148645, baseEnd_148645] using wordTrace_append hprefix tailTrace_148645
  have hstable : (prefixWord ++ tailWord_148645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148645).length < 2 ^ (prefixWord ++ tailWord_148645).sum := by decide
  have hdescent : baseEnd_148645 < baseStart_148645 := by decide
  rcases family_descends (prefixWord ++ tailWord_148645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148676 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_148676 : Nat := 118140960795 + 148676 * 2 ^ 59
def prefixEnd_148676 : Nat := 4983230072969 + 3 ^ 40 * 148676 * 2
def baseEnd_148676 : Nat := 67859777589302700592229

theorem tailTrace_148676 : CollatzResearch.WordTrace tailWord_148676 prefixEnd_148676 67859777589302700592229 := by
  unfold tailWord_148676
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711329604689859342180941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3615106139586479122907921 2711329604689859342180941)
  ·
    refine ⟨1016748601758697253317853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2711329604689859342180941 1016748601758697253317853)
    ·
      refine ⟨381280725659511469994195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1016748601758697253317853 381280725659511469994195)
      ·
        refine ⟨571921088489267204991293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381280725659511469994195 571921088489267204991293)
        ·
          refine ⟨214470408183475201871735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 571921088489267204991293 214470408183475201871735)
          ·
            refine ⟨321705612275212802807603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214470408183475201871735 321705612275212802807603)
            ·
              refine ⟨482558418412819204211405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321705612275212802807603 482558418412819204211405)
              ·
                refine ⟨180959406904807201579277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482558418412819204211405 180959406904807201579277)
                ·
                  refine ⟨67859777589302700592229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180959406904807201579277 67859777589302700592229)
                  ·
                    rfl

theorem cell20_148676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_148676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148676 prefixEnd_148676 := by exact prefixLift 148676
  have htrace : WordTrace (prefixWord ++ tailWord_148676) baseStart_148676 baseEnd_148676 := by
    simpa [prefixWord, tailWord_148676, baseEnd_148676] using wordTrace_append hprefix tailTrace_148676
  have hstable : (prefixWord ++ tailWord_148676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148676).length < 2 ^ (prefixWord ++ tailWord_148676).sum := by decide
  have hdescent : baseEnd_148676 < baseStart_148676 := by decide
  rcases family_descends (prefixWord ++ tailWord_148676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148711 : List Nat := [1, 1, 5, 3, 2, 8]
def baseStart_148711 : Nat := 118140960795 + 148711 * 2 ^ 59
def prefixEnd_148711 : Nat := 4983230072969 + 3 ^ 40 * 148711 * 2
def baseEnd_148711 : Nat := 2513916760851782756497

theorem tailTrace_148711 : CollatzResearch.WordTrace tailWord_148711 prefixEnd_148711 2513916760851782756497 := by
  unfold tailWord_148711
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423935764252919661885987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3615957176168613107923991 5423935764252919661885987)
  ·
    refine ⟨8135903646379379492828981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5423935764252919661885987 8135903646379379492828981)
    ·
      refine ⟨762740966848066827452717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8135903646379379492828981 762740966848066827452717)
      ·
        refine ⟨286027862568025060294769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 762740966848066827452717 286027862568025060294769)
        ·
          refine ⟨214520896926018795221077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286027862568025060294769 214520896926018795221077)
          ·
            refine ⟨2513916760851782756497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 214520896926018795221077 2513916760851782756497)
            ·
              rfl

theorem cell20_148711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 8].length) (baseStart_148711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148711 prefixEnd_148711 := by exact prefixLift 148711
  have htrace : WordTrace (prefixWord ++ tailWord_148711) baseStart_148711 baseEnd_148711 := by
    simpa [prefixWord, tailWord_148711, baseEnd_148711] using wordTrace_append hprefix tailTrace_148711
  have hstable : (prefixWord ++ tailWord_148711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148711).length < 2 ^ (prefixWord ++ tailWord_148711).sum := by decide
  have hdescent : baseEnd_148711 < baseStart_148711 := by decide
  rcases family_descends (prefixWord ++ tailWord_148711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148717 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 2]
def baseStart_148717 : Nat := 118140960795 + 148717 * 2 ^ 59
def prefixEnd_148717 : Nat := 4983230072969 + 3 ^ 40 * 148717 * 2
def baseEnd_148717 : Nat := 67878491106488780225395

theorem tailTrace_148717 : CollatzResearch.WordTrace tailWord_148717 prefixEnd_148717 67878491106488780225395 := by
  unfold tailWord_148717
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424154602231182686604405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3616103068154121791069603 5424154602231182686604405)
  ·
    refine ⟨508514493959173376869163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5424154602231182686604405 508514493959173376869163)
    ·
      refine ⟨762771740938760065303745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508514493959173376869163 762771740938760065303745)
      ·
        refine ⟨572078805704070048977809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 762771740938760065303745 572078805704070048977809)
        ·
          refine ⟨429059104278052536733357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572078805704070048977809 429059104278052536733357)
          ·
            refine ⟨160897164104269701275009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429059104278052536733357 160897164104269701275009)
            ·
              refine ⟨120672873078202275956257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160897164104269701275009 120672873078202275956257)
              ·
                refine ⟨90504654808651706967193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120672873078202275956257 90504654808651706967193)
                ·
                  refine ⟨67878491106488780225395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90504654808651706967193 67878491106488780225395)
                  ·
                    rfl

theorem cell20_148717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_148717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148717 prefixEnd_148717 := by exact prefixLift 148717
  have htrace : WordTrace (prefixWord ++ tailWord_148717) baseStart_148717 baseEnd_148717 := by
    simpa [prefixWord, tailWord_148717, baseEnd_148717] using wordTrace_append hprefix tailTrace_148717
  have hstable : (prefixWord ++ tailWord_148717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148717).length < 2 ^ (prefixWord ++ tailWord_148717).sum := by decide
  have hdescent : baseEnd_148717 < baseStart_148717 := by decide
  rcases family_descends (prefixWord ++ tailWord_148717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148718 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_148718 : Nat := 118140960795 + 148718 * 2 ^ 59
def prefixEnd_148718 : Nat := 4983230072969 + 3 ^ 40 * 148718 * 2
def baseEnd_148718 : Nat := 67878947533737221192057

theorem tailTrace_148718 : CollatzResearch.WordTrace tailWord_148718 prefixEnd_148718 67878947533737221192057 := by
  unfold tailWord_148718
  simp only [CollatzResearch.WordTrace]
  refine ⟨678023884403444982173851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3616127383485039904927205 678023884403444982173851)
  ·
    refine ⟨1017035826605167473260777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 678023884403444982173851 1017035826605167473260777)
    ·
      refine ⟨762776869953875604945583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1017035826605167473260777 762776869953875604945583)
      ·
        refine ⟨1144165304930813407418375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762776869953875604945583 1144165304930813407418375)
        ·
          refine ⟨1716247957396220111127563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144165304930813407418375 1716247957396220111127563)
          ·
            refine ⟨2574371936094330166691345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716247957396220111127563 2574371936094330166691345)
            ·
              refine ⟨1930778952070747625018509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574371936094330166691345 1930778952070747625018509)
              ·
                refine ⟨724042107026530359381941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1930778952070747625018509 724042107026530359381941)
                ·
                  refine ⟨67878947533737221192057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 724042107026530359381941 67878947533737221192057)
                  ·
                    rfl

theorem cell20_148718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_148718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148718 prefixEnd_148718 := by exact prefixLift 148718
  have htrace : WordTrace (prefixWord ++ tailWord_148718) baseStart_148718 baseEnd_148718 := by
    simpa [prefixWord, tailWord_148718, baseEnd_148718] using wordTrace_append hprefix tailTrace_148718
  have hstable : (prefixWord ++ tailWord_148718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148718).length < 2 ^ (prefixWord ++ tailWord_148718).sum := by decide
  have hdescent : baseEnd_148718 < baseStart_148718 := by decide
  rcases family_descends (prefixWord ++ tailWord_148718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148759 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 2]
def baseStart_148759 : Nat := 118140960795 + 148759 * 2 ^ 59
def prefixEnd_148759 : Nat := 4983230072969 + 3 ^ 40 * 148759 * 2
def baseEnd_148759 : Nat := 67897661050923300825223

theorem tailTrace_148759 : CollatzResearch.WordTrace tailWord_148759 prefixEnd_148759 67897661050923300825223 := by
  unfold tailWord_148759
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425686468079023859633331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3617124312052682573088887 5425686468079023859633331)
  ·
    refine ⟨8138529702118535789449997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5425686468079023859633331 8138529702118535789449997)
    ·
      refine ⟨3051948638294450921043749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8138529702118535789449997 3051948638294450921043749)
      ·
        refine ⟨572240369680209547695703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3051948638294450921043749 572240369680209547695703)
        ·
          refine ⟨858360554520314321543555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572240369680209547695703 858360554520314321543555)
          ·
            refine ⟨1287540831780471482315333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858360554520314321543555 1287540831780471482315333)
            ·
              refine ⟨241413905958838402934125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1287540831780471482315333 241413905958838402934125)
              ·
                refine ⟨90530214734564401100297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241413905958838402934125 90530214734564401100297)
                ·
                  refine ⟨67897661050923300825223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90530214734564401100297 67897661050923300825223)
                  ·
                    rfl

theorem cell20_148759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 2].length) (baseStart_148759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148759 prefixEnd_148759 := by exact prefixLift 148759
  have htrace : WordTrace (prefixWord ++ tailWord_148759) baseStart_148759 baseEnd_148759 := by
    simpa [prefixWord, tailWord_148759, baseEnd_148759] using wordTrace_append hprefix tailTrace_148759
  have hstable : (prefixWord ++ tailWord_148759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148759).length < 2 ^ (prefixWord ++ tailWord_148759).sum := by decide
  have hdescent : baseEnd_148759 < baseStart_148759 := by decide
  rcases family_descends (prefixWord ++ tailWord_148759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148773 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_148773 : Nat := 118140960795 + 148773 * 2 ^ 59
def prefixEnd_148773 : Nat := 4983230072969 + 3 ^ 40 * 148773 * 2
def baseEnd_148773 : Nat := 67904051032401474358499

theorem tailTrace_148773 : CollatzResearch.WordTrace tailWord_148773 prefixEnd_148773 67904051032401474358499 := by
  unfold tailWord_148773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5426197090028304250642973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3617464726685536167095315 5426197090028304250642973)
  ·
    refine ⟨2034823908760614093991115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5426197090028304250642973 2034823908760614093991115)
    ·
      refine ⟨3052235863140921140986673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034823908760614093991115 3052235863140921140986673)
      ·
        refine ⟨2289176897355690855740005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3052235863140921140986673 2289176897355690855740005)
        ·
          refine ⟨429220668254192035451251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2289176897355690855740005 429220668254192035451251)
          ·
            refine ⟨643831002381288053176877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429220668254192035451251 643831002381288053176877)
            ·
              refine ⟨241436625892983019941329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 643831002381288053176877 241436625892983019941329)
              ·
                refine ⟨181077469419737264955997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241436625892983019941329 181077469419737264955997)
                ·
                  refine ⟨67904051032401474358499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181077469419737264955997 67904051032401474358499)
                  ·
                    rfl

theorem cell20_148773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_148773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148773 prefixEnd_148773 := by exact prefixLift 148773
  have htrace : WordTrace (prefixWord ++ tailWord_148773) baseStart_148773 baseEnd_148773 := by
    simpa [prefixWord, tailWord_148773, baseEnd_148773] using wordTrace_append hprefix tailTrace_148773
  have hstable : (prefixWord ++ tailWord_148773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148773).length < 2 ^ (prefixWord ++ tailWord_148773).sum := by decide
  have hdescent : baseEnd_148773 < baseStart_148773 := by decide
  rcases family_descends (prefixWord ++ tailWord_148773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148804 : List Nat := [2, 3, 4, 1, 1, 2, 1, 6]
def baseStart_148804 : Nat := 118140960795 + 148804 * 2 ^ 59
def prefixEnd_148804 : Nat := 4983230072969 + 3 ^ 40 * 148804 * 2
def baseEnd_148804 : Nat := 22639400092367714775013

theorem tailTrace_148804 : CollatzResearch.WordTrace tailWord_148804 prefixEnd_148804 22639400092367714775013 := by
  unfold tailWord_148804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713663876457998272510733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3618218501943997696680977 2713663876457998272510733)
  ·
    refine ⟨1017623953671749352191525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2713663876457998272510733 1017623953671749352191525)
    ·
      refine ⟨190804491313453003535911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1017623953671749352191525 190804491313453003535911)
      ·
        refine ⟨286206736970179505303867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190804491313453003535911 286206736970179505303867)
        ·
          refine ⟨429310105455269257955801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286206736970179505303867 429310105455269257955801)
          ·
            refine ⟨321982579091451943466851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429310105455269257955801 321982579091451943466851)
            ·
              refine ⟨482973868637177915200277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321982579091451943466851 482973868637177915200277)
              ·
                refine ⟨22639400092367714775013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 482973868637177915200277 22639400092367714775013)
                ·
                  rfl

theorem cell20_148804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_148804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148804 prefixEnd_148804 := by exact prefixLift 148804
  have htrace : WordTrace (prefixWord ++ tailWord_148804) baseStart_148804 baseEnd_148804 := by
    simpa [prefixWord, tailWord_148804, baseEnd_148804] using wordTrace_append hprefix tailTrace_148804
  have hstable : (prefixWord ++ tailWord_148804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148804).length < 2 ^ (prefixWord ++ tailWord_148804).sum := by decide
  have hdescent : baseEnd_148804 < baseStart_148804 := by decide
  rcases family_descends (prefixWord ++ tailWord_148804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148832 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_148832 : Nat := 118140960795 + 148832 * 2 ^ 59
def prefixEnd_148832 : Nat := 4983230072969 + 3 ^ 40 * 148832 * 2
def baseEnd_148832 : Nat := 67930980240059491391591

theorem tailTrace_148832 : CollatzResearch.WordTrace tailWord_148832 prefixEnd_148832 67930980240059491391591 := by
  unfold tailWord_148832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714174498407278663520375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3618899331209704884693833 2714174498407278663520375)
  ·
    refine ⟨4071261747610917995280563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2714174498407278663520375 4071261747610917995280563)
    ·
      refine ⟨6106892621416376992920845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071261747610917995280563 6106892621416376992920845)
      ·
        refine ⟨2290084733031141372345317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6106892621416376992920845 2290084733031141372345317)
        ·
          refine ⟨429390887443339007314747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2290084733031141372345317 429390887443339007314747)
          ·
            refine ⟨644086331165008510972121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429390887443339007314747 644086331165008510972121)
            ·
              refine ⟨483064748373756383229091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644086331165008510972121 483064748373756383229091)
              ·
                refine ⟨724597122560634574843637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483064748373756383229091 724597122560634574843637)
                ·
                  refine ⟨67930980240059491391591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 724597122560634574843637 67930980240059491391591)
                  ·
                    rfl

theorem cell20_148832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_148832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148832 prefixEnd_148832 := by exact prefixLift 148832
  have htrace : WordTrace (prefixWord ++ tailWord_148832) baseStart_148832 baseEnd_148832 := by
    simpa [prefixWord, tailWord_148832, baseEnd_148832] using wordTrace_append hprefix tailTrace_148832
  have hstable : (prefixWord ++ tailWord_148832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148832).length < 2 ^ (prefixWord ++ tailWord_148832).sum := by decide
  have hdescent : baseEnd_148832 < baseStart_148832 := by decide
  rcases family_descends (prefixWord ++ tailWord_148832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148842 : List Nat := [3, 1, 3, 3, 2, 1, 2, 5]
def baseStart_148842 : Nat := 118140960795 + 148842 * 2 ^ 59
def prefixEnd_148842 : Nat := 4983230072969 + 3 ^ 40 * 148842 * 2
def baseEnd_148842 : Nat := 22645181504181300352739

theorem tailTrace_148842 : CollatzResearch.WordTrace tailWord_148842 prefixEnd_148842 22645181504181300352739 := by
  unfold tailWord_148842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357178431694582258726195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3619142484518886023269853 1357178431694582258726195)
  ·
    refine ⟨2035767647541873388089293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357178431694582258726195 2035767647541873388089293)
    ·
      refine ⟨763412867828202520533485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2035767647541873388089293 763412867828202520533485)
      ·
        refine ⟨286279825435575945200057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 763412867828202520533485 286279825435575945200057)
        ·
          refine ⟨214709869076681958900043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286279825435575945200057 214709869076681958900043)
          ·
            refine ⟨322064803615022938350065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214709869076681958900043 322064803615022938350065)
            ·
              refine ⟨241548602711267203762549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322064803615022938350065 241548602711267203762549)
              ·
                refine ⟨22645181504181300352739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241548602711267203762549 22645181504181300352739)
                ·
                  rfl

theorem cell20_148842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_148842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148842 prefixEnd_148842 := by exact prefixLift 148842
  have htrace : WordTrace (prefixWord ++ tailWord_148842) baseStart_148842 baseEnd_148842 := by
    simpa [prefixWord, tailWord_148842, baseEnd_148842] using wordTrace_append hprefix tailTrace_148842
  have hstable : (prefixWord ++ tailWord_148842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148842).length < 2 ^ (prefixWord ++ tailWord_148842).sum := by decide
  have hdescent : baseEnd_148842 < baseStart_148842 := by decide
  rcases family_descends (prefixWord ++ tailWord_148842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148849 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 3]
def baseStart_148849 : Nat := 118140960795 + 148849 * 2 ^ 59
def prefixEnd_148849 : Nat := 4983230072969 + 3 ^ 40 * 148849 * 2
def baseEnd_148849 : Nat := 67938739503282987824855

theorem tailTrace_148849 : CollatzResearch.WordTrace tailWord_148849 prefixEnd_148849 67938739503282987824855 := by
  unfold tailWord_148849
  simp only [CollatzResearch.WordTrace]
  refine ⟨5428969037752969230409601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3619312691835312820273067 5428969037752969230409601)
  ·
    refine ⟨4071726778314726922807201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5428969037752969230409601 4071726778314726922807201)
    ·
      refine ⟨3053795083736045192105401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4071726778314726922807201 3053795083736045192105401)
      ·
        refine ⟨2290346312802033894079051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3053795083736045192105401 2290346312802033894079051)
        ·
          refine ⟨3435519469203050841118577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290346312802033894079051 3435519469203050841118577)
          ·
            refine ⟨2576639601902288130838933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435519469203050841118577 2576639601902288130838933)
            ·
              refine ⟨120779981339169756133075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2576639601902288130838933 120779981339169756133075)
              ·
                refine ⟨181169972008754634199613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120779981339169756133075 181169972008754634199613)
                ·
                  refine ⟨67938739503282987824855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181169972008754634199613 67938739503282987824855)
                  ·
                    rfl

theorem cell20_148849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_148849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148849 prefixEnd_148849 := by exact prefixLift 148849
  have htrace : WordTrace (prefixWord ++ tailWord_148849) baseStart_148849 baseEnd_148849 := by
    simpa [prefixWord, tailWord_148849, baseEnd_148849] using wordTrace_append hprefix tailTrace_148849
  have hstable : (prefixWord ++ tailWord_148849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148849).length < 2 ^ (prefixWord ++ tailWord_148849).sum := by decide
  have hdescent : baseEnd_148849 < baseStart_148849 := by decide
  rcases family_descends (prefixWord ++ tailWord_148849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148908 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_148908 : Nat := 118140960795 + 148908 * 2 ^ 59
def prefixEnd_148908 : Nat := 4983230072969 + 3 ^ 40 * 148908 * 2
def baseEnd_148908 : Nat := 67965668710941004857947

theorem tailTrace_148908 : CollatzResearch.WordTrace tailWord_148908 prefixEnd_148908 67965668710941004857947 := by
  unfold tailWord_148908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715560472269611153403689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3620747296359481537871585 2715560472269611153403689)
  ·
    refine ⟨2036670354202208365052767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2715560472269611153403689 2036670354202208365052767)
    ·
      refine ⟨3055005531303312547579151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036670354202208365052767 3055005531303312547579151)
      ·
        refine ⟨4582508296954968821368727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3055005531303312547579151 4582508296954968821368727)
        ·
          refine ⟨6873762445432453232053091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4582508296954968821368727 6873762445432453232053091)
          ·
            refine ⟨10310643668148679848079637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6873762445432453232053091 10310643668148679848079637)
            ·
              refine ⟨483311421944469367878733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10310643668148679848079637 483311421944469367878733)
              ·
                refine ⟨181241783229176012954525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483311421944469367878733 181241783229176012954525)
                ·
                  refine ⟨67965668710941004857947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181241783229176012954525 67965668710941004857947)
                  ·
                    rfl

theorem cell20_148908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_148908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148908 prefixEnd_148908 := by exact prefixLift 148908
  have htrace : WordTrace (prefixWord ++ tailWord_148908) baseStart_148908 baseEnd_148908 := by
    simpa [prefixWord, tailWord_148908, baseEnd_148908] using wordTrace_append hprefix tailTrace_148908
  have hstable : (prefixWord ++ tailWord_148908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148908).length < 2 ^ (prefixWord ++ tailWord_148908).sum := by decide
  have hdescent : baseEnd_148908 < baseStart_148908 := by decide
  rcases family_descends (prefixWord ++ tailWord_148908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148953 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_148953 : Nat := 118140960795 + 148953 * 2 ^ 59
def prefixEnd_148953 : Nat := 4983230072969 + 3 ^ 40 * 148953 * 2
def baseEnd_148953 : Nat := 67986207937120848357763

theorem tailTrace_148953 : CollatzResearch.WordTrace tailWord_148953 prefixEnd_148953 67986207937120848357763 := by
  unfold tailWord_148953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5432762229376194992195513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3621841486250796661463675 5432762229376194992195513)
  ·
    refine ⟨4074571672032146244146635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5432762229376194992195513 4074571672032146244146635)
    ·
      refine ⟨6111857508048219366219953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4074571672032146244146635 6111857508048219366219953)
      ·
        refine ⟨4583893131036164524664965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6111857508048219366219953 4583893131036164524664965)
        ·
          refine ⟨859479962069280848374681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4583893131036164524664965 859479962069280848374681)
          ·
            refine ⟨644609971551960636281011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859479962069280848374681 644609971551960636281011)
            ·
              refine ⟨966914957327940954421517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644609971551960636281011 966914957327940954421517)
              ·
                refine ⟨362593108997977857908069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966914957327940954421517 362593108997977857908069)
                ·
                  refine ⟨67986207937120848357763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 362593108997977857908069 67986207937120848357763)
                  ·
                    rfl

theorem cell20_148953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_148953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148953 prefixEnd_148953 := by exact prefixLift 148953
  have htrace : WordTrace (prefixWord ++ tailWord_148953) baseStart_148953 baseEnd_148953 := by
    simpa [prefixWord, tailWord_148953, baseEnd_148953] using wordTrace_append hprefix tailTrace_148953
  have hstable : (prefixWord ++ tailWord_148953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148953).length < 2 ^ (prefixWord ++ tailWord_148953).sum := by decide
  have hdescent : baseEnd_148953 < baseStart_148953 := by decide
  rcases family_descends (prefixWord ++ tailWord_148953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148973 : List Nat := [1, 5, 1, 3, 2, 2, 2, 4]
def baseStart_148973 : Nat := 118140960795 + 148973 * 2 ^ 59
def prefixEnd_148973 : Nat := 4983230072969 + 3 ^ 40 * 148973 * 2
def baseEnd_148973 : Nat := 22665112160696555897005

theorem tailTrace_148973 : CollatzResearch.WordTrace tailWord_148973 prefixEnd_148973 22665112160696555897005 := by
  unfold tailWord_148973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433491689303738407923573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3622327792869158938615715 5433491689303738407923573)
  ·
    refine ⟨509389845872225475742835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5433491689303738407923573 509389845872225475742835)
    ·
      refine ⟨764084768808338213614253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509389845872225475742835 764084768808338213614253)
      ·
        refine ⟨286531788303126830105345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 764084768808338213614253 286531788303126830105345)
        ·
          refine ⟨214898841227345122579009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286531788303126830105345 214898841227345122579009)
          ·
            refine ⟨161174130920508841934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214898841227345122579009 161174130920508841934257)
            ·
              refine ⟨120880598190381631450693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161174130920508841934257 120880598190381631450693)
              ·
                refine ⟨22665112160696555897005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120880598190381631450693 22665112160696555897005)
                ·
                  rfl

theorem cell20_148973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_148973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148973 prefixEnd_148973 := by exact prefixLift 148973
  have htrace : WordTrace (prefixWord ++ tailWord_148973) baseStart_148973 baseEnd_148973 := by
    simpa [prefixWord, tailWord_148973, baseEnd_148973] using wordTrace_append hprefix tailTrace_148973
  have hstable : (prefixWord ++ tailWord_148973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148973).length < 2 ^ (prefixWord ++ tailWord_148973).sum := by decide
  have hdescent : baseEnd_148973 < baseStart_148973 := by decide
  rcases family_descends (prefixWord ++ tailWord_148973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148977 : List Nat := [1, 2, 2, 2, 3, 2, 4, 4]
def baseStart_148977 : Nat := 118140960795 + 148977 * 2 ^ 59
def prefixEnd_148977 : Nat := 4983230072969 + 3 ^ 40 * 148977 * 2
def baseEnd_148977 : Nat := 22665720730361143852555

theorem tailTrace_148977 : CollatzResearch.WordTrace tailWord_148977 prefixEnd_148977 22665720730361143852555 := by
  unfold tailWord_148977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433637581289247091069185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3622425054192831394046123 5433637581289247091069185)
  ·
    refine ⟨4075228185966935318301889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5433637581289247091069185 4075228185966935318301889)
    ·
      refine ⟨3056421139475201488726417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4075228185966935318301889 3056421139475201488726417)
      ·
        refine ⟨2292315854606401116544813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3056421139475201488726417 2292315854606401116544813)
        ·
          refine ⟨859618445477400418704305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2292315854606401116544813 859618445477400418704305)
          ·
            refine ⟨644713834108050314028229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859618445477400418704305 644713834108050314028229)
            ·
              refine ⟨120883843895259433880293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 644713834108050314028229 120883843895259433880293)
              ·
                refine ⟨22665720730361143852555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120883843895259433880293 22665720730361143852555)
                ·
                  rfl

theorem cell20_148977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_148977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148977 prefixEnd_148977 := by exact prefixLift 148977
  have htrace : WordTrace (prefixWord ++ tailWord_148977) baseStart_148977 baseEnd_148977 := by
    simpa [prefixWord, tailWord_148977, baseEnd_148977] using wordTrace_append hprefix tailTrace_148977
  have hstable : (prefixWord ++ tailWord_148977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148977).length < 2 ^ (prefixWord ++ tailWord_148977).sum := by decide
  have hdescent : baseEnd_148977 < baseStart_148977 := by decide
  rcases family_descends (prefixWord ++ tailWord_148977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148994 : List Nat := [3, 4, 1, 2, 1, 3, 6]
def baseStart_148994 : Nat := 118140960795 + 148994 * 2 ^ 59
def prefixEnd_148994 : Nat := 4983230072969 + 3 ^ 40 * 148994 * 2
def baseEnd_148994 : Nat := 7556102383811880887881

theorem tailTrace_148994 : CollatzResearch.WordTrace tailWord_148994 prefixEnd_148994 7556102383811880887881 := by
  unfold tailWord_148994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358564405556914748609509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3622838414818439329625357 1358564405556914748609509)
  ·
    refine ⟨254730826041921515364283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1358564405556914748609509 254730826041921515364283)
    ·
      refine ⟨382096239062882273046425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254730826041921515364283 382096239062882273046425)
      ·
        refine ⟨286572179297161704784819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382096239062882273046425 286572179297161704784819)
        ·
          refine ⟨429858268945742557177229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286572179297161704784819 429858268945742557177229)
          ·
            refine ⟨161196850854653458941461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429858268945742557177229 161196850854653458941461)
            ·
              refine ⟨7556102383811880887881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161196850854653458941461 7556102383811880887881)
              ·
                rfl

theorem cell20_148994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 6].length) (baseStart_148994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_148994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_148994 prefixEnd_148994 := by exact prefixLift 148994
  have htrace : WordTrace (prefixWord ++ tailWord_148994) baseStart_148994 baseEnd_148994 := by
    simpa [prefixWord, tailWord_148994, baseEnd_148994] using wordTrace_append hprefix tailTrace_148994
  have hstable : (prefixWord ++ tailWord_148994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148994).length < 2 ^ (prefixWord ++ tailWord_148994).sum := by decide
  have hdescent : baseEnd_148994 < baseStart_148994 := by decide
  rcases family_descends (prefixWord ++ tailWord_148994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149004 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 2]
def baseStart_149004 : Nat := 118140960795 + 149004 * 2 ^ 59
def prefixEnd_149004 : Nat := 4983230072969 + 3 ^ 40 * 149004 * 2
def baseEnd_149004 : Nat := 68009485726791337657555

theorem tailTrace_149004 : CollatzResearch.WordTrace tailWord_149004 prefixEnd_149004 68009485726791337657555 := by
  unfold tailWord_149004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717311176095715351151033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3623081568127620468201377 2717311176095715351151033)
  ·
    refine ⟨2037983382071786513363275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2717311176095715351151033 2037983382071786513363275)
    ·
      refine ⟨3056975073107679770044913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037983382071786513363275 3056975073107679770044913)
      ·
        refine ⟨2292731304830759827533685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3056975073107679770044913 2292731304830759827533685)
        ·
          refine ⟨214943559827883733831283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2292731304830759827533685 214943559827883733831283)
          ·
            refine ⟨322415339741825600746925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214943559827883733831283 322415339741825600746925)
            ·
              refine ⟨120905752403184600280097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322415339741825600746925 120905752403184600280097)
              ·
                refine ⟨90679314302388450210073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120905752403184600280097 90679314302388450210073)
                ·
                  refine ⟨68009485726791337657555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90679314302388450210073 68009485726791337657555)
                  ·
                    rfl

theorem cell20_149004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_149004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149004 prefixEnd_149004 := by exact prefixLift 149004
  have htrace : WordTrace (prefixWord ++ tailWord_149004) baseStart_149004 baseEnd_149004 := by
    simpa [prefixWord, tailWord_149004, baseEnd_149004] using wordTrace_append hprefix tailTrace_149004
  have hstable : (prefixWord ++ tailWord_149004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149004).length < 2 ^ (prefixWord ++ tailWord_149004).sum := by decide
  have hdescent : baseEnd_149004 < baseStart_149004 := by decide
  rcases family_descends (prefixWord ++ tailWord_149004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149053 : List Nat := [1, 4, 1, 3, 4, 7]
def baseStart_149053 : Nat := 118140960795 + 149053 * 2 ^ 59
def prefixEnd_149053 : Nat := 4983230072969 + 3 ^ 40 * 149053 * 2
def baseEnd_149053 : Nat := 2519698172665368334223

theorem tailTrace_149053 : CollatzResearch.WordTrace tailWord_149053 prefixEnd_149053 2519698172665368334223 := by
  unfold tailWord_149053
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436409529013912070835813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3624273019342608047223875 5436409529013912070835813)
  ·
    refine ⟨1019326786690108513281715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5436409529013912070835813 1019326786690108513281715)
    ·
      refine ⟨1528990180035162769922573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019326786690108513281715 1528990180035162769922573)
      ·
        refine ⟨573371317513186038720965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1528990180035162769922573 573371317513186038720965)
        ·
          refine ⟨107507122033722382260181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 573371317513186038720965 107507122033722382260181)
          ·
            refine ⟨2519698172665368334223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 107507122033722382260181 2519698172665368334223)
            ·
              rfl

theorem cell20_149053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 7].length) (baseStart_149053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149053 prefixEnd_149053 := by exact prefixLift 149053
  have htrace : WordTrace (prefixWord ++ tailWord_149053) baseStart_149053 baseEnd_149053 := by
    simpa [prefixWord, tailWord_149053, baseEnd_149053] using wordTrace_append hprefix tailTrace_149053
  have hstable : (prefixWord ++ tailWord_149053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149053).length < 2 ^ (prefixWord ++ tailWord_149053).sum := by decide
  have hdescent : baseEnd_149053 < baseStart_149053 := by decide
  rcases family_descends (prefixWord ++ tailWord_149053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149063 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 2]
def baseStart_149063 : Nat := 118140960795 + 149063 * 2 ^ 59
def prefixEnd_149063 : Nat := 4983230072969 + 3 ^ 40 * 149063 * 2
def baseEnd_149063 : Nat := 68036414934449354690647

theorem tailTrace_149063 : CollatzResearch.WordTrace tailWord_149063 prefixEnd_149063 68036414934449354690647 := by
  unfold tailWord_149063
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436774258977683778699843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3624516172651789185799895 5436774258977683778699843)
  ·
    refine ⟨8155161388466525668049765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5436774258977683778699843 8155161388466525668049765)
    ·
      refine ⟨1529092760337473562759331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8155161388466525668049765 1529092760337473562759331)
      ·
        refine ⟨2293639140506210344138997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529092760337473562759331 2293639140506210344138997)
        ·
          refine ⟨215028669422457219763031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2293639140506210344138997 215028669422457219763031)
          ·
            refine ⟨322543004133685829644547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215028669422457219763031 322543004133685829644547)
            ·
              refine ⟨483814506200528744466821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322543004133685829644547 483814506200528744466821)
              ·
                refine ⟨90715219912599139587529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483814506200528744466821 90715219912599139587529)
                ·
                  refine ⟨68036414934449354690647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90715219912599139587529 68036414934449354690647)
                  ·
                    rfl

theorem cell20_149063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 2].length) (baseStart_149063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149063 prefixEnd_149063 := by exact prefixLift 149063
  have htrace : WordTrace (prefixWord ++ tailWord_149063) baseStart_149063 baseEnd_149063 := by
    simpa [prefixWord, tailWord_149063, baseEnd_149063] using wordTrace_append hprefix tailTrace_149063
  have hstable : (prefixWord ++ tailWord_149063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149063).length < 2 ^ (prefixWord ++ tailWord_149063).sum := by decide
  have hdescent : baseEnd_149063 < baseStart_149063 := by decide
  rcases family_descends (prefixWord ++ tailWord_149063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149084 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_149084 : Nat := 118140960795 + 149084 * 2 ^ 59
def prefixEnd_149084 : Nat := 4983230072969 + 3 ^ 40 * 149084 * 2
def baseEnd_149084 : Nat := 68045999906666614990561

theorem tailTrace_149084 : CollatzResearch.WordTrace tailWord_149084 prefixEnd_149084 68045999906666614990561 := by
  unfold tailWord_149084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718770095950802182607153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3625026794601069576809537 2718770095950802182607153)
  ·
    refine ⟨2039077571963101636955365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2718770095950802182607153 2039077571963101636955365)
    ·
      refine ⟨382327044743081556929131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2039077571963101636955365 382327044743081556929131)
      ·
        refine ⟨573490567114622335393697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382327044743081556929131 573490567114622335393697)
        ·
          refine ⟨430117925335966751545273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573490567114622335393697 430117925335966751545273)
          ·
            refine ⟨322588444001975063658955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430117925335966751545273 322588444001975063658955)
            ·
              refine ⟨483882666002962595488433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322588444001975063658955 483882666002962595488433)
              ·
                refine ⟨362911999502221946616325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483882666002962595488433 362911999502221946616325)
                ·
                  refine ⟨68045999906666614990561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 362911999502221946616325 68045999906666614990561)
                  ·
                    rfl

theorem cell20_149084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_149084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149084 prefixEnd_149084 := by exact prefixLift 149084
  have htrace : WordTrace (prefixWord ++ tailWord_149084) baseStart_149084 baseEnd_149084 := by
    simpa [prefixWord, tailWord_149084, baseEnd_149084] using wordTrace_append hprefix tailTrace_149084
  have hstable : (prefixWord ++ tailWord_149084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149084).length < 2 ^ (prefixWord ++ tailWord_149084).sum := by decide
  have hdescent : baseEnd_149084 < baseStart_149084 := by decide
  rcases family_descends (prefixWord ++ tailWord_149084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149091 : List Nat := [1, 1, 1, 5, 1, 4, 3, 4]
def baseStart_149091 : Nat := 118140960795 + 149091 * 2 ^ 59
def prefixEnd_149091 : Nat := 4983230072969 + 3 ^ 40 * 149091 * 2
def baseEnd_149091 : Nat := 22683064965801900585733

theorem tailTrace_149091 : CollatzResearch.WordTrace tailWord_149091 prefixEnd_149091 22683064965801900585733 := by
  unfold tailWord_149091
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437795502876244560719127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3625197001917496373812751 5437795502876244560719127)
  ·
    refine ⟨8156693254314366841078691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5437795502876244560719127 8156693254314366841078691)
    ·
      refine ⟨12235039881471550261618037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8156693254314366841078691 12235039881471550261618037)
      ·
        refine ⟨1147034988887957837026691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12235039881471550261618037 1147034988887957837026691)
        ·
          refine ⟨1720552483331936755540037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147034988887957837026691 1720552483331936755540037)
          ·
            refine ⟨322603590624738141663757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1720552483331936755540037 322603590624738141663757)
            ·
              refine ⟨120976346484276803123909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322603590624738141663757 120976346484276803123909)
              ·
                refine ⟨22683064965801900585733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120976346484276803123909 22683064965801900585733)
                ·
                  rfl

theorem cell20_149091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_149091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149091 prefixEnd_149091 := by exact prefixLift 149091
  have htrace : WordTrace (prefixWord ++ tailWord_149091) baseStart_149091 baseEnd_149091 := by
    simpa [prefixWord, tailWord_149091, baseEnd_149091] using wordTrace_append hprefix tailTrace_149091
  have hstable : (prefixWord ++ tailWord_149091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149091).length < 2 ^ (prefixWord ++ tailWord_149091).sum := by decide
  have hdescent : baseEnd_149091 < baseStart_149091 := by decide
  rcases family_descends (prefixWord ++ tailWord_149091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149143 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_149143 : Nat := 118140960795 + 149143 * 2 ^ 59
def prefixEnd_149143 : Nat := 4983230072969 + 3 ^ 40 * 149143 * 2
def baseEnd_149143 : Nat := 68072929114324632023653

theorem tailTrace_149143 : CollatzResearch.WordTrace tailWord_149143 prefixEnd_149143 68072929114324632023653 := by
  unfold tailWord_149143
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439692098687857441612083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3626461399125238294408055 5439692098687857441612083)
  ·
    refine ⟨8159538148031786162418125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5439692098687857441612083 8159538148031786162418125)
    ·
      refine ⟨3059826805511919810906797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8159538148031786162418125 3059826805511919810906797)
      ·
        refine ⟨1147435052066969929090049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3059826805511919810906797 1147435052066969929090049)
        ·
          refine ⟨860576289050227446817537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147435052066969929090049 860576289050227446817537)
          ·
            refine ⟨645432216787670585113153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860576289050227446817537 645432216787670585113153)
            ·
              refine ⟨484074162590752938834865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645432216787670585113153 484074162590752938834865)
              ·
                refine ⟨363055621943064704126149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484074162590752938834865 363055621943064704126149)
                ·
                  refine ⟨68072929114324632023653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363055621943064704126149 68072929114324632023653)
                  ·
                    rfl

theorem cell20_149143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_149143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149143 prefixEnd_149143 := by exact prefixLift 149143
  have htrace : WordTrace (prefixWord ++ tailWord_149143) baseStart_149143 baseEnd_149143 := by
    simpa [prefixWord, tailWord_149143, baseEnd_149143] using wordTrace_append hprefix tailTrace_149143
  have hstable : (prefixWord ++ tailWord_149143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149143).length < 2 ^ (prefixWord ++ tailWord_149143).sum := by decide
  have hdescent : baseEnd_149143 < baseStart_149143 := by decide
  rcases family_descends (prefixWord ++ tailWord_149143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149157 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_149157 : Nat := 118140960795 + 149157 * 2 ^ 59
def prefixEnd_149157 : Nat := 4983230072969 + 3 ^ 40 * 149157 * 2
def baseEnd_149157 : Nat := 68079319095802805556929

theorem tailTrace_149157 : CollatzResearch.WordTrace tailWord_149157 prefixEnd_149157 68079319095802805556929 := by
  unfold tailWord_149157
  simp only [CollatzResearch.WordTrace]
  refine ⟨5440202720637137832621725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3626801813758091888414483 5440202720637137832621725)
  ·
    refine ⟨2040076020238926687233147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5440202720637137832621725 2040076020238926687233147)
    ·
      refine ⟨3060114030358390030849721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040076020238926687233147 3060114030358390030849721)
      ·
        refine ⟨2295085522768792523137291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3060114030358390030849721 2295085522768792523137291)
        ·
          refine ⟨3442628284153188784705937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295085522768792523137291 3442628284153188784705937)
          ·
            refine ⟨2581971213114891588529453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3442628284153188784705937 2581971213114891588529453)
            ·
              refine ⟨968239204918084345698545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2581971213114891588529453 968239204918084345698545)
              ·
                refine ⟨726179403688563259273909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968239204918084345698545 726179403688563259273909)
                ·
                  refine ⟨68079319095802805556929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726179403688563259273909 68079319095802805556929)
                  ·
                    rfl

theorem cell20_149157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_149157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149157 prefixEnd_149157 := by exact prefixLift 149157
  have htrace : WordTrace (prefixWord ++ tailWord_149157) baseStart_149157 baseEnd_149157 := by
    simpa [prefixWord, tailWord_149157, baseEnd_149157] using wordTrace_append hprefix tailTrace_149157
  have hstable : (prefixWord ++ tailWord_149157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149157).length < 2 ^ (prefixWord ++ tailWord_149157).sum := by decide
  have hdescent : baseEnd_149157 < baseStart_149157 := by decide
  rcases family_descends (prefixWord ++ tailWord_149157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149229 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_149229 : Nat := 118140960795 + 149229 * 2 ^ 59
def prefixEnd_149229 : Nat := 4983230072969 + 3 ^ 40 * 149229 * 2
def baseEnd_149229 : Nat := 68112181857690555156635

theorem tailTrace_149229 : CollatzResearch.WordTrace tailWord_149229 prefixEnd_149229 68112181857690555156635 := by
  unfold tailWord_149229
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442828776376294129242741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3628552517584196086161827 5442828776376294129242741)
  ·
    refine ⟨510265197785277574616507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5442828776376294129242741 510265197785277574616507)
    ·
      refine ⟨765397796677916361924761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510265197785277574616507 765397796677916361924761)
      ·
        refine ⟨574048347508437271443571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 765397796677916361924761 574048347508437271443571)
        ·
          refine ⟨861072521262655907165357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574048347508437271443571 861072521262655907165357)
          ·
            refine ⟨322902195473495965187009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 861072521262655907165357 322902195473495965187009)
            ·
              refine ⟨242176646605121973890257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322902195473495965187009 242176646605121973890257)
              ·
                refine ⟨181632484953841480417693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242176646605121973890257 181632484953841480417693)
                ·
                  refine ⟨68112181857690555156635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181632484953841480417693 68112181857690555156635)
                  ·
                    rfl

theorem cell20_149229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_149229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149229 prefixEnd_149229 := by exact prefixLift 149229
  have htrace : WordTrace (prefixWord ++ tailWord_149229) baseStart_149229 baseEnd_149229 := by
    simpa [prefixWord, tailWord_149229, baseEnd_149229] using wordTrace_append hprefix tailTrace_149229
  have hstable : (prefixWord ++ tailWord_149229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149229).length < 2 ^ (prefixWord ++ tailWord_149229).sum := by decide
  have hdescent : baseEnd_149229 < baseStart_149229 := by decide
  rcases family_descends (prefixWord ++ tailWord_149229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149274 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_149274 : Nat := 118140960795 + 149274 * 2 ^ 59
def prefixEnd_149274 : Nat := 4983230072969 + 3 ^ 40 * 149274 * 2
def baseEnd_149274 : Nat := 68132721083870398656451

theorem tailTrace_149274 : CollatzResearch.WordTrace tailWord_149274 prefixEnd_149274 68132721083870398656451 := by
  unfold tailWord_149274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361117515303316703657719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3629646707475511209753917 1361117515303316703657719)
  ·
    refine ⟨2041676272954975055486579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361117515303316703657719 2041676272954975055486579)
    ·
      refine ⟨3062514409432462583229869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041676272954975055486579 3062514409432462583229869)
      ·
        refine ⟨1148442903537173468711201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3062514409432462583229869 1148442903537173468711201)
        ·
          refine ⟨861332177652880101533401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1148442903537173468711201 861332177652880101533401)
          ·
            refine ⟨645999133239660076150051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861332177652880101533401 645999133239660076150051)
            ·
              refine ⟨968998699859490114225077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645999133239660076150051 968998699859490114225077)
              ·
                refine ⟨90843628111827198208601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 968998699859490114225077 90843628111827198208601)
                ·
                  refine ⟨68132721083870398656451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90843628111827198208601 68132721083870398656451)
                  ·
                    rfl

theorem cell20_149274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_149274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149274 prefixEnd_149274 := by exact prefixLift 149274
  have htrace : WordTrace (prefixWord ++ tailWord_149274) baseStart_149274 baseEnd_149274 := by
    simpa [prefixWord, tailWord_149274, baseEnd_149274] using wordTrace_append hprefix tailTrace_149274
  have hstable : (prefixWord ++ tailWord_149274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149274).length < 2 ^ (prefixWord ++ tailWord_149274).sum := by decide
  have hdescent : baseEnd_149274 < baseStart_149274 := by decide
  rcases family_descends (prefixWord ++ tailWord_149274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149288 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_149288 : Nat := 118140960795 + 149288 * 2 ^ 59
def prefixEnd_149288 : Nat := 4983230072969 + 3 ^ 40 * 149288 * 2
def baseEnd_149288 : Nat := 68139111065348572189727

theorem tailTrace_149288 : CollatzResearch.WordTrace tailWord_149288 prefixEnd_149288 68139111065348572189727 := by
  unfold tailWord_149288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722490341581273602820259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3629987122108364803760345 2722490341581273602820259)
  ·
    refine ⟨4083735512371910404230389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2722490341581273602820259 4083735512371910404230389)
    ·
      refine ⟨382850204284866600396599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4083735512371910404230389 382850204284866600396599)
      ·
        refine ⟨574275306427299900594899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382850204284866600396599 574275306427299900594899)
        ·
          refine ⟨861412959640949850892349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574275306427299900594899 861412959640949850892349)
          ·
            refine ⟨323029859865356194084631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 861412959640949850892349 323029859865356194084631)
            ·
              refine ⟨484544789798034291126947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323029859865356194084631 484544789798034291126947)
              ·
                refine ⟨726817184697051436690421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484544789798034291126947 726817184697051436690421)
                ·
                  refine ⟨68139111065348572189727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726817184697051436690421 68139111065348572189727)
                  ·
                    rfl

theorem cell20_149288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_149288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149288 prefixEnd_149288 := by exact prefixLift 149288
  have htrace : WordTrace (prefixWord ++ tailWord_149288) baseStart_149288 baseEnd_149288 := by
    simpa [prefixWord, tailWord_149288, baseEnd_149288] using wordTrace_append hprefix tailTrace_149288
  have hstable : (prefixWord ++ tailWord_149288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149288).length < 2 ^ (prefixWord ++ tailWord_149288).sum := by decide
  have hdescent : baseEnd_149288 < baseStart_149288 := by decide
  rcases family_descends (prefixWord ++ tailWord_149288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149329 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 2]
def baseStart_149329 : Nat := 118140960795 + 149329 * 2 ^ 59
def prefixEnd_149329 : Nat := 4983230072969 + 3 ^ 40 * 149329 * 2
def baseEnd_149329 : Nat := 68157824582534651822893

theorem tailTrace_149329 : CollatzResearch.WordTrace tailWord_149329 prefixEnd_149329 68157824582534651822893 := by
  unfold tailWord_149329
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446476076014011207883041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3630984050676007471922027 5446476076014011207883041)
  ·
    refine ⟨4084857057010508405912281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5446476076014011207883041 4084857057010508405912281)
    ·
      refine ⟨3063642792757881304434211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4084857057010508405912281 3063642792757881304434211)
      ·
        refine ⟨4595464189136821956651317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063642792757881304434211 4595464189136821956651317)
        ·
          refine ⟨430824767731577058436061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4595464189136821956651317 430824767731577058436061)
          ·
            refine ⟨161559287899341396913523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 430824767731577058436061 161559287899341396913523)
            ·
              refine ⟨242338931849012095370285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161559287899341396913523 242338931849012095370285)
              ·
                refine ⟨90877099443379535763857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242338931849012095370285 90877099443379535763857)
                ·
                  refine ⟨68157824582534651822893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90877099443379535763857 68157824582534651822893)
                  ·
                    rfl

theorem cell20_149329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_149329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149329 prefixEnd_149329 := by exact prefixLift 149329
  have htrace : WordTrace (prefixWord ++ tailWord_149329) baseStart_149329 baseEnd_149329 := by
    simpa [prefixWord, tailWord_149329, baseEnd_149329] using wordTrace_append hprefix tailTrace_149329
  have hstable : (prefixWord ++ tailWord_149329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149329).length < 2 ^ (prefixWord ++ tailWord_149329).sum := by decide
  have hdescent : baseEnd_149329 < baseStart_149329 := by decide
  rcases family_descends (prefixWord ++ tailWord_149329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149346 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_149346 : Nat := 118140960795 + 149346 * 2 ^ 59
def prefixEnd_149346 : Nat := 4983230072969 + 3 ^ 40 * 149346 * 2
def baseEnd_149346 : Nat := 68165583845758148256157

theorem tailTrace_149346 : CollatzResearch.WordTrace tailWord_149346 prefixEnd_149346 68165583845758148256157 := by
  unfold tailWord_149346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361774029238105777812973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3631397411301615407501261 1361774029238105777812973)
  ·
    refine ⟨510665260964289666679865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1361774029238105777812973 510665260964289666679865)
    ·
      refine ⟨382998945723217250009899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510665260964289666679865 382998945723217250009899)
      ·
        refine ⟨574498418584825875014849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382998945723217250009899 574498418584825875014849)
        ·
          refine ⟨430873813938619406261137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574498418584825875014849 430873813938619406261137)
          ·
            refine ⟨323155360453964554695853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430873813938619406261137 323155360453964554695853)
            ·
              refine ⟨121183260170236708010945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323155360453964554695853 121183260170236708010945)
              ·
                refine ⟨90887445127677531008209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121183260170236708010945 90887445127677531008209)
                ·
                  refine ⟨68165583845758148256157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90887445127677531008209 68165583845758148256157)
                  ·
                    rfl

theorem cell20_149346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_149346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149346 prefixEnd_149346 := by exact prefixLift 149346
  have htrace : WordTrace (prefixWord ++ tailWord_149346) baseStart_149346 baseEnd_149346 := by
    simpa [prefixWord, tailWord_149346, baseEnd_149346] using wordTrace_append hprefix tailTrace_149346
  have hstable : (prefixWord ++ tailWord_149346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149346).length < 2 ^ (prefixWord ++ tailWord_149346).sum := by decide
  have hdescent : baseEnd_149346 < baseStart_149346 := by decide
  rcases family_descends (prefixWord ++ tailWord_149346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149399 : List Nat := [1, 1, 3, 3, 1, 11]
def baseStart_149399 : Nat := 118140960795 + 149399 * 2 ^ 59
def prefixEnd_149399 : Nat := 4983230072969 + 3 ^ 40 * 149399 * 2
def baseEnd_149399 : Nat := 2525547203330574795899

theorem tailTrace_149399 : CollatzResearch.WordTrace tailWord_149399 prefixEnd_149399 2525547203330574795899 := by
  unfold tailWord_149399
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449029185760413162931251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3632686123840275441954167 5449029185760413162931251)
  ·
    refine ⟨8173543778640619744396877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5449029185760413162931251 8173543778640619744396877)
    ·
      refine ⟨3065078916990232404148829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8173543778640619744396877 3065078916990232404148829)
      ·
        refine ⟨1149404593871337151555811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3065078916990232404148829 1149404593871337151555811)
        ·
          refine ⟨1724106890807005727333717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149404593871337151555811 1724106890807005727333717)
          ·
            refine ⟨2525547203330574795899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1724106890807005727333717 2525547203330574795899)
            ·
              rfl

theorem cell20_149399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 11].length) (baseStart_149399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149399 prefixEnd_149399 := by exact prefixLift 149399
  have htrace : WordTrace (prefixWord ++ tailWord_149399) baseStart_149399 baseEnd_149399 := by
    simpa [prefixWord, tailWord_149399, baseEnd_149399] using wordTrace_append hprefix tailTrace_149399
  have hstable : (prefixWord ++ tailWord_149399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149399).length < 2 ^ (prefixWord ++ tailWord_149399).sum := by decide
  have hdescent : baseEnd_149399 < baseStart_149399 := by decide
  rcases family_descends (prefixWord ++ tailWord_149399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149402 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_149402 : Nat := 118140960795 + 149402 * 2 ^ 59
def prefixEnd_149402 : Nat := 4983230072969 + 3 ^ 40 * 149402 * 2
def baseEnd_149402 : Nat := 68191143771670842389261

theorem tailTrace_149402 : CollatzResearch.WordTrace tailWord_149402 prefixEnd_149402 68191143771670842389261 := by
  unfold tailWord_149402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362284651187386168822615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3632759069833029783526973 1362284651187386168822615)
  ·
    refine ⟨2043426976781079253233923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1362284651187386168822615 2043426976781079253233923)
    ·
      refine ⟨3065140465171618879850885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043426976781079253233923 3065140465171618879850885)
      ·
        refine ⟨574713837219678539972041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3065140465171618879850885 574713837219678539972041)
        ·
          refine ⟨431035377914758904979031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574713837219678539972041 431035377914758904979031)
          ·
            refine ⟨646553066872138357468547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431035377914758904979031 646553066872138357468547)
            ·
              refine ⟨969829600308207536202821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646553066872138357468547 969829600308207536202821)
              ·
                refine ⟨181843050057788913038029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 969829600308207536202821 181843050057788913038029)
                ·
                  refine ⟨68191143771670842389261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181843050057788913038029 68191143771670842389261)
                  ·
                    rfl

theorem cell20_149402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_149402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149402 prefixEnd_149402 := by exact prefixLift 149402
  have htrace : WordTrace (prefixWord ++ tailWord_149402) baseStart_149402 baseEnd_149402 := by
    simpa [prefixWord, tailWord_149402, baseEnd_149402] using wordTrace_append hprefix tailTrace_149402
  have hstable : (prefixWord ++ tailWord_149402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149402).length < 2 ^ (prefixWord ++ tailWord_149402).sum := by decide
  have hdescent : baseEnd_149402 < baseStart_149402 := by decide
  rcases family_descends (prefixWord ++ tailWord_149402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149405 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 2]
def baseStart_149405 : Nat := 118140960795 + 149405 * 2 ^ 59
def prefixEnd_149405 : Nat := 4983230072969 + 3 ^ 40 * 149405 * 2
def baseEnd_149405 : Nat := 68192513053416165289249

theorem tailTrace_149405 : CollatzResearch.WordTrace tailWord_149405 prefixEnd_149405 68192513053416165289249 := by
  unfold tailWord_149405
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449248023738676187649669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3632832015825784125099779 5449248023738676187649669)
  ·
    refine ⟨1021734004451001785184313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5449248023738676187649669 1021734004451001785184313)
    ·
      refine ⟨766300503338251338888235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1021734004451001785184313 766300503338251338888235)
      ·
        refine ⟨1149450755007377008332353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766300503338251338888235 1149450755007377008332353)
        ·
          refine ⟨862088066255532756249265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149450755007377008332353 862088066255532756249265)
          ·
            refine ⟨646566049691649567186949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862088066255532756249265 646566049691649567186949)
            ·
              refine ⟨121231134317184293847553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 646566049691649567186949 121231134317184293847553)
              ·
                refine ⟨90923350737888220385665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121231134317184293847553 90923350737888220385665)
                ·
                  refine ⟨68192513053416165289249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90923350737888220385665 68192513053416165289249)
                  ·
                    rfl

theorem cell20_149405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_149405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149405 prefixEnd_149405 := by exact prefixLift 149405
  have htrace : WordTrace (prefixWord ++ tailWord_149405) baseStart_149405 baseEnd_149405 := by
    simpa [prefixWord, tailWord_149405, baseEnd_149405] using wordTrace_append hprefix tailTrace_149405
  have hstable : (prefixWord ++ tailWord_149405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149405).length < 2 ^ (prefixWord ++ tailWord_149405).sum := by decide
  have hdescent : baseEnd_149405 < baseStart_149405 := by decide
  rcases family_descends (prefixWord ++ tailWord_149405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149422 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_149422 : Nat := 118140960795 + 149422 * 2 ^ 59
def prefixEnd_149422 : Nat := 4983230072969 + 3 ^ 40 * 149422 * 2
def baseEnd_149422 : Nat := 68200272316639661722513

theorem tailTrace_149422 : CollatzResearch.WordTrace tailWord_149422 prefixEnd_149422 68200272316639661722513 := by
  unfold tailWord_149422
  simp only [CollatzResearch.WordTrace]
  refine ⟨681233508084636011377315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3633245376451392060679013 681233508084636011377315)
  ·
    refine ⟨1021850262126954017065973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 681233508084636011377315 1021850262126954017065973)
    ·
      refine ⟨95798462074401939099935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1021850262126954017065973 95798462074401939099935)
      ·
        refine ⟨143697693111602908649903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95798462074401939099935 143697693111602908649903)
        ·
          refine ⟨215546539667404362974855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143697693111602908649903 215546539667404362974855)
          ·
            refine ⟨323319809501106544462283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215546539667404362974855 323319809501106544462283)
            ·
              refine ⟨484979714251659816693425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323319809501106544462283 484979714251659816693425)
              ·
                refine ⟨363734785688744862520069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484979714251659816693425 363734785688744862520069)
                ·
                  refine ⟨68200272316639661722513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363734785688744862520069 68200272316639661722513)
                  ·
                    rfl

theorem cell20_149422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_149422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149422 prefixEnd_149422 := by exact prefixLift 149422
  have htrace : WordTrace (prefixWord ++ tailWord_149422) baseStart_149422 baseEnd_149422 := by
    simpa [prefixWord, tailWord_149422, baseEnd_149422] using wordTrace_append hprefix tailTrace_149422
  have hstable : (prefixWord ++ tailWord_149422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149422).length < 2 ^ (prefixWord ++ tailWord_149422).sum := by decide
  have hdescent : baseEnd_149422 < baseStart_149422 := by decide
  rcases family_descends (prefixWord ++ tailWord_149422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149423 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_149423 : Nat := 118140960795 + 149423 * 2 ^ 59
def prefixEnd_149423 : Nat := 4983230072969 + 3 ^ 40 * 149423 * 2
def baseEnd_149423 : Nat := 68200728743888102689175

theorem tailTrace_149423 : CollatzResearch.WordTrace tailWord_149423 prefixEnd_149423 68200728743888102689175 := by
  unfold tailWord_149423
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449904537673465261804923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3633269691782310174536615 5449904537673465261804923)
  ·
    refine ⟨8174856806510197892707385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5449904537673465261804923 8174856806510197892707385)
    ·
      refine ⟨6131142604882648419530539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8174856806510197892707385 6131142604882648419530539)
      ·
        refine ⟨9196713907323972629295809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6131142604882648419530539 9196713907323972629295809)
        ·
          refine ⟨6897535430492979471971857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9196713907323972629295809 6897535430492979471971857)
          ·
            refine ⟨5173151572869734603978893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6897535430492979471971857 5173151572869734603978893)
            ·
              refine ⟨1939931839826150476492085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5173151572869734603978893 1939931839826150476492085)
              ·
                refine ⟨181868609983701607171133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1939931839826150476492085 181868609983701607171133)
                ·
                  refine ⟨68200728743888102689175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181868609983701607171133 68200728743888102689175)
                  ·
                    rfl

theorem cell20_149423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_149423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149423 prefixEnd_149423 := by exact prefixLift 149423
  have htrace : WordTrace (prefixWord ++ tailWord_149423) baseStart_149423 baseEnd_149423 := by
    simpa [prefixWord, tailWord_149423, baseEnd_149423] using wordTrace_append hprefix tailTrace_149423
  have hstable : (prefixWord ++ tailWord_149423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149423).length < 2 ^ (prefixWord ++ tailWord_149423).sum := by decide
  have hdescent : baseEnd_149423 < baseStart_149423 := by decide
  rcases family_descends (prefixWord ++ tailWord_149423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149523 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 2]
def baseStart_149523 : Nat := 118140960795 + 149523 * 2 ^ 59
def prefixEnd_149523 : Nat := 4983230072969 + 3 ^ 40 * 149523 * 2
def baseEnd_149523 : Nat := 68246371468732199355433

theorem tailTrace_149523 : CollatzResearch.WordTrace tailWord_149523 prefixEnd_149523 68246371468732199355433 := by
  unfold tailWord_149523
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453551837311182340445223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3635701224874121560296815 5453551837311182340445223)
  ·
    refine ⟨8180327755966773510667835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5453551837311182340445223 8180327755966773510667835)
    ·
      refine ⟨12270491633950160266001753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8180327755966773510667835 12270491633950160266001753)
      ·
        refine ⟨9202868725462620199501315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12270491633950160266001753 9202868725462620199501315)
        ·
          refine ⟨13804303088193930299251973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202868725462620199501315 13804303088193930299251973)
          ·
            refine ⟨2588306829036361931109745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13804303088193930299251973 2588306829036361931109745)
            ·
              refine ⟨1941230121777271448332309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588306829036361931109745 1941230121777271448332309)
              ·
                refine ⟨90995161958309599140577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1941230121777271448332309 90995161958309599140577)
                ·
                  refine ⟨68246371468732199355433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90995161958309599140577 68246371468732199355433)
                  ·
                    rfl

theorem cell20_149523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 2].length) (baseStart_149523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149523 prefixEnd_149523 := by exact prefixLift 149523
  have htrace : WordTrace (prefixWord ++ tailWord_149523) baseStart_149523 baseEnd_149523 := by
    simpa [prefixWord, tailWord_149523, baseEnd_149523] using wordTrace_append hprefix tailTrace_149523
  have hstable : (prefixWord ++ tailWord_149523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149523).length < 2 ^ (prefixWord ++ tailWord_149523).sum := by decide
  have hdescent : baseEnd_149523 < baseStart_149523 := by decide
  rcases family_descends (prefixWord ++ tailWord_149523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149530 : List Nat := [3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_149530 : Nat := 118140960795 + 149530 * 2 ^ 59
def prefixEnd_149530 : Nat := 4983230072969 + 3 ^ 40 * 149530 * 2
def baseEnd_149530 : Nat := 22749855486490428707357

theorem tailTrace_149530 : CollatzResearch.WordTrace tailWord_149530 prefixEnd_149530 22749855486490428707357 := by
  unfold tailWord_149530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363451787071455633987511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3635871432190548357300029 1363451787071455633987511)
  ·
    refine ⟨2045177680607183450981267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1363451787071455633987511 2045177680607183450981267)
    ·
      refine ⟨3067766520910775176471901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2045177680607183450981267 3067766520910775176471901)
      ·
        refine ⟨1150412445341540691176963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3067766520910775176471901 1150412445341540691176963)
        ·
          refine ⟨1725618668012311036765445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150412445341540691176963 1725618668012311036765445)
          ·
            refine ⟨323553500252308319393521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1725618668012311036765445 323553500252308319393521)
            ·
              refine ⟨242665125189231239545141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323553500252308319393521 242665125189231239545141)
              ·
                refine ⟨22749855486490428707357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242665125189231239545141 22749855486490428707357)
                ·
                  rfl

theorem cell20_149530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_149530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149530 prefixEnd_149530 := by exact prefixLift 149530
  have htrace : WordTrace (prefixWord ++ tailWord_149530) baseStart_149530 baseEnd_149530 := by
    simpa [prefixWord, tailWord_149530, baseEnd_149530] using wordTrace_append hprefix tailTrace_149530
  have hstable : (prefixWord ++ tailWord_149530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149530).length < 2 ^ (prefixWord ++ tailWord_149530).sum := by decide
  have hdescent : baseEnd_149530 < baseStart_149530 := by decide
  rcases family_descends (prefixWord ++ tailWord_149530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149533 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 3]
def baseStart_149533 : Nat := 118140960795 + 149533 * 2 ^ 59
def prefixEnd_149533 : Nat := 4983230072969 + 3 ^ 40 * 149533 * 2
def baseEnd_149533 : Nat := 68250935741216609022059

theorem tailTrace_149533 : CollatzResearch.WordTrace tailWord_149533 prefixEnd_149533 68250935741216609022059 := by
  unfold tailWord_149533
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453916567274954048309253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3635944378183302698872835 5453916567274954048309253)
  ·
    refine ⟨1022609356364053884057985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5453916567274954048309253 1022609356364053884057985)
    ·
      refine ⟨766957017273040413043489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1022609356364053884057985 766957017273040413043489)
      ·
        refine ⟨575217762954780309782617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 766957017273040413043489 575217762954780309782617)
        ·
          refine ⟨431413322216085232336963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575217762954780309782617 431413322216085232336963)
          ·
            refine ⟨647119983324127848505445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431413322216085232336963 647119983324127848505445)
            ·
              refine ⟨121334996873273971594771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 647119983324127848505445 121334996873273971594771)
              ·
                refine ⟨182002495309910957392157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121334996873273971594771 182002495309910957392157)
                ·
                  refine ⟨68250935741216609022059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182002495309910957392157 68250935741216609022059)
                  ·
                    rfl

theorem cell20_149533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_149533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149533 prefixEnd_149533 := by exact prefixLift 149533
  have htrace : WordTrace (prefixWord ++ tailWord_149533) baseStart_149533 baseEnd_149533 := by
    simpa [prefixWord, tailWord_149533, baseEnd_149533] using wordTrace_append hprefix tailTrace_149533
  have hstable : (prefixWord ++ tailWord_149533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149533).length < 2 ^ (prefixWord ++ tailWord_149533).sum := by decide
  have hdescent : baseEnd_149533 < baseStart_149533 := by decide
  rcases family_descends (prefixWord ++ tailWord_149533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149602 : List Nat := [3, 3, 2, 2, 2, 1, 3, 4]
def baseStart_149602 : Nat := 118140960795 + 149602 * 2 ^ 59
def prefixEnd_149602 : Nat := 4983230072969 + 3 ^ 40 * 149602 * 2
def baseEnd_149602 : Nat := 22760809740453011907259

theorem tailTrace_149602 : CollatzResearch.WordTrace tailWord_149602 prefixEnd_149602 22760809740453011907259 := by
  unfold tailWord_149602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364108301006244708142765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3637622136016652555047373 1364108301006244708142765)
  ·
    refine ⟨511540612877341765553537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1364108301006244708142765 511540612877341765553537)
    ·
      refine ⟨383655459658006324165153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 511540612877341765553537 383655459658006324165153)
      ·
        refine ⟨287741594743504743123865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383655459658006324165153 287741594743504743123865)
        ·
          refine ⟨215806196057628557342899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287741594743504743123865 215806196057628557342899)
          ·
            refine ⟨323709294086442836014349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215806196057628557342899 323709294086442836014349)
            ·
              refine ⟨121390985282416063505381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323709294086442836014349 121390985282416063505381)
              ·
                refine ⟨22760809740453011907259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121390985282416063505381 22760809740453011907259)
                ·
                  rfl

theorem cell20_149602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_149602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149602 prefixEnd_149602 := by exact prefixLift 149602
  have htrace : WordTrace (prefixWord ++ tailWord_149602) baseStart_149602 baseEnd_149602 := by
    simpa [prefixWord, tailWord_149602, baseEnd_149602] using wordTrace_append hprefix tailTrace_149602
  have hstable : (prefixWord ++ tailWord_149602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149602).length < 2 ^ (prefixWord ++ tailWord_149602).sum := by decide
  have hdescent : baseEnd_149602 < baseStart_149602 := by decide
  rcases family_descends (prefixWord ++ tailWord_149602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149613 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_149613 : Nat := 118140960795 + 149613 * 2 ^ 59
def prefixEnd_149613 : Nat := 4983230072969 + 3 ^ 40 * 149613 * 2
def baseEnd_149613 : Nat := 68287449921091886355065

theorem tailTrace_149613 : CollatzResearch.WordTrace tailWord_149613 prefixEnd_149613 68287449921091886355065 := by
  unfold tailWord_149613
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456834406985127711221493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3637889604656751807480995 5456834406985127711221493)
  ·
    refine ⟨511578225654855722927015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5456834406985127711221493 511578225654855722927015)
    ·
      refine ⟨767367338482283584390523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511578225654855722927015 767367338482283584390523)
      ·
        refine ⟨1151051007723425376585785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767367338482283584390523 1151051007723425376585785)
        ·
          refine ⟨863288255792569032439339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151051007723425376585785 863288255792569032439339)
          ·
            refine ⟨1294932383688853548659009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863288255792569032439339 1294932383688853548659009)
            ·
              refine ⟨971199287766640161494257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294932383688853548659009 971199287766640161494257)
              ·
                refine ⟨728399465824980121120693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971199287766640161494257 728399465824980121120693)
                ·
                  refine ⟨68287449921091886355065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 728399465824980121120693 68287449921091886355065)
                  ·
                    rfl

theorem cell20_149613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_149613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149613 prefixEnd_149613 := by exact prefixLift 149613
  have htrace : WordTrace (prefixWord ++ tailWord_149613) baseStart_149613 baseEnd_149613 := by
    simpa [prefixWord, tailWord_149613, baseEnd_149613] using wordTrace_append hprefix tailTrace_149613
  have hstable : (prefixWord ++ tailWord_149613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149613).length < 2 ^ (prefixWord ++ tailWord_149613).sum := by decide
  have hdescent : baseEnd_149613 < baseStart_149613 := by decide
  rcases family_descends (prefixWord ++ tailWord_149613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149616 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 2]
def baseStart_149616 : Nat := 118140960795 + 149616 * 2 ^ 59
def prefixEnd_149616 : Nat := 4983230072969 + 3 ^ 40 * 149616 * 2
def baseEnd_149616 : Nat := 68288819202837209255053

theorem tailTrace_149616 : CollatzResearch.WordTrace tailWord_149616 prefixEnd_149616 68288819202837209255053 := by
  unfold tailWord_149616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2728471912987129611790351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3637962550649506149053801 2728471912987129611790351)
  ·
    refine ⟨4092707869480694417685527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2728471912987129611790351 4092707869480694417685527)
    ·
      refine ⟨6139061804221041626528291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092707869480694417685527 6139061804221041626528291)
      ·
        refine ⟨9208592706331562439792437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139061804221041626528291 9208592706331562439792437)
        ·
          refine ⟨863305566218583978730541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9208592706331562439792437 863305566218583978730541)
          ·
            refine ⟨323739587331968992023953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863305566218583978730541 323739587331968992023953)
            ·
              refine ⟨242804690498976744017965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323739587331968992023953 242804690498976744017965)
              ·
                refine ⟨91051758937116279006737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242804690498976744017965 91051758937116279006737)
                ·
                  refine ⟨68288819202837209255053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91051758937116279006737 68288819202837209255053)
                  ·
                    rfl

theorem cell20_149616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_149616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149616 prefixEnd_149616 := by exact prefixLift 149616
  have htrace : WordTrace (prefixWord ++ tailWord_149616) baseStart_149616 baseEnd_149616 := by
    simpa [prefixWord, tailWord_149616, baseEnd_149616] using wordTrace_append hprefix tailTrace_149616
  have hstable : (prefixWord ++ tailWord_149616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149616).length < 2 ^ (prefixWord ++ tailWord_149616).sum := by decide
  have hdescent : baseEnd_149616 < baseStart_149616 := by decide
  rcases family_descends (prefixWord ++ tailWord_149616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149637 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_149637 : Nat := 118140960795 + 149637 * 2 ^ 59
def prefixEnd_149637 : Nat := 4983230072969 + 3 ^ 40 * 149637 * 2
def baseEnd_149637 : Nat := 68298404175054469554967

theorem tailTrace_149637 : CollatzResearch.WordTrace tailWord_149637 prefixEnd_149637 68298404175054469554967 := by
  unfold tailWord_149637
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457709758898179810095165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3638473172598786540063443 5457709758898179810095165)
  ·
    refine ⟨2046641159586817428785687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5457709758898179810095165 2046641159586817428785687)
    ·
      refine ⟨3069961739380226143178531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046641159586817428785687 3069961739380226143178531)
      ·
        refine ⟨4604942609070339214767797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3069961739380226143178531 4604942609070339214767797)
        ·
          refine ⟨431713369600344301384481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4604942609070339214767797 431713369600344301384481)
          ·
            refine ⟨323785027200258226038361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431713369600344301384481 323785027200258226038361)
            ·
              refine ⟨242838770400193669528771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323785027200258226038361 242838770400193669528771)
              ·
                refine ⟨364258155600290504293157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242838770400193669528771 364258155600290504293157)
                ·
                  refine ⟨68298404175054469554967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364258155600290504293157 68298404175054469554967)
                  ·
                    rfl

theorem cell20_149637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_149637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149637 prefixEnd_149637 := by exact prefixLift 149637
  have htrace : WordTrace (prefixWord ++ tailWord_149637) baseStart_149637 baseEnd_149637 := by
    simpa [prefixWord, tailWord_149637, baseEnd_149637] using wordTrace_append hprefix tailTrace_149637
  have hstable : (prefixWord ++ tailWord_149637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149637).length < 2 ^ (prefixWord ++ tailWord_149637).sum := by decide
  have hdescent : baseEnd_149637 < baseStart_149637 := by decide
  rcases family_descends (prefixWord ++ tailWord_149637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149661 : List Nat := [1, 4, 2, 1, 1, 5, 2, 4]
def baseStart_149661 : Nat := 118140960795 + 149661 * 2 ^ 59
def prefixEnd_149661 : Nat := 4983230072969 + 3 ^ 40 * 149661 * 2
def baseEnd_149661 : Nat := 22769786143005684251623

theorem tailTrace_149661 : CollatzResearch.WordTrace tailWord_149661 prefixEnd_149661 22769786143005684251623 := by
  unfold tailWord_149661
  simp only [CollatzResearch.WordTrace]
  refine ⟨5458585110811231908968837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639056740540821272645891 5458585110811231908968837)
  ·
    refine ⟨1023484708277105982931657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5458585110811231908968837 1023484708277105982931657)
    ·
      refine ⟨767613531207829487198743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1023484708277105982931657 767613531207829487198743)
      ·
        refine ⟨1151420296811744230798115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767613531207829487198743 1151420296811744230798115)
        ·
          refine ⟨1727130445217616346197173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151420296811744230798115 1727130445217616346197173)
          ·
            refine ⟨161918479239151532455985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1727130445217616346197173 161918479239151532455985)
            ·
              refine ⟨121438859429363649341989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161918479239151532455985 121438859429363649341989)
              ·
                refine ⟨22769786143005684251623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121438859429363649341989 22769786143005684251623)
                ·
                  rfl

theorem cell20_149661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_149661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149661 prefixEnd_149661 := by exact prefixLift 149661
  have htrace : WordTrace (prefixWord ++ tailWord_149661) baseStart_149661 baseEnd_149661 := by
    simpa [prefixWord, tailWord_149661, baseEnd_149661] using wordTrace_append hprefix tailTrace_149661
  have hstable : (prefixWord ++ tailWord_149661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149661).length < 2 ^ (prefixWord ++ tailWord_149661).sum := by decide
  have hdescent : baseEnd_149661 < baseStart_149661 := by decide
  rcases family_descends (prefixWord ++ tailWord_149661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149678 : List Nat := [4, 1, 4, 2, 1, 2, 6]
def baseStart_149678 : Nat := 118140960795 + 149678 * 2 ^ 59
def prefixEnd_149678 : Nat := 4983230072969 + 3 ^ 40 * 149678 * 2
def baseEnd_149678 : Nat := 7590790854693394354237

theorem tailTrace_149678 : CollatzResearch.WordTrace tailWord_149678 prefixEnd_149678 7590790854693394354237 := by
  unfold tailWord_149678
  simp only [CollatzResearch.WordTrace]
  refine ⟨682400643968705476542211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3639470101166429208225125 682400643968705476542211)
  ·
    refine ⟨1023600965953058214813317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 682400643968705476542211 1023600965953058214813317)
    ·
      refine ⟨191925181116198415277497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1023600965953058214813317 191925181116198415277497)
      ·
        refine ⟨143943885837148811458123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191925181116198415277497 143943885837148811458123)
        ·
          refine ⟨215915828755723217187185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143943885837148811458123 215915828755723217187185)
          ·
            refine ⟨161936871566792412890389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215915828755723217187185 161936871566792412890389)
            ·
              refine ⟨7590790854693394354237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161936871566792412890389 7590790854693394354237)
              ·
                rfl

theorem cell20_149678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 6].length) (baseStart_149678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149678 prefixEnd_149678 := by exact prefixLift 149678
  have htrace : WordTrace (prefixWord ++ tailWord_149678) baseStart_149678 baseEnd_149678 := by
    simpa [prefixWord, tailWord_149678, baseEnd_149678] using wordTrace_append hprefix tailTrace_149678
  have hstable : (prefixWord ++ tailWord_149678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149678).length < 2 ^ (prefixWord ++ tailWord_149678).sum := by decide
  have hdescent : baseEnd_149678 < baseStart_149678 := by decide
  rcases family_descends (prefixWord ++ tailWord_149678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149684 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 2]
def baseStart_149684 : Nat := 118140960795 + 149684 * 2 ^ 59
def prefixEnd_149684 : Nat := 4983230072969 + 3 ^ 40 * 149684 * 2
def baseEnd_149684 : Nat := 68319856255731194988109

theorem tailTrace_149684 : CollatzResearch.WordTrace tailWord_149684 prefixEnd_149684 68319856255731194988109 := by
  unfold tailWord_149684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729711994863953418528053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3639615993151937891370737 2729711994863953418528053)
  ·
    refine ⟨255910499518495632987005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2729711994863953418528053 255910499518495632987005)
    ·
      refine ⟨95966437319435862370127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255910499518495632987005 95966437319435862370127)
      ·
        refine ⟨143949655979153793555191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95966437319435862370127 143949655979153793555191)
        ·
          refine ⟨215924483968730690332787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143949655979153793555191 215924483968730690332787)
          ·
            refine ⟨323886725953096035499181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215924483968730690332787 323886725953096035499181)
            ·
              refine ⟨121457522232411013312193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323886725953096035499181 121457522232411013312193)
              ·
                refine ⟨91093141674308259984145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121457522232411013312193 91093141674308259984145)
                ·
                  refine ⟨68319856255731194988109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91093141674308259984145 68319856255731194988109)
                  ·
                    rfl

theorem cell20_149684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_149684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149684 prefixEnd_149684 := by exact prefixLift 149684
  have htrace : WordTrace (prefixWord ++ tailWord_149684) baseStart_149684 baseEnd_149684 := by
    simpa [prefixWord, tailWord_149684, baseEnd_149684] using wordTrace_append hprefix tailTrace_149684
  have hstable : (prefixWord ++ tailWord_149684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149684).length < 2 ^ (prefixWord ++ tailWord_149684).sum := by decide
  have hdescent : baseEnd_149684 < baseStart_149684 := by decide
  rcases family_descends (prefixWord ++ tailWord_149684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149689 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_149689 : Nat := 118140960795 + 149689 * 2 ^ 59
def prefixEnd_149689 : Nat := 4983230072969 + 3 ^ 40 * 149689 * 2
def baseEnd_149689 : Nat := 68322138391973399821421

theorem tailTrace_149689 : CollatzResearch.WordTrace tailWord_149689 prefixEnd_149689 68322138391973399821421 := by
  unfold tailWord_149689
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459606354709792690988121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639737569806528460658747 5459606354709792690988121)
  ·
    refine ⟨4094704766032344518241091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5459606354709792690988121 4094704766032344518241091)
    ·
      refine ⟨6142057149048516777361637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094704766032344518241091 6142057149048516777361637)
      ·
        refine ⟨1151635715446596895755307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6142057149048516777361637 1151635715446596895755307)
        ·
          refine ⟨1727453573169895343632961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151635715446596895755307 1727453573169895343632961)
          ·
            refine ⟨1295590179877421507724721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727453573169895343632961 1295590179877421507724721)
            ·
              refine ⟨971692634908066130793541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295590179877421507724721 971692634908066130793541)
              ·
                refine ⟨182192369045262399523789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 971692634908066130793541 182192369045262399523789)
                ·
                  refine ⟨68322138391973399821421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182192369045262399523789 68322138391973399821421)
                  ·
                    rfl

theorem cell20_149689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_149689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149689 prefixEnd_149689 := by exact prefixLift 149689
  have htrace : WordTrace (prefixWord ++ tailWord_149689) baseStart_149689 baseEnd_149689 := by
    simpa [prefixWord, tailWord_149689, baseEnd_149689] using wordTrace_append hprefix tailTrace_149689
  have hstable : (prefixWord ++ tailWord_149689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149689).length < 2 ^ (prefixWord ++ tailWord_149689).sum := by decide
  have hdescent : baseEnd_149689 < baseStart_149689 := by decide
  rcases family_descends (prefixWord ++ tailWord_149689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149692 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_149692 : Nat := 118140960795 + 149692 * 2 ^ 59
def prefixEnd_149692 : Nat := 4983230072969 + 3 ^ 40 * 149692 * 2
def baseEnd_149692 : Nat := 68323507673718722721409

theorem tailTrace_149692 : CollatzResearch.WordTrace tailWord_149692 prefixEnd_149692 68323507673718722721409 := by
  unfold tailWord_149692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729857886849462101673665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3639810515799282802231553 2729857886849462101673665)
  ·
    refine ⟨2047393415137096576255249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2729857886849462101673665 2047393415137096576255249)
    ·
      refine ⟨1535545061352822432191437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2047393415137096576255249 1535545061352822432191437)
      ·
        refine ⟨575829398007308412071789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1535545061352822432191437 575829398007308412071789)
        ·
          refine ⟨215936024252740654526921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 575829398007308412071789 215936024252740654526921)
          ·
            refine ⟨161952018189555490895191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215936024252740654526921 161952018189555490895191)
            ·
              refine ⟨242928027284333236342787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161952018189555490895191 242928027284333236342787)
              ·
                refine ⟨364392040926499854514181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242928027284333236342787 364392040926499854514181)
                ·
                  refine ⟨68323507673718722721409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364392040926499854514181 68323507673718722721409)
                  ·
                    rfl

theorem cell20_149692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_149692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149692 prefixEnd_149692 := by exact prefixLift 149692
  have htrace : WordTrace (prefixWord ++ tailWord_149692) baseStart_149692 baseEnd_149692 := by
    simpa [prefixWord, tailWord_149692, baseEnd_149692] using wordTrace_append hprefix tailTrace_149692
  have hstable : (prefixWord ++ tailWord_149692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149692).length < 2 ^ (prefixWord ++ tailWord_149692).sum := by decide
  have hdescent : baseEnd_149692 < baseStart_149692 := by decide
  rcases family_descends (prefixWord ++ tailWord_149692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149741 : List Nat := [1, 5, 1, 2, 11]
def baseStart_149741 : Nat := 118140960795 + 149741 * 2 ^ 59
def prefixEnd_149741 : Nat := 4983230072969 + 3 ^ 40 * 149741 * 2
def baseEnd_149741 : Nat := 843776205048053457875

theorem tailTrace_149741 : CollatzResearch.WordTrace tailWord_149741 prefixEnd_149741 843776205048053457875 := by
  unfold tailWord_149741
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461502950521405571881077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3641001967014270381254051 5461502950521405571881077)
  ·
    refine ⟨512015901611381772363851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5461502950521405571881077 512015901611381772363851)
    ·
      refine ⟨768023852417072658545777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512015901611381772363851 768023852417072658545777)
      ·
        refine ⟨576017889312804493909333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 768023852417072658545777 576017889312804493909333)
        ·
          refine ⟨843776205048053457875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 576017889312804493909333 843776205048053457875)
          ·
            rfl

theorem cell20_149741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 11].length) (baseStart_149741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149741 prefixEnd_149741 := by exact prefixLift 149741
  have htrace : WordTrace (prefixWord ++ tailWord_149741) baseStart_149741 baseEnd_149741 := by
    simpa [prefixWord, tailWord_149741, baseEnd_149741] using wordTrace_append hprefix tailTrace_149741
  have hstable : (prefixWord ++ tailWord_149741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149741).length < 2 ^ (prefixWord ++ tailWord_149741).sum := by decide
  have hdescent : baseEnd_149741 < baseStart_149741 := by decide
  rcases family_descends (prefixWord ++ tailWord_149741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149755 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_149755 : Nat := 118140960795 + 149755 * 2 ^ 59
def prefixEnd_149755 : Nat := 4983230072969 + 3 ^ 40 * 149755 * 2
def baseEnd_149755 : Nat := 68352262590370503621151

theorem tailTrace_149755 : CollatzResearch.WordTrace tailWord_149755 prefixEnd_149755 68352262590370503621151 := by
  unfold tailWord_149755
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462013572470685962890719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3641342381647123975260479 5462013572470685962890719)
  ·
    refine ⟨8193020358706028944336079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5462013572470685962890719 8193020358706028944336079)
    ·
      refine ⟨12289530538059043416504119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8193020358706028944336079 12289530538059043416504119)
      ·
        refine ⟨18434295807088565124756179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12289530538059043416504119 18434295807088565124756179)
        ·
          refine ⟨27651443710632847687134269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18434295807088565124756179 27651443710632847687134269)
          ·
            refine ⟨10369291391487317882675351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27651443710632847687134269 10369291391487317882675351)
            ·
              refine ⟨15553937087230976824013027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10369291391487317882675351 15553937087230976824013027)
              ·
                refine ⟨23330905630846465236019541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15553937087230976824013027 23330905630846465236019541)
                ·
                  refine ⟨68352262590370503621151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 23330905630846465236019541 68352262590370503621151)
                  ·
                    rfl

theorem cell20_149755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_149755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149755 prefixEnd_149755 := by exact prefixLift 149755
  have htrace : WordTrace (prefixWord ++ tailWord_149755) baseStart_149755 baseEnd_149755 := by
    simpa [prefixWord, tailWord_149755, baseEnd_149755] using wordTrace_append hprefix tailTrace_149755
  have hstable : (prefixWord ++ tailWord_149755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149755).length < 2 ^ (prefixWord ++ tailWord_149755).sum := by decide
  have hdescent : baseEnd_149755 < baseStart_149755 := by decide
  rcases family_descends (prefixWord ++ tailWord_149755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149772 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_149772 : Nat := 118140960795 + 149772 * 2 ^ 59
def prefixEnd_149772 : Nat := 4983230072969 + 3 ^ 40 * 149772 * 2
def baseEnd_149772 : Nat := 68360021853594000054415

theorem tailTrace_149772 : CollatzResearch.WordTrace tailWord_149772 prefixEnd_149772 68360021853594000054415 := by
  unfold tailWord_149772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731316806704548933129785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3641755742272731910839713 2731316806704548933129785)
  ·
    refine ⟨2048487605028411699847339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2731316806704548933129785 2048487605028411699847339)
    ·
      refine ⟨3072731407542617549771009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048487605028411699847339 3072731407542617549771009)
      ·
        refine ⟨2304548555656963162328257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3072731407542617549771009 2304548555656963162328257)
        ·
          refine ⟨1728411416742722371746193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304548555656963162328257 1728411416742722371746193)
          ·
            refine ⟨1296308562557041778809645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728411416742722371746193 1296308562557041778809645)
            ·
              refine ⟨486115710958890667053617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1296308562557041778809645 486115710958890667053617)
              ·
                refine ⟨364586783219168000290213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486115710958890667053617 364586783219168000290213)
                ·
                  refine ⟨68360021853594000054415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364586783219168000290213 68360021853594000054415)
                  ·
                    rfl

theorem cell20_149772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_149772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149772 prefixEnd_149772 := by exact prefixLift 149772
  have htrace : WordTrace (prefixWord ++ tailWord_149772) baseStart_149772 baseEnd_149772 := by
    simpa [prefixWord, tailWord_149772, baseEnd_149772] using wordTrace_append hprefix tailTrace_149772
  have hstable : (prefixWord ++ tailWord_149772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149772).length < 2 ^ (prefixWord ++ tailWord_149772).sum := by decide
  have hdescent : baseEnd_149772 < baseStart_149772 := by decide
  rcases family_descends (prefixWord ++ tailWord_149772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149820 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_149820 : Nat := 118140960795 + 149820 * 2 ^ 59
def prefixEnd_149820 : Nat := 4983230072969 + 3 ^ 40 * 149820 * 2
def baseEnd_149820 : Nat := 68381930361519166454219

theorem tailTrace_149820 : CollatzResearch.WordTrace tailWord_149820 prefixEnd_149820 68381930361519166454219 := by
  unfold tailWord_149820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732192158617601032003457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3642922878156801376004609 2732192158617601032003457)
  ·
    refine ⟨2049144118963200774002593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2732192158617601032003457 2049144118963200774002593)
    ·
      refine ⟨1536858089222400580501945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2049144118963200774002593 1536858089222400580501945)
      ·
        refine ⟨1152643566916800435376459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536858089222400580501945 1152643566916800435376459)
        ·
          refine ⟨1728965350375200653064689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152643566916800435376459 1728965350375200653064689)
          ·
            refine ⟨1296724012781400489798517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728965350375200653064689 1296724012781400489798517)
            ·
              refine ⟨121567876198256295918611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1296724012781400489798517 121567876198256295918611)
              ·
                refine ⟨182351814297384443877917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121567876198256295918611 182351814297384443877917)
                ·
                  refine ⟨68381930361519166454219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182351814297384443877917 68381930361519166454219)
                  ·
                    rfl

theorem cell20_149820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_149820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149820 prefixEnd_149820 := by exact prefixLift 149820
  have htrace : WordTrace (prefixWord ++ tailWord_149820) baseStart_149820 baseEnd_149820 := by
    simpa [prefixWord, tailWord_149820, baseEnd_149820] using wordTrace_append hprefix tailTrace_149820
  have hstable : (prefixWord ++ tailWord_149820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149820).length < 2 ^ (prefixWord ++ tailWord_149820).sum := by decide
  have hdescent : baseEnd_149820 < baseStart_149820 := by decide
  rcases family_descends (prefixWord ++ tailWord_149820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149844 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 2]
def baseStart_149844 : Nat := 118140960795 + 149844 * 2 ^ 59
def prefixEnd_149844 : Nat := 4983230072969 + 3 ^ 40 * 149844 * 2
def baseEnd_149844 : Nat := 68392884615481749654121

theorem tailTrace_149844 : CollatzResearch.WordTrace tailWord_149844 prefixEnd_149844 68392884615481749654121 := by
  unfold tailWord_149844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732629834574127081440293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3643506446098836108587057 2732629834574127081440293)
  ·
    refine ⟨512368093982648827770055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2732629834574127081440293 512368093982648827770055)
    ·
      refine ⟨768552140973973241655083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512368093982648827770055 768552140973973241655083)
      ·
        refine ⟨1152828211460959862482625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768552140973973241655083 1152828211460959862482625)
        ·
          refine ⟨864621158595719896861969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152828211460959862482625 864621158595719896861969)
          ·
            refine ⟨648465868946789922646477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864621158595719896861969 648465868946789922646477)
            ·
              refine ⟨243174700855046220992429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 648465868946789922646477 243174700855046220992429)
              ·
                refine ⟨91190512820642332872161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243174700855046220992429 91190512820642332872161)
                ·
                  refine ⟨68392884615481749654121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91190512820642332872161 68392884615481749654121)
                  ·
                    rfl

theorem cell20_149844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_149844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149844 prefixEnd_149844 := by exact prefixLift 149844
  have htrace : WordTrace (prefixWord ++ tailWord_149844) baseStart_149844 baseEnd_149844 := by
    simpa [prefixWord, tailWord_149844, baseEnd_149844] using wordTrace_append hprefix tailTrace_149844
  have hstable : (prefixWord ++ tailWord_149844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149844).length < 2 ^ (prefixWord ++ tailWord_149844).sum := by decide
  have hdescent : baseEnd_149844 < baseStart_149844 := by decide
  rcases family_descends (prefixWord ++ tailWord_149844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149920 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 2]
def baseStart_149920 : Nat := 118140960795 + 149920 * 2 ^ 59
def prefixEnd_149920 : Nat := 4983230072969 + 3 ^ 40 * 149920 * 2
def baseEnd_149920 : Nat := 68427573086363263120477

theorem tailTrace_149920 : CollatzResearch.WordTrace tailWord_149920 prefixEnd_149920 68427573086363263120477 := by
  unfold tailWord_149920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734015808436459571323607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3645354411248612761764809 2734015808436459571323607)
  ·
    refine ⟨4101023712654689356985411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2734015808436459571323607 4101023712654689356985411)
    ·
      refine ⟨6151535568982034035478117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101023712654689356985411 6151535568982034035478117)
      ·
        refine ⟨1153412919184131381652147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6151535568982034035478117 1153412919184131381652147)
        ·
          refine ⟨1730119378776197072478221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153412919184131381652147 1730119378776197072478221)
          ·
            refine ⟨648794767041073902179333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1730119378776197072478221 648794767041073902179333)
            ·
              refine ⟨121649018820201356658625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 648794767041073902179333 121649018820201356658625)
              ·
                refine ⟨91236764115151017493969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121649018820201356658625 91236764115151017493969)
                ·
                  refine ⟨68427573086363263120477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91236764115151017493969 68427573086363263120477)
                  ·
                    rfl

theorem cell20_149920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_149920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149920 prefixEnd_149920 := by exact prefixLift 149920
  have htrace : WordTrace (prefixWord ++ tailWord_149920) baseStart_149920 baseEnd_149920 := by
    simpa [prefixWord, tailWord_149920, baseEnd_149920] using wordTrace_append hprefix tailTrace_149920
  have hstable : (prefixWord ++ tailWord_149920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149920).length < 2 ^ (prefixWord ++ tailWord_149920).sum := by decide
  have hdescent : baseEnd_149920 < baseStart_149920 := by decide
  rcases family_descends (prefixWord ++ tailWord_149920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149941 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_149941 : Nat := 118140960795 + 149941 * 2 ^ 59
def prefixEnd_149941 : Nat := 4983230072969 + 3 ^ 40 * 149941 * 2
def baseEnd_149941 : Nat := 68437158058580523420391

theorem tailTrace_149941 : CollatzResearch.WordTrace tailWord_149941 prefixEnd_149941 68437158058580523420391 := by
  unfold tailWord_149941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468797549796839729161677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3645865033197893152774451 5468797549796839729161677)
  ·
    refine ⟨2050799081173814898435629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5468797549796839729161677 2050799081173814898435629)
    ·
      refine ⟨769049655440180586913361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2050799081173814898435629 769049655440180586913361)
      ·
        refine ⟨576787241580135440185021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769049655440180586913361 576787241580135440185021)
        ·
          refine ⟨216295215592550790069383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 576787241580135440185021 216295215592550790069383)
          ·
            refine ⟨324442823388826185104075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216295215592550790069383 324442823388826185104075)
            ·
              refine ⟨486664235083239277656113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324442823388826185104075 486664235083239277656113)
              ·
                refine ⟨364998176312429458242085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486664235083239277656113 364998176312429458242085)
                ·
                  refine ⟨68437158058580523420391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364998176312429458242085 68437158058580523420391)
                  ·
                    rfl

theorem cell20_149941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_149941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149941 prefixEnd_149941 := by exact prefixLift 149941
  have htrace : WordTrace (prefixWord ++ tailWord_149941) baseStart_149941 baseEnd_149941 := by
    simpa [prefixWord, tailWord_149941, baseEnd_149941] using wordTrace_append hprefix tailTrace_149941
  have hstable : (prefixWord ++ tailWord_149941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149941).length < 2 ^ (prefixWord ++ tailWord_149941).sum := by decide
  have hdescent : baseEnd_149941 < baseStart_149941 := by decide
  rcases family_descends (prefixWord ++ tailWord_149941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149972 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_149972 : Nat := 118140960795 + 149972 * 2 ^ 59
def prefixEnd_149972 : Nat := 4983230072969 + 3 ^ 40 * 149972 * 2
def baseEnd_149972 : Nat := 68451307303282193386931

theorem tailTrace_149972 : CollatzResearch.WordTrace tailWord_149972 prefixEnd_149972 68451307303282193386931 := by
  unfold tailWord_149972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734964106342266011770085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3646618808456354682360113 2734964106342266011770085)
  ·
    refine ⟨512805769939174877206891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2734964106342266011770085 512805769939174877206891)
    ·
      refine ⟨769208654908762315810337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512805769939174877206891 769208654908762315810337)
      ·
        refine ⟨576906491181571736857753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769208654908762315810337 576906491181571736857753)
        ·
          refine ⟨432679868386178802643315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576906491181571736857753 432679868386178802643315)
          ·
            refine ⟨649019802579268203964973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432679868386178802643315 649019802579268203964973)
            ·
              refine ⟨243382425967225576486865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649019802579268203964973 243382425967225576486865)
              ·
                refine ⟨182536819475419182365149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243382425967225576486865 182536819475419182365149)
                ·
                  refine ⟨68451307303282193386931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182536819475419182365149 68451307303282193386931)
                  ·
                    rfl

theorem cell20_149972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_149972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149972 prefixEnd_149972 := by exact prefixLift 149972
  have htrace : WordTrace (prefixWord ++ tailWord_149972) baseStart_149972 baseEnd_149972 := by
    simpa [prefixWord, tailWord_149972, baseEnd_149972] using wordTrace_append hprefix tailTrace_149972
  have hstable : (prefixWord ++ tailWord_149972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149972).length < 2 ^ (prefixWord ++ tailWord_149972).sum := by decide
  have hdescent : baseEnd_149972 < baseStart_149972 := by decide
  rcases family_descends (prefixWord ++ tailWord_149972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149989 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 3]
def baseStart_149989 : Nat := 118140960795 + 149989 * 2 ^ 59
def prefixEnd_149989 : Nat := 4983230072969 + 3 ^ 40 * 149989 * 2
def baseEnd_149989 : Nat := 68459066566505689820195

theorem tailTrace_149989 : CollatzResearch.WordTrace tailWord_149989 prefixEnd_149989 68459066566505689820195 := by
  unfold tailWord_149989
  simp only [CollatzResearch.WordTrace]
  refine ⟨5470548253622943926909021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3647032169081962617939347 5470548253622943926909021)
  ·
    refine ⟨2051455595108603972590883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5470548253622943926909021 2051455595108603972590883)
    ·
      refine ⟨3077183392662905958886325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051455595108603972590883 3077183392662905958886325)
      ·
        refine ⟨288485943062147433645593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3077183392662905958886325 288485943062147433645593)
        ·
          refine ⟨216364457296610575234195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288485943062147433645593 216364457296610575234195)
          ·
            refine ⟨324546685944915862851293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216364457296610575234195 324546685944915862851293)
            ·
              refine ⟨121705007229343448569235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324546685944915862851293 121705007229343448569235)
              ·
                refine ⟨182557510844015172853853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121705007229343448569235 182557510844015172853853)
                ·
                  refine ⟨68459066566505689820195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182557510844015172853853 68459066566505689820195)
                  ·
                    rfl

theorem cell20_149989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_149989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_149989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_149989 prefixEnd_149989 := by exact prefixLift 149989
  have htrace : WordTrace (prefixWord ++ tailWord_149989) baseStart_149989 baseEnd_149989 := by
    simpa [prefixWord, tailWord_149989, baseEnd_149989] using wordTrace_append hprefix tailTrace_149989
  have hstable : (prefixWord ++ tailWord_149989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149989).length < 2 ^ (prefixWord ++ tailWord_149989).sum := by decide
  have hdescent : baseEnd_149989 < baseStart_149989 := by decide
  rcases family_descends (prefixWord ++ tailWord_149989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150021 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_150021 : Nat := 118140960795 + 150021 * 2 ^ 59
def prefixEnd_150021 : Nat := 4983230072969 + 3 ^ 40 * 150021 * 2
def baseEnd_150021 : Nat := 68473672238455800753397

theorem tailTrace_150021 : CollatzResearch.WordTrace tailWord_150021 prefixEnd_150021 68473672238455800753397 := by
  unfold tailWord_150021
  simp only [CollatzResearch.WordTrace]
  refine ⟨5471715389507013392073917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3647810259671342261382611 5471715389507013392073917)
  ·
    refine ⟨2051893271065130022027719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5471715389507013392073917 2051893271065130022027719)
    ·
      refine ⟨3077839906597695033041579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051893271065130022027719 3077839906597695033041579)
      ·
        refine ⟨4616759859896542549562369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077839906597695033041579 4616759859896542549562369)
        ·
          refine ⟨3462569894922406912171777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4616759859896542549562369 3462569894922406912171777)
          ·
            refine ⟨2596927421191805184128833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3462569894922406912171777 2596927421191805184128833)
            ·
              refine ⟨1947695565893853888096625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596927421191805184128833 1947695565893853888096625)
              ·
                refine ⟨1460771674420390416072469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947695565893853888096625 1460771674420390416072469)
                ·
                  refine ⟨68473672238455800753397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1460771674420390416072469 68473672238455800753397)
                  ·
                    rfl

theorem cell20_150021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_150021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150021 prefixEnd_150021 := by exact prefixLift 150021
  have htrace : WordTrace (prefixWord ++ tailWord_150021) baseStart_150021 baseEnd_150021 := by
    simpa [prefixWord, tailWord_150021, baseEnd_150021] using wordTrace_append hprefix tailTrace_150021
  have hstable : (prefixWord ++ tailWord_150021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150021).length < 2 ^ (prefixWord ++ tailWord_150021).sum := by decide
  have hdescent : baseEnd_150021 < baseStart_150021 := by decide
  rcases family_descends (prefixWord ++ tailWord_150021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150045 : List Nat := [1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_150045 : Nat := 118140960795 + 150045 * 2 ^ 59
def prefixEnd_150045 : Nat := 4983230072969 + 3 ^ 40 * 150045 * 2
def baseEnd_150045 : Nat := 22828208830806127984433

theorem tailTrace_150045 : CollatzResearch.WordTrace tailWord_150045 prefixEnd_150045 22828208830806127984433 := by
  unfold tailWord_150045
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472590741420065490947589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3648393827613376993965059 5472590741420065490947589)
  ·
    refine ⟨1026110764016262279552673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5472590741420065490947589 1026110764016262279552673)
    ·
      refine ⟨769583073012196709664505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1026110764016262279552673 769583073012196709664505)
      ·
        refine ⟨577187304759147532248379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769583073012196709664505 577187304759147532248379)
        ·
          refine ⟨865780957138721298372569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577187304759147532248379 865780957138721298372569)
          ·
            refine ⟨649335717854040973779427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865780957138721298372569 649335717854040973779427)
            ·
              refine ⟨974003576781061460669141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649335717854040973779427 974003576781061460669141)
              ·
                refine ⟨22828208830806127984433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 974003576781061460669141 22828208830806127984433)
                ·
                  rfl

theorem cell20_150045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_150045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150045 prefixEnd_150045 := by exact prefixLift 150045
  have htrace : WordTrace (prefixWord ++ tailWord_150045) baseStart_150045 baseEnd_150045 := by
    simpa [prefixWord, tailWord_150045, baseEnd_150045] using wordTrace_append hprefix tailTrace_150045
  have hstable : (prefixWord ++ tailWord_150045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150045).length < 2 ^ (prefixWord ++ tailWord_150045).sum := by decide
  have hdescent : baseEnd_150045 < baseStart_150045 := by decide
  rcases family_descends (prefixWord ++ tailWord_150045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150048 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_150048 : Nat := 118140960795 + 150048 * 2 ^ 59
def prefixEnd_150048 : Nat := 4983230072969 + 3 ^ 40 * 150048 * 2
def baseEnd_150048 : Nat := 68485995774163706853287

theorem tailTrace_150048 : CollatzResearch.WordTrace tailWord_150048 prefixEnd_150048 68485995774163706853287 := by
  unfold tailWord_150048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736350080204598501653399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3648466773606131335537865 2736350080204598501653399)
  ·
    refine ⟨4104525120306897752480099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2736350080204598501653399 4104525120306897752480099)
    ·
      refine ⟨6156787680460346628720149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104525120306897752480099 6156787680460346628720149)
      ·
        refine ⟨288599422521578748221257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6156787680460346628720149 288599422521578748221257)
        ·
          refine ⟨216449566891184061165943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288599422521578748221257 216449566891184061165943)
          ·
            refine ⟨324674350336776091748915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216449566891184061165943 324674350336776091748915)
            ·
              refine ⟨487011525505164137623373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324674350336776091748915 487011525505164137623373)
              ·
                refine ⟨182629322064436551608765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487011525505164137623373 182629322064436551608765)
                ·
                  refine ⟨68485995774163706853287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182629322064436551608765 68485995774163706853287)
                  ·
                    rfl

theorem cell20_150048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_150048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150048 prefixEnd_150048 := by exact prefixLift 150048
  have htrace : WordTrace (prefixWord ++ tailWord_150048) baseStart_150048 baseEnd_150048 := by
    simpa [prefixWord, tailWord_150048, baseEnd_150048] using wordTrace_append hprefix tailTrace_150048
  have hstable : (prefixWord ++ tailWord_150048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150048).length < 2 ^ (prefixWord ++ tailWord_150048).sum := by decide
  have hdescent : baseEnd_150048 < baseStart_150048 := by decide
  rcases family_descends (prefixWord ++ tailWord_150048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150059 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_150059 : Nat := 118140960795 + 150059 * 2 ^ 59
def prefixEnd_150059 : Nat := 4983230072969 + 3 ^ 40 * 150059 * 2
def baseEnd_150059 : Nat := 68491016473896557486575

theorem tailTrace_150059 : CollatzResearch.WordTrace tailWord_150059 prefixEnd_150059 68491016473896557486575 := by
  unfold tailWord_150059
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473101363369345881957231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3648734242246230587971487 5473101363369345881957231)
  ·
    refine ⟨8209652045054018822935847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5473101363369345881957231 8209652045054018822935847)
    ·
      refine ⟨12314478067581028234403771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8209652045054018822935847 12314478067581028234403771)
      ·
        refine ⟨18471717101371542351605657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12314478067581028234403771 18471717101371542351605657)
        ·
          refine ⟨13853787826028656763704243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18471717101371542351605657 13853787826028656763704243)
          ·
            refine ⟨20780681739042985145556365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13853787826028656763704243 20780681739042985145556365)
            ·
              refine ⟨7792755652141119429583637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20780681739042985145556365 7792755652141119429583637)
              ·
                refine ⟨365285421194114973261733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7792755652141119429583637 365285421194114973261733)
                ·
                  refine ⟨68491016473896557486575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365285421194114973261733 68491016473896557486575)
                  ·
                    rfl

theorem cell20_150059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_150059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150059 prefixEnd_150059 := by exact prefixLift 150059
  have htrace : WordTrace (prefixWord ++ tailWord_150059) baseStart_150059 baseEnd_150059 := by
    simpa [prefixWord, tailWord_150059, baseEnd_150059] using wordTrace_append hprefix tailTrace_150059
  have hstable : (prefixWord ++ tailWord_150059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150059).length < 2 ^ (prefixWord ++ tailWord_150059).sum := by decide
  have hdescent : baseEnd_150059 < baseStart_150059 := by decide
  rcases family_descends (prefixWord ++ tailWord_150059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150100 : List Nat := [2, 4, 1, 1, 1, 5, 1, 5]
def baseStart_150100 : Nat := 118140960795 + 150100 * 2 ^ 59
def prefixEnd_150100 : Nat := 4983230072969 + 3 ^ 40 * 150100 * 2
def baseEnd_150100 : Nat := 22836576663694212373247

theorem tailTrace_150100 : CollatzResearch.WordTrace tailWord_150100 prefixEnd_150100 22836576663694212373247 := by
  unfold tailWord_150100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2737298378110404942099877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3649731170813873256133169 2737298378110404942099877)
  ·
    refine ⟨513243445895700926643727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2737298378110404942099877 513243445895700926643727)
    ·
      refine ⟨769865168843551389965591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513243445895700926643727 769865168843551389965591)
      ·
        refine ⟨1154797753265327084948387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769865168843551389965591 1154797753265327084948387)
        ·
          refine ⟨1732196629897990627422581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154797753265327084948387 1732196629897990627422581)
          ·
            refine ⟨162393434052936621320867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1732196629897990627422581 162393434052936621320867)
            ·
              refine ⟨243590151079404931981301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162393434052936621320867 243590151079404931981301)
              ·
                refine ⟨22836576663694212373247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 243590151079404931981301 22836576663694212373247)
                ·
                  rfl

theorem cell20_150100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_150100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150100 prefixEnd_150100 := by exact prefixLift 150100
  have htrace : WordTrace (prefixWord ++ tailWord_150100) baseStart_150100 baseEnd_150100 := by
    simpa [prefixWord, tailWord_150100, baseEnd_150100] using wordTrace_append hprefix tailTrace_150100
  have hstable : (prefixWord ++ tailWord_150100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150100).length < 2 ^ (prefixWord ++ tailWord_150100).sum := by decide
  have hdescent : baseEnd_150100 < baseStart_150100 := by decide
  rcases family_descends (prefixWord ++ tailWord_150100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150141 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 3]
def baseStart_150141 : Nat := 118140960795 + 150141 * 2 ^ 59
def prefixEnd_150141 : Nat := 4983230072969 + 3 ^ 40 * 150141 * 2
def baseEnd_150141 : Nat := 68528443508268716752907

theorem tailTrace_150141 : CollatzResearch.WordTrace tailWord_150141 prefixEnd_150141 68528443508268716752907 := by
  unfold tailWord_150141
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476092149072273886442277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3650728099381515924294851 5476092149072273886442277)
  ·
    refine ⟨1026767277951051353707927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5476092149072273886442277 1026767277951051353707927)
    ·
      refine ⟨1540150916926577030561891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026767277951051353707927 1540150916926577030561891)
      ·
        refine ⟨2310226375389865545842837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540150916926577030561891 2310226375389865545842837)
        ·
          refine ⟨108291861346399947461383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2310226375389865545842837 108291861346399947461383)
          ·
            refine ⟨162437792019599921192075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108291861346399947461383 162437792019599921192075)
            ·
              refine ⟨243656688029399881788113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162437792019599921192075 243656688029399881788113)
              ·
                refine ⟨182742516022049911341085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243656688029399881788113 182742516022049911341085)
                ·
                  refine ⟨68528443508268716752907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182742516022049911341085 68528443508268716752907)
                  ·
                    rfl

theorem cell20_150141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_150141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150141 prefixEnd_150141 := by exact prefixLift 150141
  have htrace : WordTrace (prefixWord ++ tailWord_150141) baseStart_150141 baseEnd_150141 := by
    simpa [prefixWord, tailWord_150141, baseEnd_150141] using wordTrace_append hprefix tailTrace_150141
  have hstable : (prefixWord ++ tailWord_150141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150141).length < 2 ^ (prefixWord ++ tailWord_150141).sum := by decide
  have hdescent : baseEnd_150141 < baseStart_150141 := by decide
  rcases family_descends (prefixWord ++ tailWord_150141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150193 : List Nat := [1, 2, 2, 6, 2, 1, 6]
def baseStart_150193 : Nat := 118140960795 + 150193 * 2 ^ 59
def prefixEnd_150193 : Nat := 4983230072969 + 3 ^ 40 * 150193 * 2
def baseEnd_150193 : Nat := 7616908636131960779929

theorem tailTrace_150193 : CollatzResearch.WordTrace tailWord_150193 prefixEnd_150193 7616908636131960779929 := by
  unfold tailWord_150193
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477988744883886767335233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3651992496589257844890155 5477988744883886767335233)
  ·
    refine ⟨4108491558662915075501425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5477988744883886767335233 4108491558662915075501425)
    ·
      refine ⟨3081368668997186306626069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4108491558662915075501425 3081368668997186306626069)
      ·
        refine ⟨144439156359243108123097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3081368668997186306626069 144439156359243108123097)
        ·
          refine ⟨108329367269432331092323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144439156359243108123097 108329367269432331092323)
          ·
            refine ⟨162494050904148496638485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108329367269432331092323 162494050904148496638485)
            ·
              refine ⟨7616908636131960779929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162494050904148496638485 7616908636131960779929)
              ·
                rfl

theorem cell20_150193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 6].length) (baseStart_150193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150193 prefixEnd_150193 := by exact prefixLift 150193
  have htrace : WordTrace (prefixWord ++ tailWord_150193) baseStart_150193 baseEnd_150193 := by
    simpa [prefixWord, tailWord_150193, baseEnd_150193] using wordTrace_append hprefix tailTrace_150193
  have hstable : (prefixWord ++ tailWord_150193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150193).length < 2 ^ (prefixWord ++ tailWord_150193).sum := by decide
  have hdescent : baseEnd_150193 < baseStart_150193 := by decide
  rcases family_descends (prefixWord ++ tailWord_150193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150197 : List Nat := [1, 3, 3, 3, 1, 1, 8]
def baseStart_150197 : Nat := 118140960795 + 150197 * 2 ^ 59
def prefixEnd_150197 : Nat := 4983230072969 + 3 ^ 40 * 150197 * 2
def baseEnd_150197 : Nat := 7617111492686823431779

theorem tailTrace_150197 : CollatzResearch.WordTrace tailWord_150197 prefixEnd_150197 7617111492686823431779 := by
  unfold tailWord_150197
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478134636869395450480845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3652089757912930300320563 5478134636869395450480845)
  ·
    refine ⟨2054300488826023293930317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5478134636869395450480845 2054300488826023293930317)
    ·
      refine ⟨770362683309758735223869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2054300488826023293930317 770362683309758735223869)
      ·
        refine ⟨288886006241159525708951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 770362683309758735223869 288886006241159525708951)
        ·
          refine ⟨433329009361739288563427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288886006241159525708951 433329009361739288563427)
          ·
            refine ⟨649993514042608932845141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433329009361739288563427 649993514042608932845141)
            ·
              refine ⟨7617111492686823431779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 649993514042608932845141 7617111492686823431779)
              ·
                rfl

theorem cell20_150197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_150197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150197 prefixEnd_150197 := by exact prefixLift 150197
  have htrace : WordTrace (prefixWord ++ tailWord_150197) baseStart_150197 baseEnd_150197 := by
    simpa [prefixWord, tailWord_150197, baseEnd_150197] using wordTrace_append hprefix tailTrace_150197
  have hstable : (prefixWord ++ tailWord_150197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150197).length < 2 ^ (prefixWord ++ tailWord_150197).sum := by decide
  have hdescent : baseEnd_150197 < baseStart_150197 := by decide
  rcases family_descends (prefixWord ++ tailWord_150197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150204 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_150204 : Nat := 118140960795 + 150204 * 2 ^ 59
def prefixEnd_150204 : Nat := 4983230072969 + 3 ^ 40 * 150204 * 2
def baseEnd_150204 : Nat := 68557198424920497652649

theorem tailTrace_150204 : CollatzResearch.WordTrace tailWord_150204 prefixEnd_150204 68557198424920497652649 := by
  unfold tailWord_150204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739194973922017822992833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3652259965229357097323777 2739194973922017822992833)
  ·
    refine ⟨2054396230441513367244625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2739194973922017822992833 2054396230441513367244625)
    ·
      refine ⟨1540797172831135025433469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2054396230441513367244625 1540797172831135025433469)
      ·
        refine ⟨577798939811675634537551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1540797172831135025433469 577798939811675634537551)
        ·
          refine ⟨866698409717513451806327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577798939811675634537551 866698409717513451806327)
          ·
            refine ⟨1300047614576270177709491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866698409717513451806327 1300047614576270177709491)
            ·
              refine ⟨1950071421864405266564237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300047614576270177709491 1950071421864405266564237)
              ·
                refine ⟨731276783199151974961589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1950071421864405266564237 731276783199151974961589)
                ·
                  refine ⟨68557198424920497652649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 731276783199151974961589 68557198424920497652649)
                  ·
                    rfl

theorem cell20_150204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_150204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150204 prefixEnd_150204 := by exact prefixLift 150204
  have htrace : WordTrace (prefixWord ++ tailWord_150204) baseStart_150204 baseEnd_150204 := by
    simpa [prefixWord, tailWord_150204, baseEnd_150204] using wordTrace_append hprefix tailTrace_150204
  have hstable : (prefixWord ++ tailWord_150204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150204).length < 2 ^ (prefixWord ++ tailWord_150204).sum := by decide
  have hdescent : baseEnd_150204 < baseStart_150204 := by decide
  rcases family_descends (prefixWord ++ tailWord_150204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150287 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_150287 : Nat := 118140960795 + 150287 * 2 ^ 59
def prefixEnd_150287 : Nat := 4983230072969 + 3 ^ 40 * 150287 * 2
def baseEnd_150287 : Nat := 68595081886541097885643

theorem tailTrace_150287 : CollatzResearch.WordTrace tailWord_150287 prefixEnd_150287 68595081886541097885643 := by
  unfold tailWord_150287
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481417206543340821257115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3654278137695560547504743 5481417206543340821257115)
  ·
    refine ⟨8222125809815011231885673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5481417206543340821257115 8222125809815011231885673)
    ·
      refine ⟨6166594357361258423914255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8222125809815011231885673 6166594357361258423914255)
      ·
        refine ⟨9249891536041887635871383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166594357361258423914255 9249891536041887635871383)
        ·
          refine ⟨13874837304062831453807075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9249891536041887635871383 13874837304062831453807075)
          ·
            refine ⟨20812255956094247180710613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13874837304062831453807075 20812255956094247180710613)
            ·
              refine ⟨487787248970958918297905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20812255956094247180710613 487787248970958918297905)
              ·
                refine ⟨365840436728219188723429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487787248970958918297905 365840436728219188723429)
                ·
                  refine ⟨68595081886541097885643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365840436728219188723429 68595081886541097885643)
                  ·
                    rfl

theorem cell20_150287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_150287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150287 prefixEnd_150287 := by exact prefixLift 150287
  have htrace : WordTrace (prefixWord ++ tailWord_150287) baseStart_150287 baseEnd_150287 := by
    simpa [prefixWord, tailWord_150287, baseEnd_150287] using wordTrace_append hprefix tailTrace_150287
  have hstable : (prefixWord ++ tailWord_150287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150287).length < 2 ^ (prefixWord ++ tailWord_150287).sum := by decide
  have hdescent : baseEnd_150287 < baseStart_150287 := by decide
  rcases family_descends (prefixWord ++ tailWord_150287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150314 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_150314 : Nat := 118140960795 + 150314 * 2 ^ 59
def prefixEnd_150314 : Nat := 4983230072969 + 3 ^ 40 * 150314 * 2
def baseEnd_150314 : Nat := 68607405422249003985533

theorem tailTrace_150314 : CollatzResearch.WordTrace tailWord_150314 prefixEnd_150314 68607405422249003985533 := by
  unfold tailWord_150314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370600494361381108122499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3654934651630349621659997 1370600494361381108122499)
  ·
    refine ⟨2055900741542071662183749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370600494361381108122499 2055900741542071662183749)
    ·
      refine ⟨385481389039138436659453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2055900741542071662183749 385481389039138436659453)
      ·
        refine ⟨144555520889676913747295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385481389039138436659453 144555520889676913747295)
        ·
          refine ⟨216833281334515370620943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144555520889676913747295 216833281334515370620943)
          ·
            refine ⟨325249922001773055931415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216833281334515370620943 325249922001773055931415)
            ·
              refine ⟨487874883002659583897123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325249922001773055931415 487874883002659583897123)
              ·
                refine ⟨731812324503989375845685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487874883002659583897123 731812324503989375845685)
                ·
                  refine ⟨68607405422249003985533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 731812324503989375845685 68607405422249003985533)
                  ·
                    rfl

theorem cell20_150314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_150314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150314 prefixEnd_150314 := by exact prefixLift 150314
  have htrace : WordTrace (prefixWord ++ tailWord_150314) baseStart_150314 baseEnd_150314 := by
    simpa [prefixWord, tailWord_150314, baseEnd_150314] using wordTrace_append hprefix tailTrace_150314
  have hstable : (prefixWord ++ tailWord_150314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150314).length < 2 ^ (prefixWord ++ tailWord_150314).sum := by decide
  have hdescent : baseEnd_150314 < baseStart_150314 := by decide
  rcases family_descends (prefixWord ++ tailWord_150314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150332 : List Nat := [2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_150332 : Nat := 118140960795 + 150332 * 2 ^ 59
def prefixEnd_150332 : Nat := 4983230072969 + 3 ^ 40 * 150332 * 2
def baseEnd_150332 : Nat := 22871873704240313795153

theorem tailTrace_150332 : CollatzResearch.WordTrace tailWord_150332 prefixEnd_150332 22871873704240313795153 := by
  unfold tailWord_150332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741529245690156753322625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3655372327586875671096833 2741529245690156753322625)
  ·
    refine ⟨2056146934267617564991969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2741529245690156753322625 2056146934267617564991969)
    ·
      refine ⟨1542110200700713173743977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2056146934267617564991969 1542110200700713173743977)
      ·
        refine ⟨1156582650525534880307983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1542110200700713173743977 1156582650525534880307983)
        ·
          refine ⟨1734873975788302320461975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156582650525534880307983 1734873975788302320461975)
          ·
            refine ⟨2602310963682453480692963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734873975788302320461975 2602310963682453480692963)
            ·
              refine ⟨3903466445523680221039445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602310963682453480692963 3903466445523680221039445)
              ·
                refine ⟨22871873704240313795153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3903466445523680221039445 22871873704240313795153)
                ·
                  rfl

theorem cell20_150332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_150332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150332 prefixEnd_150332 := by exact prefixLift 150332
  have htrace : WordTrace (prefixWord ++ tailWord_150332) baseStart_150332 baseEnd_150332 := by
    simpa [prefixWord, tailWord_150332, baseEnd_150332] using wordTrace_append hprefix tailTrace_150332
  have hstable : (prefixWord ++ tailWord_150332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150332).length < 2 ^ (prefixWord ++ tailWord_150332).sum := by decide
  have hdescent : baseEnd_150332 < baseStart_150332 := by decide
  rcases family_descends (prefixWord ++ tailWord_150332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150359 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 2]
def baseStart_150359 : Nat := 118140960795 + 150359 * 2 ^ 59
def prefixEnd_150359 : Nat := 4983230072969 + 3 ^ 40 * 150359 * 2
def baseEnd_150359 : Nat := 68627944648428847485349

theorem tailTrace_150359 : CollatzResearch.WordTrace tailWord_150359 prefixEnd_150359 68627944648428847485349 := by
  unfold tailWord_150359
  simp only [CollatzResearch.WordTrace]
  refine ⟨5484043262282497117878131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3656028841521664745252087 5484043262282497117878131)
  ·
    refine ⟨8226064893423745676817197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5484043262282497117878131 8226064893423745676817197)
    ·
      refine ⟨3084774335033904628806449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8226064893423745676817197 3084774335033904628806449)
      ·
        refine ⟨2313580751275428471604837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3084774335033904628806449 2313580751275428471604837)
        ·
          refine ⟨433796390864142838425907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2313580751275428471604837 433796390864142838425907)
          ·
            refine ⟨650694586296214257638861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433796390864142838425907 650694586296214257638861)
            ·
              refine ⟨244010469861080346614573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 650694586296214257638861 244010469861080346614573)
              ·
                refine ⟨91503926197905129980465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244010469861080346614573 91503926197905129980465)
                ·
                  refine ⟨68627944648428847485349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91503926197905129980465 68627944648428847485349)
                  ·
                    rfl

theorem cell20_150359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 2].length) (baseStart_150359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150359 prefixEnd_150359 := by exact prefixLift 150359
  have htrace : WordTrace (prefixWord ++ tailWord_150359) baseStart_150359 baseEnd_150359 := by
    simpa [prefixWord, tailWord_150359, baseEnd_150359] using wordTrace_append hprefix tailTrace_150359
  have hstable : (prefixWord ++ tailWord_150359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150359).length < 2 ^ (prefixWord ++ tailWord_150359).sum := by decide
  have hdescent : baseEnd_150359 < baseStart_150359 := by decide
  rcases family_descends (prefixWord ++ tailWord_150359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150376 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 2]
def baseStart_150376 : Nat := 118140960795 + 150376 * 2 ^ 59
def prefixEnd_150376 : Nat := 4983230072969 + 3 ^ 40 * 150376 * 2
def baseEnd_150376 : Nat := 68635703911652343918613

theorem tailTrace_150376 : CollatzResearch.WordTrace tailWord_150376 prefixEnd_150376 68635703911652343918613 := by
  unfold tailWord_150376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742331651610454510623491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3656442202147272680831321 2742331651610454510623491)
  ·
    refine ⟨4113497477415681765935237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2742331651610454510623491 4113497477415681765935237)
    ·
      refine ⟨771280777015440331112857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4113497477415681765935237 771280777015440331112857)
      ·
        refine ⟨578460582761580248334643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771280777015440331112857 578460582761580248334643)
        ·
          refine ⟨867690874142370372501965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578460582761580248334643 867690874142370372501965)
          ·
            refine ⟨325384077803388889688237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 867690874142370372501965 325384077803388889688237)
            ·
              refine ⟨122019029176270833633089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325384077803388889688237 122019029176270833633089)
              ·
                refine ⟨91514271882203125224817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122019029176270833633089 91514271882203125224817)
                ·
                  refine ⟨68635703911652343918613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91514271882203125224817 68635703911652343918613)
                  ·
                    rfl

theorem cell20_150376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_150376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150376 prefixEnd_150376 := by exact prefixLift 150376
  have htrace : WordTrace (prefixWord ++ tailWord_150376) baseStart_150376 baseEnd_150376 := by
    simpa [prefixWord, tailWord_150376, baseEnd_150376] using wordTrace_append hprefix tailTrace_150376
  have hstable : (prefixWord ++ tailWord_150376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150376).length < 2 ^ (prefixWord ++ tailWord_150376).sum := by decide
  have hdescent : baseEnd_150376 < baseStart_150376 := by decide
  rcases family_descends (prefixWord ++ tailWord_150376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150390 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_150390 : Nat := 118140960795 + 150390 * 2 ^ 59
def prefixEnd_150390 : Nat := 4983230072969 + 3 ^ 40 * 150390 * 2
def baseEnd_150390 : Nat := 68642093893130517451889

theorem tailTrace_150390 : CollatzResearch.WordTrace tailWord_150390 prefixEnd_150390 68642093893130517451889 := by
  unfold tailWord_150390
  simp only [CollatzResearch.WordTrace]
  refine ⟨342823370323136838266039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3656782616780126274837749 342823370323136838266039)
  ·
    refine ⟨514235055484705257399059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342823370323136838266039 514235055484705257399059)
    ·
      refine ⟨771352583227057886098589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514235055484705257399059 771352583227057886098589)
      ·
        refine ⟨289257218710146707286971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 771352583227057886098589 289257218710146707286971)
        ·
          refine ⟨433885828065220060930457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289257218710146707286971 433885828065220060930457)
          ·
            refine ⟨325414371048915045697843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433885828065220060930457 325414371048915045697843)
            ·
              refine ⟨488121556573372568546765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325414371048915045697843 488121556573372568546765)
              ·
                refine ⟨183045583715014713205037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488121556573372568546765 183045583715014713205037)
                ·
                  refine ⟨68642093893130517451889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183045583715014713205037 68642093893130517451889)
                  ·
                    rfl

theorem cell20_150390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_150390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150390 prefixEnd_150390 := by exact prefixLift 150390
  have htrace : WordTrace (prefixWord ++ tailWord_150390) baseStart_150390 baseEnd_150390 := by
    simpa [prefixWord, tailWord_150390, baseEnd_150390] using wordTrace_append hprefix tailTrace_150390
  have hstable : (prefixWord ++ tailWord_150390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150390).length < 2 ^ (prefixWord ++ tailWord_150390).sum := by decide
  have hdescent : baseEnd_150390 < baseStart_150390 := by decide
  rcases family_descends (prefixWord ++ tailWord_150390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150428 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_150428 : Nat := 118140960795 + 150428 * 2 ^ 59
def prefixEnd_150428 : Nat := 4983230072969 + 3 ^ 40 * 150428 * 2
def baseEnd_150428 : Nat := 68659438128571274185067

theorem tailTrace_150428 : CollatzResearch.WordTrace tailWord_150428 prefixEnd_150428 68659438128571274185067 := by
  unfold tailWord_150428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743279949516260951069969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3657706599355014601426625 2743279949516260951069969)
  ·
    refine ⟨2057459962137195713302477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2743279949516260951069969 2057459962137195713302477)
    ·
      refine ⟨771547485801448392488429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2057459962137195713302477 771547485801448392488429)
      ·
        refine ⟨289330307175543147183161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 771547485801448392488429 289330307175543147183161)
        ·
          refine ⟨216997730381657360387371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289330307175543147183161 216997730381657360387371)
          ·
            refine ⟨325496595572486040581057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216997730381657360387371 325496595572486040581057)
            ·
              refine ⟨244122446679364530435793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325496595572486040581057 244122446679364530435793)
              ·
                refine ⟨183091835009523397826845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244122446679364530435793 183091835009523397826845)
                ·
                  refine ⟨68659438128571274185067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183091835009523397826845 68659438128571274185067)
                  ·
                    rfl

theorem cell20_150428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_150428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150428 prefixEnd_150428 := by exact prefixLift 150428
  have htrace : WordTrace (prefixWord ++ tailWord_150428) baseStart_150428 baseEnd_150428 := by
    simpa [prefixWord, tailWord_150428, baseEnd_150428] using wordTrace_append hprefix tailTrace_150428
  have hstable : (prefixWord ++ tailWord_150428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150428).length < 2 ^ (prefixWord ++ tailWord_150428).sum := by decide
  have hdescent : baseEnd_150428 < baseStart_150428 := by decide
  rcases family_descends (prefixWord ++ tailWord_150428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150432 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_150432 : Nat := 118140960795 + 150432 * 2 ^ 59
def prefixEnd_150432 : Nat := 4983230072969 + 3 ^ 40 * 150432 * 2
def baseEnd_150432 : Nat := 68661263837565038051717

theorem tailTrace_150432 : CollatzResearch.WordTrace tailWord_150432 prefixEnd_150432 68661263837565038051717 := by
  unfold tailWord_150432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743352895509015292642775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3657803860678687056857033 2743352895509015292642775)
  ·
    refine ⟨4115029343263522938964163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2743352895509015292642775 4115029343263522938964163)
    ·
      refine ⟨6172544014895284408446245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115029343263522938964163 6172544014895284408446245)
      ·
        refine ⟨1157352002792865826583671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6172544014895284408446245 1157352002792865826583671)
        ·
          refine ⟨1736028004189298739875507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157352002792865826583671 1736028004189298739875507)
          ·
            refine ⟨2604042006283948109813261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736028004189298739875507 2604042006283948109813261)
            ·
              refine ⟨976515752356480541179973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2604042006283948109813261 976515752356480541179973)
              ·
                refine ⟨183096703566840101471245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 976515752356480541179973 183096703566840101471245)
                ·
                  refine ⟨68661263837565038051717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183096703566840101471245 68661263837565038051717)
                  ·
                    rfl

theorem cell20_150432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_150432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150432 prefixEnd_150432 := by exact prefixLift 150432
  have htrace : WordTrace (prefixWord ++ tailWord_150432) baseStart_150432 baseEnd_150432 := by
    simpa [prefixWord, tailWord_150432, baseEnd_150432] using wordTrace_append hprefix tailTrace_150432
  have hstable : (prefixWord ++ tailWord_150432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150432).length < 2 ^ (prefixWord ++ tailWord_150432).sum := by decide
  have hdescent : baseEnd_150432 < baseStart_150432 := by decide
  rcases family_descends (prefixWord ++ tailWord_150432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150435 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 2]
def baseStart_150435 : Nat := 118140960795 + 150435 * 2 ^ 59
def prefixEnd_150435 : Nat := 4983230072969 + 3 ^ 40 * 150435 * 2
def baseEnd_150435 : Nat := 68662633119310360951705

theorem tailTrace_150435 : CollatzResearch.WordTrace tailWord_150435 prefixEnd_150435 68662633119310360951705 := by
  unfold tailWord_150435
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486815210007162097644759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3657876806671441398429839 5486815210007162097644759)
  ·
    refine ⟨8230222815010743146467139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5486815210007162097644759 8230222815010743146467139)
    ·
      refine ⟨12345334222516114719700709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8230222815010743146467139 12345334222516114719700709)
      ·
        refine ⟨2314750166721771509943883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12345334222516114719700709 2314750166721771509943883)
        ·
          refine ⟨3472125250082657264915825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314750166721771509943883 3472125250082657264915825)
          ·
            refine ⟨2604093937561992948686869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3472125250082657264915825 2604093937561992948686869)
            ·
              refine ⟨122066903323218419469697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2604093937561992948686869 122066903323218419469697)
              ·
                refine ⟨91550177492413814602273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122066903323218419469697 91550177492413814602273)
                ·
                  refine ⟨68662633119310360951705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91550177492413814602273 68662633119310360951705)
                  ·
                    rfl

theorem cell20_150435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 2].length) (baseStart_150435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150435 prefixEnd_150435 := by exact prefixLift 150435
  have htrace : WordTrace (prefixWord ++ tailWord_150435) baseStart_150435 baseEnd_150435 := by
    simpa [prefixWord, tailWord_150435, baseEnd_150435] using wordTrace_append hprefix tailTrace_150435
  have hstable : (prefixWord ++ tailWord_150435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150435).length < 2 ^ (prefixWord ++ tailWord_150435).sum := by decide
  have hdescent : baseEnd_150435 < baseStart_150435 := by decide
  rcases family_descends (prefixWord ++ tailWord_150435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150514 : List Nat := [3, 2, 1, 5, 2, 1, 2, 4]
def baseStart_150514 : Nat := 118140960795 + 150514 * 2 ^ 59
def prefixEnd_150514 : Nat := 4983230072969 + 3 ^ 40 * 150514 * 2
def baseEnd_150514 : Nat := 22899563623979065772683

theorem tailTrace_150514 : CollatzResearch.WordTrace tailWord_150514 prefixEnd_150514 22899563623979065772683 := by
  unfold tailWord_150514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372424144180239647442649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3659797717813972393180397 1372424144180239647442649)
  ·
    refine ⟨1029318108135179735581987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1372424144180239647442649 1029318108135179735581987)
    ·
      refine ⟨1543977162202769603372981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029318108135179735581987 1543977162202769603372981)
      ·
        refine ⟨144747858956509650316217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1543977162202769603372981 144747858956509650316217)
        ·
          refine ⟨108560894217382237737163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144747858956509650316217 108560894217382237737163)
          ·
            refine ⟨162841341326073356605745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108560894217382237737163 162841341326073356605745)
            ·
              refine ⟨122131005994555017454309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162841341326073356605745 122131005994555017454309)
              ·
                refine ⟨22899563623979065772683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122131005994555017454309 22899563623979065772683)
                ·
                  rfl

theorem cell20_150514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_150514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150514 prefixEnd_150514 := by exact prefixLift 150514
  have htrace : WordTrace (prefixWord ++ tailWord_150514) baseStart_150514 baseEnd_150514 := by
    simpa [prefixWord, tailWord_150514, baseEnd_150514] using wordTrace_append hprefix tailTrace_150514
  have hstable : (prefixWord ++ tailWord_150514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150514).length < 2 ^ (prefixWord ++ tailWord_150514).sum := by decide
  have hdescent : baseEnd_150514 < baseStart_150514 := by decide
  rcases family_descends (prefixWord ++ tailWord_150514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150518 : List Nat := [5, 1, 1, 1, 3, 1, 4, 4]
def baseStart_150518 : Nat := 118140960795 + 150518 * 2 ^ 59
def prefixEnd_150518 : Nat := 4983230072969 + 3 ^ 40 * 150518 * 2
def baseEnd_150518 : Nat := 22900172193643653728233

theorem tailTrace_150518 : CollatzResearch.WordTrace tailWord_150518 prefixEnd_150518 22900172193643653728233 := by
  unfold tailWord_150518
  simp only [CollatzResearch.WordTrace]
  refine ⟨343115154294154204557263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3659894979137644848610805 343115154294154204557263)
  ·
    refine ⟨514672731441231306835895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 343115154294154204557263 514672731441231306835895)
    ·
      refine ⟨772009097161846960253843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514672731441231306835895 772009097161846960253843)
      ·
        refine ⟨1158013645742770440380765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772009097161846960253843 1158013645742770440380765)
        ·
          refine ⟨434255117153538915142787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1158013645742770440380765 434255117153538915142787)
          ·
            refine ⟨651382675730308372714181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434255117153538915142787 651382675730308372714181)
            ·
              refine ⟨122134251699432819883909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 651382675730308372714181 122134251699432819883909)
              ·
                refine ⟨22900172193643653728233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122134251699432819883909 22900172193643653728233)
                ·
                  rfl

theorem cell20_150518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_150518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150518 prefixEnd_150518 := by exact prefixLift 150518
  have htrace : WordTrace (prefixWord ++ tailWord_150518) baseStart_150518 baseEnd_150518 := by
    simpa [prefixWord, tailWord_150518, baseEnd_150518] using wordTrace_append hprefix tailTrace_150518
  have hstable : (prefixWord ++ tailWord_150518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150518).length < 2 ^ (prefixWord ++ tailWord_150518).sum := by decide
  have hdescent : baseEnd_150518 < baseStart_150518 := by decide
  rcases family_descends (prefixWord ++ tailWord_150518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150553 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_150553 : Nat := 118140960795 + 150553 * 2 ^ 59
def prefixEnd_150553 : Nat := 4983230072969 + 3 ^ 40 * 150553 * 2
def baseEnd_150553 : Nat := 68716491534626395017889

theorem tailTrace_150553 : CollatzResearch.WordTrace tailWord_150553 prefixEnd_150553 68716491534626395017889 := by
  unfold tailWord_150553
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491119023579668250440313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3660746015719778833626875 5491119023579668250440313)
  ·
    refine ⟨4118339267684751187830235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5491119023579668250440313 4118339267684751187830235)
    ·
      refine ⟨6177508901527126781745353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118339267684751187830235 6177508901527126781745353)
      ·
        refine ⟨4633131676145345086309015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177508901527126781745353 4633131676145345086309015)
        ·
          refine ⟨6949697514218017629463523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633131676145345086309015 6949697514218017629463523)
          ·
            refine ⟨10424546271327026444195285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949697514218017629463523 10424546271327026444195285)
            ·
              refine ⟨244325303234227182285827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10424546271327026444195285 244325303234227182285827)
              ·
                refine ⟨366487954851340773428741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244325303234227182285827 366487954851340773428741)
                ·
                  refine ⟨68716491534626395017889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366487954851340773428741 68716491534626395017889)
                  ·
                    rfl

theorem cell20_150553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_150553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150553 prefixEnd_150553 := by exact prefixLift 150553
  have htrace : WordTrace (prefixWord ++ tailWord_150553) baseStart_150553 baseEnd_150553 := by
    simpa [prefixWord, tailWord_150553, baseEnd_150553] using wordTrace_append hprefix tailTrace_150553
  have hstable : (prefixWord ++ tailWord_150553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150553).length < 2 ^ (prefixWord ++ tailWord_150553).sum := by decide
  have hdescent : baseEnd_150553 < baseStart_150553 := by decide
  rcases family_descends (prefixWord ++ tailWord_150553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150563 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 3]
def baseStart_150563 : Nat := 118140960795 + 150563 * 2 ^ 59
def prefixEnd_150563 : Nat := 4983230072969 + 3 ^ 40 * 150563 * 2
def baseEnd_150563 : Nat := 68721055807110804684515

theorem tailTrace_150563 : CollatzResearch.WordTrace tailWord_150563 prefixEnd_150563 68721055807110804684515 := by
  unfold tailWord_150563
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491483753543439958304343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3660989169028959972202895 5491483753543439958304343)
  ·
    refine ⟨8237225630315159937456515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5491483753543439958304343 8237225630315159937456515)
    ·
      refine ⟨12355838445472739906184773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8237225630315159937456515 12355838445472739906184773)
      ·
        refine ⟨2316719708526138732409645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12355838445472739906184773 2316719708526138732409645)
        ·
          refine ⟨868769890697302024653617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2316719708526138732409645 868769890697302024653617)
          ·
            refine ⟨651577418022976518490213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 868769890697302024653617 651577418022976518490213)
            ·
              refine ⟨122170765879308097216915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 651577418022976518490213 122170765879308097216915)
              ·
                refine ⟨183256148818962145825373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122170765879308097216915 183256148818962145825373)
                ·
                  refine ⟨68721055807110804684515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183256148818962145825373 68721055807110804684515)
                  ·
                    rfl

theorem cell20_150563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_150563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150563 prefixEnd_150563 := by exact prefixLift 150563
  have htrace : WordTrace (prefixWord ++ tailWord_150563) baseStart_150563 baseEnd_150563 := by
    simpa [prefixWord, tailWord_150563, baseEnd_150563] using wordTrace_append hprefix tailTrace_150563
  have hstable : (prefixWord ++ tailWord_150563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150563).length < 2 ^ (prefixWord ++ tailWord_150563).sum := by decide
  have hdescent : baseEnd_150563 < baseStart_150563 := by decide
  rcases family_descends (prefixWord ++ tailWord_150563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150629 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_150629 : Nat := 118140960795 + 150629 * 2 ^ 59
def prefixEnd_150629 : Nat := 4983230072969 + 3 ^ 40 * 150629 * 2
def baseEnd_150629 : Nat := 68751180005507908484245

theorem tailTrace_150629 : CollatzResearch.WordTrace tailWord_150629 prefixEnd_150629 68751180005507908484245 := by
  unfold tailWord_150629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493890971304333230206941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3662593980869555486804627 5493890971304333230206941)
  ·
    refine ⟨2060209114239124961327603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5493890971304333230206941 2060209114239124961327603)
    ·
      refine ⟨3090313671358687441991405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060209114239124961327603 3090313671358687441991405)
      ·
        refine ⟨1158867626759507790746777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3090313671358687441991405 1158867626759507790746777)
        ·
          refine ⟨869150720069630843060083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1158867626759507790746777 869150720069630843060083)
          ·
            refine ⟨1303726080104446264590125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869150720069630843060083 1303726080104446264590125)
            ·
              refine ⟨488897280039167349221297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303726080104446264590125 488897280039167349221297)
              ·
                refine ⟨366672960029375511915973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488897280039167349221297 366672960029375511915973)
                ·
                  refine ⟨68751180005507908484245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366672960029375511915973 68751180005507908484245)
                  ·
                    rfl

theorem cell20_150629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_150629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150629 prefixEnd_150629 := by exact prefixLift 150629
  have htrace : WordTrace (prefixWord ++ tailWord_150629) baseStart_150629 baseEnd_150629 := by
    simpa [prefixWord, tailWord_150629, baseEnd_150629] using wordTrace_append hprefix tailTrace_150629
  have hstable : (prefixWord ++ tailWord_150629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150629).length < 2 ^ (prefixWord ++ tailWord_150629).sum := by decide
  have hdescent : baseEnd_150629 < baseStart_150629 := by decide
  rcases family_descends (prefixWord ++ tailWord_150629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150660 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_150660 : Nat := 118140960795 + 150660 * 2 ^ 59
def prefixEnd_150660 : Nat := 4983230072969 + 3 ^ 40 * 150660 * 2
def baseEnd_150660 : Nat := 68765329250209578450785

theorem tailTrace_150660 : CollatzResearch.WordTrace tailWord_150660 prefixEnd_150660 68765329250209578450785 := by
  unfold tailWord_150660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747510817096012762292717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3663347756128017016390289 2747510817096012762292717)
  ·
    refine ⟨1030316556411004785859769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2747510817096012762292717 1030316556411004785859769)
    ·
      refine ⟨772737417308253589394827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1030316556411004785859769 772737417308253589394827)
      ·
        refine ⟨1159106125962380384092241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772737417308253589394827 1159106125962380384092241)
        ·
          refine ⟨869329594471785288069181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159106125962380384092241 869329594471785288069181)
          ·
            refine ⟨325998597926919483025943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 869329594471785288069181 325998597926919483025943)
            ·
              refine ⟨488997896890379224538915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325998597926919483025943 488997896890379224538915)
              ·
                refine ⟨733496845335568836808373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488997896890379224538915 733496845335568836808373)
                ·
                  refine ⟨68765329250209578450785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 733496845335568836808373 68765329250209578450785)
                  ·
                    rfl

theorem cell20_150660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_150660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150660 prefixEnd_150660 := by exact prefixLift 150660
  have htrace : WordTrace (prefixWord ++ tailWord_150660) baseStart_150660 baseEnd_150660 := by
    simpa [prefixWord, tailWord_150660, baseEnd_150660] using wordTrace_append hprefix tailTrace_150660
  have hstable : (prefixWord ++ tailWord_150660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150660).length < 2 ^ (prefixWord ++ tailWord_150660).sum := by decide
  have hdescent : baseEnd_150660 < baseStart_150660 := by decide
  rcases family_descends (prefixWord ++ tailWord_150660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150687 : List Nat := [1, 1, 2, 6, 3, 1, 2, 4]
def baseStart_150687 : Nat := 118140960795 + 150687 * 2 ^ 59
def prefixEnd_150687 : Nat := 4983230072969 + 3 ^ 40 * 150687 * 2
def baseEnd_150687 : Nat := 22925884261972494850225

theorem tailTrace_150687 : CollatzResearch.WordTrace tailWord_150687 prefixEnd_150687 22925884261972494850225 := by
  unfold tailWord_150687
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496006405094209135818315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3664004270062806090545543 5496006405094209135818315)
  ·
    refine ⟨8244009607641313703727473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496006405094209135818315 8244009607641313703727473)
    ·
      refine ⟨6183007205730985277795605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8244009607641313703727473 6183007205730985277795605)
      ·
        refine ⟨289828462768639934896669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6183007205730985277795605 289828462768639934896669)
        ·
          refine ⟨108685673538239975586251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289828462768639934896669 108685673538239975586251)
          ·
            refine ⟨163028510307359963379377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108685673538239975586251 163028510307359963379377)
            ·
              refine ⟨122271382730519972534533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163028510307359963379377 122271382730519972534533)
              ·
                refine ⟨22925884261972494850225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122271382730519972534533 22925884261972494850225)
                ·
                  rfl

theorem cell20_150687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].length) (baseStart_150687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150687 prefixEnd_150687 := by exact prefixLift 150687
  have htrace : WordTrace (prefixWord ++ tailWord_150687) baseStart_150687 baseEnd_150687 := by
    simpa [prefixWord, tailWord_150687, baseEnd_150687] using wordTrace_append hprefix tailTrace_150687
  have hstable : (prefixWord ++ tailWord_150687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150687).length < 2 ^ (prefixWord ++ tailWord_150687).sum := by decide
  have hdescent : baseEnd_150687 < baseStart_150687 := by decide
  rcases family_descends (prefixWord ++ tailWord_150687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150718 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_150718 : Nat := 118140960795 + 150718 * 2 ^ 59
def prefixEnd_150718 : Nat := 4983230072969 + 3 ^ 40 * 150718 * 2
def baseEnd_150718 : Nat := 68791802030619154517215

theorem tailTrace_150718 : CollatzResearch.WordTrace tailWord_150718 prefixEnd_150718 68791802030619154517215 := by
  unfold tailWord_150718
  simp only [CollatzResearch.WordTrace]
  refine ⟨687142133497737678774601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3664758045321267620131205 687142133497737678774601)
  ·
    refine ⟨515356600123303259080951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 687142133497737678774601 515356600123303259080951)
    ·
      refine ⟨773034900184954888621427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515356600123303259080951 773034900184954888621427)
      ·
        refine ⟨1159552350277432332932141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773034900184954888621427 1159552350277432332932141)
        ·
          refine ⟨434832131354037124849553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1159552350277432332932141 434832131354037124849553)
          ·
            refine ⟨326124098515527843637165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434832131354037124849553 326124098515527843637165)
            ·
              refine ⟨122296536943322941363937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326124098515527843637165 122296536943322941363937)
              ·
                refine ⟨91722402707492206022953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122296536943322941363937 91722402707492206022953)
                ·
                  refine ⟨68791802030619154517215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91722402707492206022953 68791802030619154517215)
                  ·
                    rfl

theorem cell20_150718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_150718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150718 prefixEnd_150718 := by exact prefixLift 150718
  have htrace : WordTrace (prefixWord ++ tailWord_150718) baseStart_150718 baseEnd_150718 := by
    simpa [prefixWord, tailWord_150718, baseEnd_150718] using wordTrace_append hprefix tailTrace_150718
  have hstable : (prefixWord ++ tailWord_150718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150718).length < 2 ^ (prefixWord ++ tailWord_150718).sum := by decide
  have hdescent : baseEnd_150718 < baseStart_150718 := by decide
  rcases family_descends (prefixWord ++ tailWord_150718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150719 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_150719 : Nat := 118140960795 + 150719 * 2 ^ 59
def prefixEnd_150719 : Nat := 4983230072969 + 3 ^ 40 * 150719 * 2
def baseEnd_150719 : Nat := 68792258457867595483877

theorem tailTrace_150719 : CollatzResearch.WordTrace tailWord_150719 prefixEnd_150719 68792258457867595483877 := by
  unfold tailWord_150719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5497173540978278600983211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3664782360652185733988807 5497173540978278600983211)
  ·
    refine ⟨8245760311467417901474817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5497173540978278600983211 8245760311467417901474817)
    ·
      refine ⟨6184320233600563426106113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8245760311467417901474817 6184320233600563426106113)
      ·
        refine ⟨4638240175200422569579585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6184320233600563426106113 4638240175200422569579585)
        ·
          refine ⟨3478680131400316927184689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4638240175200422569579585 3478680131400316927184689)
          ·
            refine ⟨2609010098550237695388517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3478680131400316927184689 2609010098550237695388517)
            ·
              refine ⟨489189393478169567885347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2609010098550237695388517 489189393478169567885347)
              ·
                refine ⟨733784090217254351828021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489189393478169567885347 733784090217254351828021)
                ·
                  refine ⟨68792258457867595483877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 733784090217254351828021 68792258457867595483877)
                  ·
                    rfl

theorem cell20_150719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_150719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150719 prefixEnd_150719 := by exact prefixLift 150719
  have htrace : WordTrace (prefixWord ++ tailWord_150719) baseStart_150719 baseEnd_150719 := by
    simpa [prefixWord, tailWord_150719, baseEnd_150719] using wordTrace_append hprefix tailTrace_150719
  have hstable : (prefixWord ++ tailWord_150719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150719).length < 2 ^ (prefixWord ++ tailWord_150719).sum := by decide
  have hdescent : baseEnd_150719 < baseStart_150719 := by decide
  rcases family_descends (prefixWord ++ tailWord_150719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150760 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 2]
def baseStart_150760 : Nat := 118140960795 + 150760 * 2 ^ 59
def prefixEnd_150760 : Nat := 4983230072969 + 3 ^ 40 * 150760 * 2
def baseEnd_150760 : Nat := 68810971975053675117043

theorem tailTrace_150760 : CollatzResearch.WordTrace tailWord_150760 prefixEnd_150760 68810971975053675117043 := by
  unfold tailWord_150760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749334466914871301612867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3665779289219828402150489 2749334466914871301612867)
  ·
    refine ⟨4124001700372306952419301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2749334466914871301612867 4124001700372306952419301)
    ·
      refine ⟨773250318819807553578619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4124001700372306952419301 773250318819807553578619)
      ·
        refine ⟨1159875478229711330367929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773250318819807553578619 1159875478229711330367929)
        ·
          refine ⟨869906608672283497775947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159875478229711330367929 869906608672283497775947)
          ·
            refine ⟨1304859913008425246663921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869906608672283497775947 1304859913008425246663921)
            ·
              refine ⟨978644934756318934997941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304859913008425246663921 978644934756318934997941)
              ·
                refine ⟨91747962633404900156057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 978644934756318934997941 91747962633404900156057)
                ·
                  refine ⟨68810971975053675117043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91747962633404900156057 68810971975053675117043)
                  ·
                    rfl

theorem cell20_150760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_150760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150760 prefixEnd_150760 := by exact prefixLift 150760
  have htrace : WordTrace (prefixWord ++ tailWord_150760) baseStart_150760 baseEnd_150760 := by
    simpa [prefixWord, tailWord_150760, baseEnd_150760] using wordTrace_append hprefix tailTrace_150760
  have hstable : (prefixWord ++ tailWord_150760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150760).length < 2 ^ (prefixWord ++ tailWord_150760).sum := by decide
  have hdescent : baseEnd_150760 < baseStart_150760 := by decide
  rcases family_descends (prefixWord ++ tailWord_150760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150771 : List Nat := [1, 1, 1, 2, 2, 13]
def baseStart_150771 : Nat := 118140960795 + 150771 * 2 ^ 59
def prefixEnd_150771 : Nat := 4983230072969 + 3 ^ 40 * 150771 * 2
def baseEnd_150771 : Nat := 2548740469436537990753

theorem tailTrace_150771 : CollatzResearch.WordTrace tailWord_150771 prefixEnd_150771 2548740469436537990753 := by
  unfold tailWord_150771
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499070136789891481876167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3666046757859927654584111 5499070136789891481876167)
  ·
    refine ⟨8248605205184837222814251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5499070136789891481876167 8248605205184837222814251)
    ·
      refine ⟨12372907807777255834221377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248605205184837222814251 12372907807777255834221377)
      ·
        refine ⟨9279680855832941875666033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12372907807777255834221377 9279680855832941875666033)
        ·
          refine ⟨6959760641874706406749525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9279680855832941875666033 6959760641874706406749525)
          ·
            refine ⟨2548740469436537990753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 6959760641874706406749525 2548740469436537990753)
            ·
              rfl

theorem cell20_150771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 13].length) (baseStart_150771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150771 prefixEnd_150771 := by exact prefixLift 150771
  have htrace : WordTrace (prefixWord ++ tailWord_150771) baseStart_150771 baseEnd_150771 := by
    simpa [prefixWord, tailWord_150771, baseEnd_150771] using wordTrace_append hprefix tailTrace_150771
  have hstable : (prefixWord ++ tailWord_150771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150771).length < 2 ^ (prefixWord ++ tailWord_150771).sum := by decide
  have hdescent : baseEnd_150771 < baseStart_150771 := by decide
  rcases family_descends (prefixWord ++ tailWord_150771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150815 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 2]
def baseStart_150815 : Nat := 118140960795 + 150815 * 2 ^ 59
def prefixEnd_150815 : Nat := 4983230072969 + 3 ^ 40 * 150815 * 2
def baseEnd_150815 : Nat := 68836075473717928283485

theorem tailTrace_150815 : CollatzResearch.WordTrace tailWord_150815 prefixEnd_150815 68836075473717928283485 := by
  unfold tailWord_150815
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500674948630486996477899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3667116632420324664318599 5500674948630486996477899)
  ·
    refine ⟨8251012422945730494716849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5500674948630486996477899 8251012422945730494716849)
    ·
      refine ⟨6188259317209297871037637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8251012422945730494716849 6188259317209297871037637)
      ·
        refine ⟨1160298621976743350819557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6188259317209297871037637 1160298621976743350819557)
        ·
          refine ⟨217555991620639378278667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1160298621976743350819557 217555991620639378278667)
          ·
            refine ⟨326333987430959067418001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217555991620639378278667 326333987430959067418001)
            ·
              refine ⟨244750490573219300563501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326333987430959067418001 244750490573219300563501)
              ·
                refine ⟨91781433964957237711313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244750490573219300563501 91781433964957237711313)
                ·
                  refine ⟨68836075473717928283485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91781433964957237711313 68836075473717928283485)
                  ·
                    rfl

theorem cell20_150815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 2].length) (baseStart_150815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150815 prefixEnd_150815 := by exact prefixLift 150815
  have htrace : WordTrace (prefixWord ++ tailWord_150815) baseStart_150815 baseEnd_150815 := by
    simpa [prefixWord, tailWord_150815, baseEnd_150815] using wordTrace_append hprefix tailTrace_150815
  have hstable : (prefixWord ++ tailWord_150815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150815).length < 2 ^ (prefixWord ++ tailWord_150815).sum := by decide
  have hdescent : baseEnd_150815 < baseStart_150815 := by decide
  rcases family_descends (prefixWord ++ tailWord_150815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150829 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_150829 : Nat := 118140960795 + 150829 * 2 ^ 59
def prefixEnd_150829 : Nat := 4983230072969 + 3 ^ 40 * 150829 * 2
def baseEnd_150829 : Nat := 68842465455196101816761

theorem tailTrace_150829 : CollatzResearch.WordTrace tailWord_150829 prefixEnd_150829 68842465455196101816761 := by
  unfold tailWord_150829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501185570579767387487541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3667457047053178258325027 5501185570579767387487541)
  ·
    refine ⟨515736147241853192576957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5501185570579767387487541 515736147241853192576957)
    ·
      refine ⟨193401055215694947216359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 515736147241853192576957 193401055215694947216359)
      ·
        refine ⟨290101582823542420824539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193401055215694947216359 290101582823542420824539)
        ·
          refine ⟨435152374235313631236809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290101582823542420824539 435152374235313631236809)
          ·
            refine ⟨326364280676485223427607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435152374235313631236809 326364280676485223427607)
            ·
              refine ⟨489546421014727835141411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326364280676485223427607 489546421014727835141411)
              ·
                refine ⟨734319631522091752712117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489546421014727835141411 734319631522091752712117)
                ·
                  refine ⟨68842465455196101816761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734319631522091752712117 68842465455196101816761)
                  ·
                    rfl

theorem cell20_150829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_150829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150829 prefixEnd_150829 := by exact prefixLift 150829
  have htrace : WordTrace (prefixWord ++ tailWord_150829) baseStart_150829 baseEnd_150829 := by
    simpa [prefixWord, tailWord_150829, baseEnd_150829] using wordTrace_append hprefix tailTrace_150829
  have hstable : (prefixWord ++ tailWord_150829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150829).length < 2 ^ (prefixWord ++ tailWord_150829).sum := by decide
  have hdescent : baseEnd_150829 < baseStart_150829 := by decide
  rcases family_descends (prefixWord ++ tailWord_150829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150836 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_150836 : Nat := 118140960795 + 150836 * 2 ^ 59
def prefixEnd_150836 : Nat := 4983230072969 + 3 ^ 40 * 150836 * 2
def baseEnd_150836 : Nat := 68845660445935188583399

theorem tailTrace_150836 : CollatzResearch.WordTrace tailWord_150836 prefixEnd_150836 68845660445935188583399 := by
  unfold tailWord_150836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750720440777203791496181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3667627254369605055328241 2750720440777203791496181)
  ·
    refine ⟨257880041322862855452767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2750720440777203791496181 257880041322862855452767)
    ·
      refine ⟨386820061984294283179151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257880041322862855452767 386820061984294283179151)
      ·
        refine ⟨580230092976441424768727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386820061984294283179151 580230092976441424768727)
        ·
          refine ⟨870345139464662137153091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580230092976441424768727 870345139464662137153091)
          ·
            refine ⟨1305517709196993205729637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870345139464662137153091 1305517709196993205729637)
            ·
              refine ⟨244784570474436226074307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1305517709196993205729637 244784570474436226074307)
              ·
                refine ⟨367176855711654339111461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244784570474436226074307 367176855711654339111461)
                ·
                  refine ⟨68845660445935188583399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367176855711654339111461 68845660445935188583399)
                  ·
                    rfl

theorem cell20_150836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_150836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150836 prefixEnd_150836 := by exact prefixLift 150836
  have htrace : WordTrace (prefixWord ++ tailWord_150836) baseStart_150836 baseEnd_150836 := by
    simpa [prefixWord, tailWord_150836, baseEnd_150836] using wordTrace_append hprefix tailTrace_150836
  have hstable : (prefixWord ++ tailWord_150836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150836).length < 2 ^ (prefixWord ++ tailWord_150836).sum := by decide
  have hdescent : baseEnd_150836 < baseStart_150836 := by decide
  rcases family_descends (prefixWord ++ tailWord_150836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150871 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_150871 : Nat := 118140960795 + 150871 * 2 ^ 59
def prefixEnd_150871 : Nat := 4983230072969 + 3 ^ 40 * 150871 * 2
def baseEnd_150871 : Nat := 68861635399630622416589

theorem tailTrace_150871 : CollatzResearch.WordTrace tailWord_150871 prefixEnd_150871 68861635399630622416589 := by
  unfold tailWord_150871
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502717436427608560516467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3668478290951739040344311 5502717436427608560516467)
  ·
    refine ⟨8254076154641412840774701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5502717436427608560516467 8254076154641412840774701)
    ·
      refine ⟨3095278557990529815290513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8254076154641412840774701 3095278557990529815290513)
      ·
        refine ⟨2321458918492897361467885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3095278557990529815290513 2321458918492897361467885)
        ·
          refine ⟨870547094434836510550457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2321458918492897361467885 870547094434836510550457)
          ·
            refine ⟨652910320826127382912843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870547094434836510550457 652910320826127382912843)
            ·
              refine ⟨979365481239191074369265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652910320826127382912843 979365481239191074369265)
              ·
                refine ⟨734524110929393305776949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979365481239191074369265 734524110929393305776949)
                ·
                  refine ⟨68861635399630622416589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734524110929393305776949 68861635399630622416589)
                  ·
                    rfl

theorem cell20_150871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_150871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150871 prefixEnd_150871 := by exact prefixLift 150871
  have htrace : WordTrace (prefixWord ++ tailWord_150871) baseStart_150871 baseEnd_150871 := by
    simpa [prefixWord, tailWord_150871, baseEnd_150871] using wordTrace_append hprefix tailTrace_150871
  have hstable : (prefixWord ++ tailWord_150871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150871).length < 2 ^ (prefixWord ++ tailWord_150871).sum := by decide
  have hdescent : baseEnd_150871 < baseStart_150871 := by decide
  rcases family_descends (prefixWord ++ tailWord_150871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150874 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_150874 : Nat := 118140960795 + 150874 * 2 ^ 59
def prefixEnd_150874 : Nat := 4983230072969 + 3 ^ 40 * 150874 * 2
def baseEnd_150874 : Nat := 68863004681375945316577

theorem tailTrace_150874 : CollatzResearch.WordTrace tailWord_150874 prefixEnd_150874 68863004681375945316577 := by
  unfold tailWord_150874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375706713854185018218919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3668551236944493381917117 1375706713854185018218919)
  ·
    refine ⟨2063560070781277527328379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1375706713854185018218919 2063560070781277527328379)
    ·
      refine ⟨3095340106171916290992569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063560070781277527328379 3095340106171916290992569)
      ·
        refine ⟨2321505079628937218244427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3095340106171916290992569 2321505079628937218244427)
        ·
          refine ⟨3482257619443405827366641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321505079628937218244427 3482257619443405827366641)
          ·
            refine ⟨2611693214582554370524981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3482257619443405827366641 2611693214582554370524981)
            ·
              refine ⟨244846238867114472236717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2611693214582554370524981 244846238867114472236717)
              ·
                refine ⟨91817339575167927088769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244846238867114472236717 91817339575167927088769)
                ·
                  refine ⟨68863004681375945316577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91817339575167927088769 68863004681375945316577)
                  ·
                    rfl

theorem cell20_150874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_150874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150874 prefixEnd_150874 := by exact prefixLift 150874
  have htrace : WordTrace (prefixWord ++ tailWord_150874) baseStart_150874 baseEnd_150874 := by
    simpa [prefixWord, tailWord_150874, baseEnd_150874] using wordTrace_append hprefix tailTrace_150874
  have hstable : (prefixWord ++ tailWord_150874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150874).length < 2 ^ (prefixWord ++ tailWord_150874).sum := by decide
  have hdescent : baseEnd_150874 < baseStart_150874 := by decide
  rcases family_descends (prefixWord ++ tailWord_150874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150877 : List Nat := [1, 4, 5, 1, 1, 2, 6]
def baseStart_150877 : Nat := 118140960795 + 150877 * 2 ^ 59
def prefixEnd_150877 : Nat := 4983230072969 + 3 ^ 40 * 150877 * 2
def baseEnd_150877 : Nat := 7651597107013474246285

theorem tailTrace_150877 : CollatzResearch.WordTrace tailWord_150877 prefixEnd_150877 7651597107013474246285 := by
  unfold tailWord_150877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502936274405871585234885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3668624182937247723489923 5502936274405871585234885)
  ·
    refine ⟨1031800551451100922231541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5502936274405871585234885 1031800551451100922231541)
    ·
      refine ⟨96731301698540711459207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1031800551451100922231541 96731301698540711459207)
      ·
        refine ⟨145096952547811067188811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96731301698540711459207 145096952547811067188811)
        ·
          refine ⟨217645428821716600783217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145096952547811067188811 217645428821716600783217)
          ·
            refine ⟨163234071616287450587413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217645428821716600783217 163234071616287450587413)
            ·
              refine ⟨7651597107013474246285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163234071616287450587413 7651597107013474246285)
              ·
                rfl

theorem cell20_150877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 6].length) (baseStart_150877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150877 prefixEnd_150877 := by exact prefixLift 150877
  have htrace : WordTrace (prefixWord ++ tailWord_150877) baseStart_150877 baseEnd_150877 := by
    simpa [prefixWord, tailWord_150877, baseEnd_150877] using wordTrace_append hprefix tailTrace_150877
  have hstable : (prefixWord ++ tailWord_150877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150877).length < 2 ^ (prefixWord ++ tailWord_150877).sum := by decide
  have hdescent : baseEnd_150877 < baseStart_150877 := by decide
  rcases family_descends (prefixWord ++ tailWord_150877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150901 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 3]
def baseStart_150901 : Nat := 118140960795 + 150901 * 2 ^ 59
def prefixEnd_150901 : Nat := 4983230072969 + 3 ^ 40 * 150901 * 2
def baseEnd_150901 : Nat := 68875328217083851416467

theorem tailTrace_150901 : CollatzResearch.WordTrace tailWord_150901 prefixEnd_150901 68875328217083851416467 := by
  unfold tailWord_150901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503811626318923684108557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3669207750879282456072371 5503811626318923684108557)
  ·
    refine ⟨2063929359869596381540709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5503811626318923684108557 2063929359869596381540709)
    ·
      refine ⟨386986754975549321538883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2063929359869596381540709 386986754975549321538883)
      ·
        refine ⟨580480132463323982308325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386986754975549321538883 580480132463323982308325)
        ·
          refine ⟨108840024836873246682811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 580480132463323982308325 108840024836873246682811)
          ·
            refine ⟨163260037255309870024217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108840024836873246682811 163260037255309870024217)
            ·
              refine ⟨122445027941482402518163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163260037255309870024217 122445027941482402518163)
              ·
                refine ⟨183667541912223603777245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122445027941482402518163 183667541912223603777245)
                ·
                  refine ⟨68875328217083851416467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183667541912223603777245 68875328217083851416467)
                  ·
                    rfl

theorem cell20_150901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_150901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150901 prefixEnd_150901 := by exact prefixLift 150901
  have htrace : WordTrace (prefixWord ++ tailWord_150901) baseStart_150901 baseEnd_150901 := by
    simpa [prefixWord, tailWord_150901, baseEnd_150901] using wordTrace_append hprefix tailTrace_150901
  have hstable : (prefixWord ++ tailWord_150901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150901).length < 2 ^ (prefixWord ++ tailWord_150901).sum := by decide
  have hdescent : baseEnd_150901 < baseStart_150901 := by decide
  rcases family_descends (prefixWord ++ tailWord_150901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150923 : List Nat := [1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_150923 : Nat := 118140960795 + 150923 * 2 ^ 59
def prefixEnd_150923 : Nat := 4983230072969 + 3 ^ 40 * 150923 * 2
def baseEnd_150923 : Nat := 22961789872183184227681

theorem tailTrace_150923 : CollatzResearch.WordTrace tailWord_150923 prefixEnd_150923 22961789872183184227681 := by
  unfold tailWord_150923
  simp only [CollatzResearch.WordTrace]
  refine ⟨5504614032239221441409423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3669742688159480960939615 5504614032239221441409423)
  ·
    refine ⟨8256921048358832162114135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5504614032239221441409423 8256921048358832162114135)
    ·
      refine ⟨12385381572538248243171203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8256921048358832162114135 12385381572538248243171203)
      ·
        refine ⟨18578072358807372364756805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12385381572538248243171203 18578072358807372364756805)
        ·
          refine ⟨3483388567276382318391901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18578072358807372364756805 3483388567276382318391901)
          ·
            refine ⟨1306270712728643369396963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3483388567276382318391901 1306270712728643369396963)
            ·
              refine ⟨1959406069092965054095445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306270712728643369396963 1959406069092965054095445)
              ·
                refine ⟨22961789872183184227681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1959406069092965054095445 22961789872183184227681)
                ·
                  rfl

theorem cell20_150923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_150923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150923 prefixEnd_150923 := by exact prefixLift 150923
  have htrace : WordTrace (prefixWord ++ tailWord_150923) baseStart_150923 baseEnd_150923 := by
    simpa [prefixWord, tailWord_150923, baseEnd_150923] using wordTrace_append hprefix tailTrace_150923
  have hstable : (prefixWord ++ tailWord_150923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150923).length < 2 ^ (prefixWord ++ tailWord_150923).sum := by decide
  have hdescent : baseEnd_150923 < baseStart_150923 := by decide
  rcases family_descends (prefixWord ++ tailWord_150923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150940 : List Nat := [2, 2, 3, 4, 9]
def baseStart_150940 : Nat := 118140960795 + 150940 * 2 ^ 59
def prefixEnd_150940 : Nat := 4983230072969 + 3 ^ 40 * 150940 * 2
def baseEnd_150940 : Nat := 850532455305840112547

theorem tailTrace_150940 : CollatzResearch.WordTrace tailWord_150940 prefixEnd_150940 850532455305840112547 := by
  unfold tailWord_150940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752617036588816672389137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3670156048785088896518849 2752617036588816672389137)
  ·
    refine ⟨2064462777441612504291853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2752617036588816672389137 2064462777441612504291853)
    ·
      refine ⟨774173541540604689109445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2064462777441612504291853 774173541540604689109445)
      ·
        refine ⟨145157539038863379208021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 774173541540604689109445 145157539038863379208021)
        ·
          refine ⟨850532455305840112547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 145157539038863379208021 850532455305840112547)
          ·
            rfl

theorem cell20_150940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 9].length) (baseStart_150940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150940 prefixEnd_150940 := by exact prefixLift 150940
  have htrace : WordTrace (prefixWord ++ tailWord_150940) baseStart_150940 baseEnd_150940 := by
    simpa [prefixWord, tailWord_150940, baseEnd_150940] using wordTrace_append hprefix tailTrace_150940
  have hstable : (prefixWord ++ tailWord_150940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150940).length < 2 ^ (prefixWord ++ tailWord_150940).sum := by decide
  have hdescent : baseEnd_150940 < baseStart_150940 := by decide
  rcases family_descends (prefixWord ++ tailWord_150940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150942 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_150942 : Nat := 118140960795 + 150942 * 2 ^ 59
def prefixEnd_150942 : Nat := 4983230072969 + 3 ^ 40 * 150942 * 2
def baseEnd_150942 : Nat := 68894041734269931049633

theorem tailTrace_150942 : CollatzResearch.WordTrace tailWord_150942 prefixEnd_150942 68894041734269931049633 := by
  unfold tailWord_150942
  simp only [CollatzResearch.WordTrace]
  refine ⟨688163377396298460793885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3670204679446925124234053 688163377396298460793885)
  ·
    refine ⟨258061266523611922797707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 688163377396298460793885 258061266523611922797707)
    ·
      refine ⟨387091899785417884196561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258061266523611922797707 387091899785417884196561)
      ·
        refine ⟨290318924839063413147421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387091899785417884196561 290318924839063413147421)
        ·
          refine ⟨108869596814648779930283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290318924839063413147421 108869596814648779930283)
          ·
            refine ⟨163304395221973169895425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108869596814648779930283 163304395221973169895425)
            ·
              refine ⟨122478296416479877421569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163304395221973169895425 122478296416479877421569)
              ·
                refine ⟨91858722312359908066177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122478296416479877421569 91858722312359908066177)
                ·
                  refine ⟨68894041734269931049633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91858722312359908066177 68894041734269931049633)
                  ·
                    rfl

theorem cell20_150942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_150942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150942 prefixEnd_150942 := by exact prefixLift 150942
  have htrace : WordTrace (prefixWord ++ tailWord_150942) baseStart_150942 baseEnd_150942 := by
    simpa [prefixWord, tailWord_150942, baseEnd_150942] using wordTrace_append hprefix tailTrace_150942
  have hstable : (prefixWord ++ tailWord_150942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150942).length < 2 ^ (prefixWord ++ tailWord_150942).sum := by decide
  have hdescent : baseEnd_150942 < baseStart_150942 := by decide
  rcases family_descends (prefixWord ++ tailWord_150942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150946 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_150946 : Nat := 118140960795 + 150946 * 2 ^ 59
def prefixEnd_150946 : Nat := 4983230072969 + 3 ^ 40 * 150946 * 2
def baseEnd_150946 : Nat := 68895867443263694916283

theorem tailTrace_150946 : CollatzResearch.WordTrace tailWord_150946 prefixEnd_150946 68895867443263694916283 := by
  unfold tailWord_150946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376363227788974092374173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3670301940770597579664461 1376363227788974092374173)
  ·
    refine ⟨516136210420865284640315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1376363227788974092374173 516136210420865284640315)
    ·
      refine ⟨774204315631297926960473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516136210420865284640315 774204315631297926960473)
      ·
        refine ⟨580653236723473445220355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774204315631297926960473 580653236723473445220355)
        ·
          refine ⟨870979855085210167830533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580653236723473445220355 870979855085210167830533)
          ·
            refine ⟨163308722828476906468225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 870979855085210167830533 163308722828476906468225)
            ·
              refine ⟨122481542121357679851169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163308722828476906468225 122481542121357679851169)
              ·
                refine ⟨91861156591018259888377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122481542121357679851169 91861156591018259888377)
                ·
                  refine ⟨68895867443263694916283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91861156591018259888377 68895867443263694916283)
                  ·
                    rfl

theorem cell20_150946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_150946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150946 prefixEnd_150946 := by exact prefixLift 150946
  have htrace : WordTrace (prefixWord ++ tailWord_150946) baseStart_150946 baseEnd_150946 := by
    simpa [prefixWord, tailWord_150946, baseEnd_150946] using wordTrace_append hprefix tailTrace_150946
  have hstable : (prefixWord ++ tailWord_150946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150946).length < 2 ^ (prefixWord ++ tailWord_150946).sum := by decide
  have hdescent : baseEnd_150946 < baseStart_150946 := by decide
  rcases family_descends (prefixWord ++ tailWord_150946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150957 : List Nat := [1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_150957 : Nat := 118140960795 + 150957 * 2 ^ 59
def prefixEnd_150957 : Nat := 4983230072969 + 3 ^ 40 * 150957 * 2
def baseEnd_150957 : Nat := 22966962714332181849857

theorem tailTrace_150957 : CollatzResearch.WordTrace tailWord_150957 prefixEnd_150957 22966962714332181849857 := by
  unfold tailWord_150957
  simp only [CollatzResearch.WordTrace]
  refine ⟨5505854114116045248147125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3670569409410696832098083 5505854114116045248147125)
  ·
    refine ⟨516173823198379242013793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5505854114116045248147125 516173823198379242013793)
    ·
      refine ⟨387130367398784431510345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 516173823198379242013793 387130367398784431510345)
      ·
        refine ⟨290347775549088323632759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387130367398784431510345 290347775549088323632759)
        ·
          refine ⟨435521663323632485449139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290347775549088323632759 435521663323632485449139)
          ·
            refine ⟨653282494985448728173709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435521663323632485449139 653282494985448728173709)
            ·
              refine ⟨244980935619543273065141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653282494985448728173709 244980935619543273065141)
              ·
                refine ⟨22966962714332181849857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244980935619543273065141 22966962714332181849857)
                ·
                  rfl

theorem cell20_150957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_150957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150957 prefixEnd_150957 := by exact prefixLift 150957
  have htrace : WordTrace (prefixWord ++ tailWord_150957) baseStart_150957 baseEnd_150957 := by
    simpa [prefixWord, tailWord_150957, baseEnd_150957] using wordTrace_append hprefix tailTrace_150957
  have hstable : (prefixWord ++ tailWord_150957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150957).length < 2 ^ (prefixWord ++ tailWord_150957).sum := by decide
  have hdescent : baseEnd_150957 < baseStart_150957 := by decide
  rcases family_descends (prefixWord ++ tailWord_150957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150988 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 2]
def baseStart_150988 : Nat := 118140960795 + 150988 * 2 ^ 59
def prefixEnd_150988 : Nat := 4983230072969 + 3 ^ 40 * 150988 * 2
def baseEnd_150988 : Nat := 68915037387698215516111

theorem tailTrace_150988 : CollatzResearch.WordTrace tailWord_150988 prefixEnd_150988 68915037387698215516111 := by
  unfold tailWord_150988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753492388501868771262809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3671323184669158361683745 2753492388501868771262809)
  ·
    refine ⟨2065119291376401578447107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2753492388501868771262809 2065119291376401578447107)
    ·
      refine ⟨3097678937064602367670661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065119291376401578447107 3097678937064602367670661)
      ·
        refine ⟨580814800699612943938249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3097678937064602367670661 580814800699612943938249)
        ·
          refine ⟨435611100524709707953687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580814800699612943938249 435611100524709707953687)
          ·
            refine ⟨653416650787064561930531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435611100524709707953687 653416650787064561930531)
            ·
              refine ⟨980124976180596842895797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653416650787064561930531 980124976180596842895797)
              ·
                refine ⟨91886716516930954021481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 980124976180596842895797 91886716516930954021481)
                ·
                  refine ⟨68915037387698215516111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91886716516930954021481 68915037387698215516111)
                  ·
                    rfl

theorem cell20_150988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_150988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150988 prefixEnd_150988 := by exact prefixLift 150988
  have htrace : WordTrace (prefixWord ++ tailWord_150988) baseStart_150988 baseEnd_150988 := by
    simpa [prefixWord, tailWord_150988, baseEnd_150988] using wordTrace_append hprefix tailTrace_150988
  have hstable : (prefixWord ++ tailWord_150988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150988).length < 2 ^ (prefixWord ++ tailWord_150988).sum := by decide
  have hdescent : baseEnd_150988 < baseStart_150988 := by decide
  rcases family_descends (prefixWord ++ tailWord_150988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150998 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_150998 : Nat := 118140960795 + 150998 * 2 ^ 59
def prefixEnd_150998 : Nat := 4983230072969 + 3 ^ 40 * 150998 * 2
def baseEnd_150998 : Nat := 68919601660182625182737

theorem tailTrace_150998 : CollatzResearch.WordTrace tailWord_150998 prefixEnd_150998 68919601660182625182737 := by
  unfold tailWord_150998
  simp only [CollatzResearch.WordTrace]
  refine ⟨344209344185469328149353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3671566337978339500259765 344209344185469328149353)
  ·
    refine ⟨258157008139101996112015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 344209344185469328149353 258157008139101996112015)
    ·
      refine ⟨387235512208652994168023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258157008139101996112015 387235512208652994168023)
      ·
        refine ⟨580853268312979491252035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387235512208652994168023 580853268312979491252035)
        ·
          refine ⟨871279902469469236878053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580853268312979491252035 871279902469469236878053)
          ·
            refine ⟨163364981713025481914635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 871279902469469236878053 163364981713025481914635)
            ·
              refine ⟨245047472569538222871953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163364981713025481914635 245047472569538222871953)
              ·
                refine ⟨183785604427153667153965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245047472569538222871953 183785604427153667153965)
                ·
                  refine ⟨68919601660182625182737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183785604427153667153965 68919601660182625182737)
                  ·
                    rfl

theorem cell20_150998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_150998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_150998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_150998 prefixEnd_150998 := by exact prefixLift 150998
  have htrace : WordTrace (prefixWord ++ tailWord_150998) baseStart_150998 baseEnd_150998 := by
    simpa [prefixWord, tailWord_150998, baseEnd_150998] using wordTrace_append hprefix tailTrace_150998
  have hstable : (prefixWord ++ tailWord_150998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150998).length < 2 ^ (prefixWord ++ tailWord_150998).sum := by decide
  have hdescent : baseEnd_150998 < baseStart_150998 := by decide
  rcases family_descends (prefixWord ++ tailWord_150998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151002 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_151002 : Nat := 118140960795 + 151002 * 2 ^ 59
def prefixEnd_151002 : Nat := 4983230072969 + 3 ^ 40 * 151002 * 2
def baseEnd_151002 : Nat := 68921427369176389049387

theorem tailTrace_151002 : CollatzResearch.WordTrace tailWord_151002 prefixEnd_151002 68921427369176389049387 := by
  unfold tailWord_151002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376873849738254483383815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3671663599302011955690173 1376873849738254483383815)
  ·
    refine ⟨2065310774607381725075723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1376873849738254483383815 2065310774607381725075723)
    ·
      refine ⟨3097966161911072587613585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065310774607381725075723 3097966161911072587613585)
      ·
        refine ⟨2323474621433304440710189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3097966161911072587613585 2323474621433304440710189)
        ·
          refine ⟨871302983037489165266321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2323474621433304440710189 871302983037489165266321)
          ·
            refine ⟨653477237278116873949741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871302983037489165266321 653477237278116873949741)
            ·
              refine ⟨245053963979293827731153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653477237278116873949741 245053963979293827731153)
              ·
                refine ⟨183790472984470370798365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245053963979293827731153 183790472984470370798365)
                ·
                  refine ⟨68921427369176389049387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183790472984470370798365 68921427369176389049387)
                  ·
                    rfl

theorem cell20_151002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_151002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151002 prefixEnd_151002 := by exact prefixLift 151002
  have htrace : WordTrace (prefixWord ++ tailWord_151002) baseStart_151002 baseEnd_151002 := by
    simpa [prefixWord, tailWord_151002, baseEnd_151002] using wordTrace_append hprefix tailTrace_151002
  have hstable : (prefixWord ++ tailWord_151002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151002).length < 2 ^ (prefixWord ++ tailWord_151002).sum := by decide
  have hdescent : baseEnd_151002 < baseStart_151002 := by decide
  rcases family_descends (prefixWord ++ tailWord_151002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151009 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_151009 : Nat := 118140960795 + 151009 * 2 ^ 59
def prefixEnd_151009 : Nat := 4983230072969 + 3 ^ 40 * 151009 * 2
def baseEnd_151009 : Nat := 68924622359915475816025

theorem tailTrace_151009 : CollatzResearch.WordTrace tailWord_151009 prefixEnd_151009 68924622359915475816025 := by
  unfold tailWord_151009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507750709927658129040081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3671833806618438752693387 5507750709927658129040081)
  ·
    refine ⟨4130813032445743596780061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5507750709927658129040081 4130813032445743596780061)
    ·
      refine ⟨1549054887167153848792523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4130813032445743596780061 1549054887167153848792523)
      ·
        refine ⟨2323582330750730773188785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549054887167153848792523 2323582330750730773188785)
        ·
          refine ⟨1742686748063048079891589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2323582330750730773188785 1742686748063048079891589)
          ·
            refine ⟨326753765261821514979673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1742686748063048079891589 326753765261821514979673)
            ·
              refine ⟨245065323946366136234755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326753765261821514979673 245065323946366136234755)
              ·
                refine ⟨367597985919549204352133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245065323946366136234755 367597985919549204352133)
                ·
                  refine ⟨68924622359915475816025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367597985919549204352133 68924622359915475816025)
                  ·
                    rfl

theorem cell20_151009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_151009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151009 prefixEnd_151009 := by exact prefixLift 151009
  have htrace : WordTrace (prefixWord ++ tailWord_151009) baseStart_151009 baseEnd_151009 := by
    simpa [prefixWord, tailWord_151009, baseEnd_151009] using wordTrace_append hprefix tailTrace_151009
  have hstable : (prefixWord ++ tailWord_151009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151009).length < 2 ^ (prefixWord ++ tailWord_151009).sum := by decide
  have hdescent : baseEnd_151009 < baseStart_151009 := by decide
  rcases family_descends (prefixWord ++ tailWord_151009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151023 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_151023 : Nat := 118140960795 + 151023 * 2 ^ 59
def prefixEnd_151023 : Nat := 4983230072969 + 3 ^ 40 * 151023 * 2
def baseEnd_151023 : Nat := 68931012341393649349301

theorem tailTrace_151023 : CollatzResearch.WordTrace tailWord_151023 prefixEnd_151023 68931012341393649349301 := by
  unfold tailWord_151023
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508261331876938520049723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3672174221251292346699815 5508261331876938520049723)
  ·
    refine ⟨8262391997815407780074585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5508261331876938520049723 8262391997815407780074585)
    ·
      refine ⟨6196793998361555835055939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8262391997815407780074585 6196793998361555835055939)
      ·
        refine ⟨9295190997542333752583909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196793998361555835055939 9295190997542333752583909)
        ·
          refine ⟨1742848312039187578609483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9295190997542333752583909 1742848312039187578609483)
          ·
            refine ⟨2614272468058781367914225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742848312039187578609483 2614272468058781367914225)
            ·
              refine ⟨1960704351044086025935669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614272468058781367914225 1960704351044086025935669)
              ·
                refine ⟨183816032910383064931469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1960704351044086025935669 183816032910383064931469)
                ·
                  refine ⟨68931012341393649349301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183816032910383064931469 68931012341393649349301)
                  ·
                    rfl

theorem cell20_151023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_151023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151023 prefixEnd_151023 := by exact prefixLift 151023
  have htrace : WordTrace (prefixWord ++ tailWord_151023) baseStart_151023 baseEnd_151023 := by
    simpa [prefixWord, tailWord_151023, baseEnd_151023] using wordTrace_append hprefix tailTrace_151023
  have hstable : (prefixWord ++ tailWord_151023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151023).length < 2 ^ (prefixWord ++ tailWord_151023).sum := by decide
  have hdescent : baseEnd_151023 < baseStart_151023 := by decide
  rcases family_descends (prefixWord ++ tailWord_151023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151046 : List Nat := [6, 2, 1, 1, 3, 1, 6]
def baseStart_151046 : Nat := 118140960795 + 151046 * 2 ^ 59
def prefixEnd_151046 : Nat := 4983230072969 + 3 ^ 40 * 151046 * 2
def baseEnd_151046 : Nat := 7660167796456421286949

theorem tailTrace_151046 : CollatzResearch.WordTrace tailWord_151046 prefixEnd_151046 7660167796456421286949 := by
  unfold tailWord_151046
  simp only [CollatzResearch.WordTrace]
  refine ⟨172159381587300420254281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3672733473862408965424661 172159381587300420254281)
  ·
    refine ⟨129119536190475315190711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172159381587300420254281 129119536190475315190711)
    ·
      refine ⟨193679304285712972786067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129119536190475315190711 193679304285712972786067)
      ·
        refine ⟨290518956428569459179101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193679304285712972786067 290518956428569459179101)
        ·
          refine ⟨108944608660713547192163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290518956428569459179101 108944608660713547192163)
          ·
            refine ⟨163416912991070320788245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108944608660713547192163 163416912991070320788245)
            ·
              refine ⟨7660167796456421286949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163416912991070320788245 7660167796456421286949)
              ·
                rfl

theorem cell20_151046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 6].length) (baseStart_151046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151046 prefixEnd_151046 := by exact prefixLift 151046
  have htrace : WordTrace (prefixWord ++ tailWord_151046) baseStart_151046 baseEnd_151046 := by
    simpa [prefixWord, tailWord_151046, baseEnd_151046] using wordTrace_append hprefix tailTrace_151046
  have hstable : (prefixWord ++ tailWord_151046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151046).length < 2 ^ (prefixWord ++ tailWord_151046).sum := by decide
  have hdescent : baseEnd_151046 < baseStart_151046 := by decide
  rcases family_descends (prefixWord ++ tailWord_151046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151060 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 4]
def baseStart_151060 : Nat := 118140960795 + 151060 * 2 ^ 59
def prefixEnd_151060 : Nat := 4983230072969 + 3 ^ 40 * 151060 * 2
def baseEnd_151060 : Nat := 68947900149585965115817

theorem tailTrace_151060 : CollatzResearch.WordTrace tailWord_151060 prefixEnd_151060 68947900149585965115817 := by
  unfold tailWord_151060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754805416371446919573317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3673073888495262559431089 2754805416371446919573317)
  ·
    refine ⟨516526015569646297419997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2754805416371446919573317 516526015569646297419997)
    ·
      refine ⟨193697255838617361532499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 516526015569646297419997 193697255838617361532499)
      ·
        refine ⟨290545883757926042298749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193697255838617361532499 290545883757926042298749)
        ·
          refine ⟨108954706409222265862031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290545883757926042298749 108954706409222265862031)
          ·
            refine ⟨163432059613833398793047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108954706409222265862031 163432059613833398793047)
            ·
              refine ⟨245148089420750098189571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163432059613833398793047 245148089420750098189571)
              ·
                refine ⟨367722134131125147284357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245148089420750098189571 367722134131125147284357)
                ·
                  refine ⟨68947900149585965115817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367722134131125147284357 68947900149585965115817)
                  ·
                    rfl

theorem cell20_151060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_151060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151060 prefixEnd_151060 := by exact prefixLift 151060
  have htrace : WordTrace (prefixWord ++ tailWord_151060) baseStart_151060 baseEnd_151060 := by
    simpa [prefixWord, tailWord_151060, baseEnd_151060] using wordTrace_append hprefix tailTrace_151060
  have hstable : (prefixWord ++ tailWord_151060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151060).length < 2 ^ (prefixWord ++ tailWord_151060).sum := by decide
  have hdescent : baseEnd_151060 < baseStart_151060 := by decide
  rcases family_descends (prefixWord ++ tailWord_151060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151061 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_151061 : Nat := 118140960795 + 151061 * 2 ^ 59
def prefixEnd_151061 : Nat := 4983230072969 + 3 ^ 40 * 151061 * 2
def baseEnd_151061 : Nat := 68948356576834406082479

theorem tailTrace_151061 : CollatzResearch.WordTrace tailWord_151061 prefixEnd_151061 68948356576834406082479 := by
  unfold tailWord_151061
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509647305739271009933037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3673098203826180673288691 5509647305739271009933037)
  ·
    refine ⟨2066117739652226628724889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5509647305739271009933037 2066117739652226628724889)
    ·
      refine ⟨1549588304739169971543667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2066117739652226628724889 1549588304739169971543667)
      ·
        refine ⟨2324382457108754957315501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549588304739169971543667 2324382457108754957315501)
        ·
          refine ⟨871643421415783108993313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2324382457108754957315501 871643421415783108993313)
          ·
            refine ⟨653732566061837331744985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871643421415783108993313 653732566061837331744985)
            ·
              refine ⟨490299424546377998808739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653732566061837331744985 490299424546377998808739)
              ·
                refine ⟨735449136819566998213109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490299424546377998808739 735449136819566998213109)
                ·
                  refine ⟨68948356576834406082479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 735449136819566998213109 68948356576834406082479)
                  ·
                    rfl

theorem cell20_151061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_151061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151061 prefixEnd_151061 := by exact prefixLift 151061
  have htrace : WordTrace (prefixWord ++ tailWord_151061) baseStart_151061 baseEnd_151061 := by
    simpa [prefixWord, tailWord_151061, baseEnd_151061] using wordTrace_append hprefix tailTrace_151061
  have hstable : (prefixWord ++ tailWord_151061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151061).length < 2 ^ (prefixWord ++ tailWord_151061).sum := by decide
  have hdescent : baseEnd_151061 < baseStart_151061 := by decide
  rcases family_descends (prefixWord ++ tailWord_151061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151064 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_151064 : Nat := 118140960795 + 151064 * 2 ^ 59
def prefixEnd_151064 : Nat := 4983230072969 + 3 ^ 40 * 151064 * 2
def baseEnd_151064 : Nat := 68949725858579728982467

theorem tailTrace_151064 : CollatzResearch.WordTrace tailWord_151064 prefixEnd_151064 68949725858579728982467 := by
  unfold tailWord_151064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754878362364201261146123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3673171149818935014861497 2754878362364201261146123)
  ·
    refine ⟨4132317543546301891719185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754878362364201261146123 4132317543546301891719185)
    ·
      refine ⟨3099238157659726418789389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4132317543546301891719185 3099238157659726418789389)
      ·
        refine ⟨1162214309122397407046021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3099238157659726418789389 1162214309122397407046021)
        ·
          refine ⟨217915182960449513821129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1162214309122397407046021 217915182960449513821129)
          ·
            refine ⟨163436387220337135365847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217915182960449513821129 163436387220337135365847)
            ·
              refine ⟨245154580830505703048771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163436387220337135365847 245154580830505703048771)
              ·
                refine ⟨367731871245758554573157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245154580830505703048771 367731871245758554573157)
                ·
                  refine ⟨68949725858579728982467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367731871245758554573157 68949725858579728982467)
                  ·
                    rfl

theorem cell20_151064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_151064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151064 prefixEnd_151064 := by exact prefixLift 151064
  have htrace : WordTrace (prefixWord ++ tailWord_151064) baseStart_151064 baseEnd_151064 := by
    simpa [prefixWord, tailWord_151064, baseEnd_151064] using wordTrace_append hprefix tailTrace_151064
  have hstable : (prefixWord ++ tailWord_151064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151064).length < 2 ^ (prefixWord ++ tailWord_151064).sum := by decide
  have hdescent : baseEnd_151064 < baseStart_151064 := by decide
  rcases family_descends (prefixWord ++ tailWord_151064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151116 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_151116 : Nat := 118140960795 + 151116 * 2 ^ 59
def prefixEnd_151116 : Nat := 4983230072969 + 3 ^ 40 * 151116 * 2
def baseEnd_151116 : Nat := 68973460075498659248921

theorem tailTrace_151116 : CollatzResearch.WordTrace tailWord_151116 prefixEnd_151116 68973460075498659248921 := by
  unfold tailWord_151116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755826660270007701592601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3674435547026676935456801 2755826660270007701592601)
  ·
    refine ⟨2066869995202505776194451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2755826660270007701592601 2066869995202505776194451)
    ·
      refine ⟨3100304992803758664291677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066869995202505776194451 3100304992803758664291677)
      ·
        refine ⟨1162614372301409499109379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3100304992803758664291677 1162614372301409499109379)
        ·
          refine ⟨1743921558452114248664069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162614372301409499109379 1743921558452114248664069)
          ·
            refine ⟨326985292209771421624513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1743921558452114248664069 326985292209771421624513)
            ·
              refine ⟨245238969157328566218385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326985292209771421624513 245238969157328566218385)
              ·
                refine ⟨183929226867996424663789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245238969157328566218385 183929226867996424663789)
                ·
                  refine ⟨68973460075498659248921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183929226867996424663789 68973460075498659248921)
                  ·
                    rfl

theorem cell20_151116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_151116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151116 prefixEnd_151116 := by exact prefixLift 151116
  have htrace : WordTrace (prefixWord ++ tailWord_151116) baseStart_151116 baseEnd_151116 := by
    simpa [prefixWord, tailWord_151116, baseEnd_151116] using wordTrace_append hprefix tailTrace_151116
  have hstable : (prefixWord ++ tailWord_151116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151116).length < 2 ^ (prefixWord ++ tailWord_151116).sum := by decide
  have hdescent : baseEnd_151116 < baseStart_151116 := by decide
  rcases family_descends (prefixWord ++ tailWord_151116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151137 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_151137 : Nat := 118140960795 + 151137 * 2 ^ 59
def prefixEnd_151137 : Nat := 4983230072969 + 3 ^ 40 * 151137 * 2
def baseEnd_151137 : Nat := 68983045047715919548835

theorem tailTrace_151137 : CollatzResearch.WordTrace tailWord_151137 prefixEnd_151137 68983045047715919548835 := by
  unfold tailWord_151137
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512419253463935989699665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3674946168975957326466443 5512419253463935989699665)
  ·
    refine ⟨4134314440097951992274749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5512419253463935989699665 4134314440097951992274749)
    ·
      refine ⟨1550367915036731997103031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4134314440097951992274749 1550367915036731997103031)
      ·
        refine ⟨2325551872555097995654547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550367915036731997103031 2325551872555097995654547)
        ·
          refine ⟨3488327808832646993481821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325551872555097995654547 3488327808832646993481821)
          ·
            refine ⟨1308122928312242622555683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3488327808832646993481821 1308122928312242622555683)
            ·
              refine ⟨1962184392468363933833525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308122928312242622555683 1962184392468363933833525)
              ·
                refine ⟨183954786793909118796893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1962184392468363933833525 183954786793909118796893)
                ·
                  refine ⟨68983045047715919548835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183954786793909118796893 68983045047715919548835)
                  ·
                    rfl

theorem cell20_151137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_151137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151137 prefixEnd_151137 := by exact prefixLift 151137
  have htrace : WordTrace (prefixWord ++ tailWord_151137) baseStart_151137 baseEnd_151137 := by
    simpa [prefixWord, tailWord_151137, baseEnd_151137] using wordTrace_append hprefix tailTrace_151137
  have hstable : (prefixWord ++ tailWord_151137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151137).length < 2 ^ (prefixWord ++ tailWord_151137).sum := by decide
  have hdescent : baseEnd_151137 < baseStart_151137 := by decide
  rcases family_descends (prefixWord ++ tailWord_151137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151157 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 2]
def baseStart_151157 : Nat := 118140960795 + 151157 * 2 ^ 59
def prefixEnd_151157 : Nat := 4983230072969 + 3 ^ 40 * 151157 * 2
def baseEnd_151157 : Nat := 68992173592684738882087

theorem tailTrace_151157 : CollatzResearch.WordTrace tailWord_151157 prefixEnd_151157 68992173592684738882087 := by
  unfold tailWord_151157
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513148713391479405427725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3675432475594319603618483 5513148713391479405427725)
  ·
    refine ⟨2067430767521804777035397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5513148713391479405427725 2067430767521804777035397)
    ·
      refine ⟨387643268910338395694137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2067430767521804777035397 387643268910338395694137)
      ·
        refine ⟨290732451682753796770603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387643268910338395694137 290732451682753796770603)
        ·
          refine ⟨436098677524130695155905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290732451682753796770603 436098677524130695155905)
          ·
            refine ⟨327074008143098021366929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436098677524130695155905 327074008143098021366929)
            ·
              refine ⟨245305506107323516025197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327074008143098021366929 245305506107323516025197)
              ·
                refine ⟨91989564790246318509449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245305506107323516025197 91989564790246318509449)
                ·
                  refine ⟨68992173592684738882087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91989564790246318509449 68992173592684738882087)
                  ·
                    rfl

theorem cell20_151157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_151157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151157 prefixEnd_151157 := by exact prefixLift 151157
  have htrace : WordTrace (prefixWord ++ tailWord_151157) baseStart_151157 baseEnd_151157 := by
    simpa [prefixWord, tailWord_151157, baseEnd_151157] using wordTrace_append hprefix tailTrace_151157
  have hstable : (prefixWord ++ tailWord_151157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151157).length < 2 ^ (prefixWord ++ tailWord_151157).sum := by decide
  have hdescent : baseEnd_151157 < baseStart_151157 := by decide
  rcases family_descends (prefixWord ++ tailWord_151157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151175 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_151175 : Nat := 118140960795 + 151175 * 2 ^ 59
def prefixEnd_151175 : Nat := 4983230072969 + 3 ^ 40 * 151175 * 2
def baseEnd_151175 : Nat := 69000389283156676282013

theorem tailTrace_151175 : CollatzResearch.WordTrace tailWord_151175 prefixEnd_151175 69000389283156676282013 := by
  unfold tailWord_151175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513805227326268479582979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3675870151550845653055319 5513805227326268479582979)
  ·
    refine ⟨8270707840989402719374469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5513805227326268479582979 8270707840989402719374469)
    ·
      refine ⟨1550757720185513009882713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8270707840989402719374469 1550757720185513009882713)
      ·
        refine ⟨1163068290139134757412035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1550757720185513009882713 1163068290139134757412035)
        ·
          refine ⟨1744602435208702136118053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163068290139134757412035 1744602435208702136118053)
          ·
            refine ⟨327112956601631650522135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1744602435208702136118053 327112956601631650522135)
            ·
              refine ⟨490669434902447475783203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327112956601631650522135 490669434902447475783203)
              ·
                refine ⟨736004152353671213674805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490669434902447475783203 736004152353671213674805)
                ·
                  refine ⟨69000389283156676282013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 736004152353671213674805 69000389283156676282013)
                  ·
                    rfl

theorem cell20_151175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_151175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151175 prefixEnd_151175 := by exact prefixLift 151175
  have htrace : WordTrace (prefixWord ++ tailWord_151175) baseStart_151175 baseEnd_151175 := by
    simpa [prefixWord, tailWord_151175, baseEnd_151175] using wordTrace_append hprefix tailTrace_151175
  have hstable : (prefixWord ++ tailWord_151175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151175).length < 2 ^ (prefixWord ++ tailWord_151175).sum := by decide
  have hdescent : baseEnd_151175 < baseStart_151175 := by decide
  rcases family_descends (prefixWord ++ tailWord_151175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151178 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_151178 : Nat := 118140960795 + 151178 * 2 ^ 59
def prefixEnd_151178 : Nat := 4983230072969 + 3 ^ 40 * 151178 * 2
def baseEnd_151178 : Nat := 69001758564901999182001

theorem tailTrace_151178 : CollatzResearch.WordTrace tailWord_151178 prefixEnd_151178 69001758564901999182001 := by
  unfold tailWord_151178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378478661578849997985547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3675943097543599994628125 1378478661578849997985547)
  ·
    refine ⟨2067717992368274996978321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1378478661578849997985547 2067717992368274996978321)
    ·
      refine ⟨1550788494276206247733741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2067717992368274996978321 1550788494276206247733741)
      ·
        refine ⟨581545685353577342900153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1550788494276206247733741 581545685353577342900153)
        ·
          refine ⟨436159264015183007175115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581545685353577342900153 436159264015183007175115)
          ·
            refine ⟨654238896022774510762673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436159264015183007175115 654238896022774510762673)
            ·
              refine ⟨490679172017080883072005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654238896022774510762673 490679172017080883072005)
              ·
                refine ⟨92002344753202665576001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 490679172017080883072005 92002344753202665576001)
                ·
                  refine ⟨69001758564901999182001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92002344753202665576001 69001758564901999182001)
                  ·
                    rfl

theorem cell20_151178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_151178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151178 prefixEnd_151178 := by exact prefixLift 151178
  have htrace : WordTrace (prefixWord ++ tailWord_151178) baseStart_151178 baseEnd_151178 := by
    simpa [prefixWord, tailWord_151178, baseEnd_151178] using wordTrace_append hprefix tailTrace_151178
  have hstable : (prefixWord ++ tailWord_151178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151178).length < 2 ^ (prefixWord ++ tailWord_151178).sum := by decide
  have hdescent : baseEnd_151178 < baseStart_151178 := by decide
  rcases family_descends (prefixWord ++ tailWord_151178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151188 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_151188 : Nat := 118140960795 + 151188 * 2 ^ 59
def prefixEnd_151188 : Nat := 4983230072969 + 3 ^ 40 * 151188 * 2
def baseEnd_151188 : Nat := 69006322837386408848627

theorem tailTrace_151188 : CollatzResearch.WordTrace tailWord_151188 prefixEnd_151188 69006322837386408848627 := by
  unfold tailWord_151188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757139688139585849903109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3676186250852781133204145 2757139688139585849903109)
  ·
    refine ⟨516963691526172346856833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2757139688139585849903109 516963691526172346856833)
    ·
      refine ⟨387722768644629260142625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 516963691526172346856833 387722768644629260142625)
      ·
        refine ⟨290792076483471945106969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387722768644629260142625 290792076483471945106969)
        ·
          refine ⟨218094057362603958830227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290792076483471945106969 218094057362603958830227)
          ·
            refine ⟨327141086043905938245341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218094057362603958830227 327141086043905938245341)
            ·
              refine ⟨122677907266464726842003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327141086043905938245341 122677907266464726842003)
              ·
                refine ⟨184016860899697090263005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122677907266464726842003 184016860899697090263005)
                ·
                  refine ⟨69006322837386408848627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184016860899697090263005 69006322837386408848627)
                  ·
                    rfl

theorem cell20_151188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_151188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151188 prefixEnd_151188 := by exact prefixLift 151188
  have htrace : WordTrace (prefixWord ++ tailWord_151188) baseStart_151188 baseEnd_151188 := by
    simpa [prefixWord, tailWord_151188, baseEnd_151188] using wordTrace_append hprefix tailTrace_151188
  have hstable : (prefixWord ++ tailWord_151188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151188).length < 2 ^ (prefixWord ++ tailWord_151188).sum := by decide
  have hdescent : baseEnd_151188 < baseStart_151188 := by decide
  rcases family_descends (prefixWord ++ tailWord_151188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151208 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 2]
def baseStart_151208 : Nat := 118140960795 + 151208 * 2 ^ 59
def prefixEnd_151208 : Nat := 4983230072969 + 3 ^ 40 * 151208 * 2
def baseEnd_151208 : Nat := 69015451382355228181879

theorem tailTrace_151208 : CollatzResearch.WordTrace tailWord_151208 prefixEnd_151208 69015451382355228181879 := by
  unfold tailWord_151208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757504418103357557767139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3676672557471143410356185 2757504418103357557767139)
  ·
    refine ⟨4136256627155036336650709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2757504418103357557767139 4136256627155036336650709)
    ·
      refine ⟨96943514698946164140251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4136256627155036336650709 96943514698946164140251)
      ·
        refine ⟨145415272048419246210377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96943514698946164140251 145415272048419246210377)
        ·
          refine ⟨109061454036314434657783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145415272048419246210377 109061454036314434657783)
          ·
            refine ⟨163592181054471651986675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109061454036314434657783 163592181054471651986675)
            ·
              refine ⟨245388271581707477980013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163592181054471651986675 245388271581707477980013)
              ·
                refine ⟨92020601843140304242505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245388271581707477980013 92020601843140304242505)
                ·
                  refine ⟨69015451382355228181879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92020601843140304242505 69015451382355228181879)
                  ·
                    rfl

theorem cell20_151208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_151208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151208 prefixEnd_151208 := by exact prefixLift 151208
  have htrace : WordTrace (prefixWord ++ tailWord_151208) baseStart_151208 baseEnd_151208 := by
    simpa [prefixWord, tailWord_151208, baseEnd_151208] using wordTrace_append hprefix tailTrace_151208
  have hstable : (prefixWord ++ tailWord_151208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151208).length < 2 ^ (prefixWord ++ tailWord_151208).sum := by decide
  have hdescent : baseEnd_151208 < baseStart_151208 := by decide
  rcases family_descends (prefixWord ++ tailWord_151208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151213 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_151213 : Nat := 118140960795 + 151213 * 2 ^ 59
def prefixEnd_151213 : Nat := 4983230072969 + 3 ^ 40 * 151213 * 2
def baseEnd_151213 : Nat := 69017733518597433015191

theorem tailTrace_151213 : CollatzResearch.WordTrace tailWord_151213 prefixEnd_151213 69017733518597433015191 := by
  unfold tailWord_151213
  simp only [CollatzResearch.WordTrace]
  refine ⟨5515191201188600969466293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3676794134125733979644195 5515191201188600969466293)
  ·
    refine ⟨517049175111431340887465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5515191201188600969466293 517049175111431340887465)
    ·
      refine ⟨387786881333573505665599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 517049175111431340887465 387786881333573505665599)
      ·
        refine ⟨581680322000360258498399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387786881333573505665599 581680322000360258498399)
        ·
          refine ⟨872520483000540387747599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581680322000360258498399 872520483000540387747599)
          ·
            refine ⟨1308780724500810581621399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872520483000540387747599 1308780724500810581621399)
            ·
              refine ⟨1963171086751215872432099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308780724500810581621399 1963171086751215872432099)
              ·
                refine ⟨2944756630126823808648149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963171086751215872432099 2944756630126823808648149)
                ·
                  refine ⟨69017733518597433015191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2944756630126823808648149 69017733518597433015191)
                  ·
                    rfl

theorem cell20_151213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_151213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151213 prefixEnd_151213 := by exact prefixLift 151213
  have htrace : WordTrace (prefixWord ++ tailWord_151213) baseStart_151213 baseEnd_151213 := by
    simpa [prefixWord, tailWord_151213, baseEnd_151213] using wordTrace_append hprefix tailTrace_151213
  have hstable : (prefixWord ++ tailWord_151213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151213).length < 2 ^ (prefixWord ++ tailWord_151213).sum := by decide
  have hdescent : baseEnd_151213 < baseStart_151213 := by decide
  rcases family_descends (prefixWord ++ tailWord_151213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151330 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_151330 : Nat := 118140960795 + 151330 * 2 ^ 59
def prefixEnd_151330 : Nat := 4983230072969 + 3 ^ 40 * 151330 * 2
def baseEnd_151330 : Nat := 69071135506665026114713

theorem tailTrace_151330 : CollatzResearch.WordTrace tailWord_151330 prefixEnd_151330 69071135506665026114713 := by
  unfold tailWord_151330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379864635441182487868861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3679639027843153300983629 1379864635441182487868861)
  ·
    refine ⟨517449238290443432950823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1379864635441182487868861 517449238290443432950823)
    ·
      refine ⟨776173857435665149426235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517449238290443432950823 776173857435665149426235)
      ·
        refine ⟨1164260786153497724139353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776173857435665149426235 1164260786153497724139353)
        ·
          refine ⟨873195589615123293104515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1164260786153497724139353 873195589615123293104515)
          ·
            refine ⟨1309793384422684939656773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873195589615123293104515 1309793384422684939656773)
            ·
              refine ⟨245586259579253426185645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1309793384422684939656773 245586259579253426185645)
              ·
                refine ⟨92094847342220034819617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245586259579253426185645 92094847342220034819617)
                ·
                  refine ⟨69071135506665026114713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92094847342220034819617 69071135506665026114713)
                  ·
                    rfl

theorem cell20_151330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_151330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151330 prefixEnd_151330 := by exact prefixLift 151330
  have htrace : WordTrace (prefixWord ++ tailWord_151330) baseStart_151330 baseEnd_151330 := by
    simpa [prefixWord, tailWord_151330, baseEnd_151330] using wordTrace_append hprefix tailTrace_151330
  have hstable : (prefixWord ++ tailWord_151330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151330).length < 2 ^ (prefixWord ++ tailWord_151330).sum := by decide
  have hdescent : baseEnd_151330 < baseStart_151330 := by decide
  rcases family_descends (prefixWord ++ tailWord_151330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151386 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_151386 : Nat := 118140960795 + 151386 * 2 ^ 59
def prefixEnd_151386 : Nat := 4983230072969 + 3 ^ 40 * 151386 * 2
def baseEnd_151386 : Nat := 69096695432577720247817

theorem tailTrace_151386 : CollatzResearch.WordTrace tailWord_151386 prefixEnd_151386 69096695432577720247817 := by
  unfold tailWord_151386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380375257390462878878503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3681000686374567677009341 1380375257390462878878503)
  ·
    refine ⟨2070562886085694318317755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1380375257390462878878503 2070562886085694318317755)
    ·
      refine ⟨3105844329128541477476633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2070562886085694318317755 3105844329128541477476633)
      ·
        refine ⟨2329383246846406108107475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3105844329128541477476633 2329383246846406108107475)
        ·
          refine ⟨3494074870269609162161213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329383246846406108107475 3494074870269609162161213)
          ·
            refine ⟨1310278076351103435810455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3494074870269609162161213 1310278076351103435810455)
            ·
              refine ⟨1965417114526655153715683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310278076351103435810455 1965417114526655153715683)
              ·
                refine ⟨2948125671789982730573525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965417114526655153715683 2948125671789982730573525)
                ·
                  refine ⟨69096695432577720247817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2948125671789982730573525 69096695432577720247817)
                  ·
                    rfl

theorem cell20_151386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_151386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151386 prefixEnd_151386 := by exact prefixLift 151386
  have htrace : WordTrace (prefixWord ++ tailWord_151386) baseStart_151386 baseEnd_151386 := by
    simpa [prefixWord, tailWord_151386, baseEnd_151386] using wordTrace_append hprefix tailTrace_151386
  have hstable : (prefixWord ++ tailWord_151386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151386).length < 2 ^ (prefixWord ++ tailWord_151386).sum := by decide
  have hdescent : baseEnd_151386 < baseStart_151386 := by decide
  rcases family_descends (prefixWord ++ tailWord_151386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151396 : List Nat := [2, 3, 1, 1, 5, 2, 6]
def baseStart_151396 : Nat := 118140960795 + 151396 * 2 ^ 59
def prefixEnd_151396 : Nat := 4983230072969 + 3 ^ 40 * 151396 * 2
def baseEnd_151396 : Nat := 7677917745006903323827

theorem tailTrace_151396 : CollatzResearch.WordTrace tailWord_151396 prefixEnd_151396 7677917745006903323827 := by
  unfold tailWord_151396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760932879762811611689021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3681243839683748815585361 2760932879762811611689021)
  ·
    refine ⟨1035349829911054354383383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2760932879762811611689021 1035349829911054354383383)
    ·
      refine ⟨1553024744866581531575075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035349829911054354383383 1553024744866581531575075)
      ·
        refine ⟨2329537117299872297362613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553024744866581531575075 2329537117299872297362613)
        ·
          refine ⟨218394104746863027877745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2329537117299872297362613 218394104746863027877745)
          ·
            refine ⟨163795578560147270908309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218394104746863027877745 163795578560147270908309)
            ·
              refine ⟨7677917745006903323827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163795578560147270908309 7677917745006903323827)
              ·
                rfl

theorem cell20_151396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 6].length) (baseStart_151396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151396 prefixEnd_151396 := by exact prefixLift 151396
  have htrace : WordTrace (prefixWord ++ tailWord_151396) baseStart_151396 baseEnd_151396 := by
    simpa [prefixWord, tailWord_151396, baseEnd_151396] using wordTrace_append hprefix tailTrace_151396
  have hstable : (prefixWord ++ tailWord_151396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151396).length < 2 ^ (prefixWord ++ tailWord_151396).sum := by decide
  have hdescent : baseEnd_151396 < baseStart_151396 := by decide
  rcases family_descends (prefixWord ++ tailWord_151396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151402 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_151402 : Nat := 118140960795 + 151402 * 2 ^ 59
def prefixEnd_151402 : Nat := 4983230072969 + 3 ^ 40 * 151402 * 2
def baseEnd_151402 : Nat := 69103998268552775714419

theorem tailTrace_151402 : CollatzResearch.WordTrace tailWord_151402 prefixEnd_151402 69103998268552775714419 := by
  unfold tailWord_151402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380521149375971562024115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3681389731669257498730973 1380521149375971562024115)
  ·
    refine ⟨2070781724063957343036173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1380521149375971562024115 2070781724063957343036173)
    ·
      refine ⟨776543146523984003638565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2070781724063957343036173 776543146523984003638565)
      ·
        refine ⟨145601839973247000682231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 776543146523984003638565 145601839973247000682231)
        ·
          refine ⟨218402759959870501023347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145601839973247000682231 218402759959870501023347)
          ·
            refine ⟨327604139939805751535021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218402759959870501023347 327604139939805751535021)
            ·
              refine ⟨122851552477427156825633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327604139939805751535021 122851552477427156825633)
              ·
                refine ⟨92138664358070367619225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122851552477427156825633 92138664358070367619225)
                ·
                  refine ⟨69103998268552775714419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92138664358070367619225 69103998268552775714419)
                  ·
                    rfl

theorem cell20_151402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_151402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151402 prefixEnd_151402 := by exact prefixLift 151402
  have htrace : WordTrace (prefixWord ++ tailWord_151402) baseStart_151402 baseEnd_151402 := by
    simpa [prefixWord, tailWord_151402, baseEnd_151402] using wordTrace_append hprefix tailTrace_151402
  have hstable : (prefixWord ++ tailWord_151402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151402).length < 2 ^ (prefixWord ++ tailWord_151402).sum := by decide
  have hdescent : baseEnd_151402 < baseStart_151402 := by decide
  rcases family_descends (prefixWord ++ tailWord_151402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151406 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_151406 : Nat := 118140960795 + 151406 * 2 ^ 59
def prefixEnd_151406 : Nat := 4983230072969 + 3 ^ 40 * 151406 * 2
def baseEnd_151406 : Nat := 69105823977546539581069

theorem tailTrace_151406 : CollatzResearch.WordTrace tailWord_151406 prefixEnd_151406 69105823977546539581069 := by
  unfold tailWord_151406
  simp only [CollatzResearch.WordTrace]
  refine ⟨690278811186174366405259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3681486992992929954161381 690278811186174366405259)
  ·
    refine ⟨1035418216779261549607889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 690278811186174366405259 1035418216779261549607889)
    ·
      refine ⟨776563662584446162205917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035418216779261549607889 776563662584446162205917)
      ·
        refine ⟨291211373469167310827219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 776563662584446162205917 291211373469167310827219)
        ·
          refine ⟨436817060203750966240829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291211373469167310827219 436817060203750966240829)
          ·
            refine ⟨163806397576406612340311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 436817060203750966240829 163806397576406612340311)
            ·
              refine ⟨245709596364609918510467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163806397576406612340311 245709596364609918510467)
              ·
                refine ⟨368564394546914877765701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245709596364609918510467 368564394546914877765701)
                ·
                  refine ⟨69105823977546539581069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368564394546914877765701 69105823977546539581069)
                  ·
                    rfl

theorem cell20_151406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_151406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151406 prefixEnd_151406 := by exact prefixLift 151406
  have htrace : WordTrace (prefixWord ++ tailWord_151406) baseStart_151406 baseEnd_151406 := by
    simpa [prefixWord, tailWord_151406, baseEnd_151406] using wordTrace_append hprefix tailTrace_151406
  have hstable : (prefixWord ++ tailWord_151406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151406).length < 2 ^ (prefixWord ++ tailWord_151406).sum := by decide
  have hdescent : baseEnd_151406 < baseStart_151406 := by decide
  rcases family_descends (prefixWord ++ tailWord_151406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151417 : List Nat := [1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_151417 : Nat := 118140960795 + 151417 * 2 ^ 59
def prefixEnd_151417 : Nat := 4983230072969 + 3 ^ 40 * 151417 * 2
def baseEnd_151417 : Nat := 23036948225759796738119

theorem tailTrace_151417 : CollatzResearch.WordTrace tailWord_151417 prefixEnd_151417 23036948225759796738119 := by
  unfold tailWord_151417
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522631692449543809892505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3681754461633029206595003 5522631692449543809892505)
  ·
    refine ⟨4141973769337157857419379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5522631692449543809892505 4141973769337157857419379)
    ·
      refine ⟨6212960654005736786129069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4141973769337157857419379 6212960654005736786129069)
      ·
        refine ⟨2329860245252151294798401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6212960654005736786129069 2329860245252151294798401)
        ·
          refine ⟨1747395183939113471098801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2329860245252151294798401 1747395183939113471098801)
          ·
            refine ⟨1310546387954335103324101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747395183939113471098801 1310546387954335103324101)
            ·
              refine ⟨245727447741437831873269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1310546387954335103324101 245727447741437831873269)
              ·
                refine ⟨23036948225759796738119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 245727447741437831873269 23036948225759796738119)
                ·
                  rfl

theorem cell20_151417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_151417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151417 prefixEnd_151417 := by exact prefixLift 151417
  have htrace : WordTrace (prefixWord ++ tailWord_151417) baseStart_151417 baseEnd_151417 := by
    simpa [prefixWord, tailWord_151417, baseEnd_151417] using wordTrace_append hprefix tailTrace_151417
  have hstable : (prefixWord ++ tailWord_151417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151417).length < 2 ^ (prefixWord ++ tailWord_151417).sum := by decide
  have hdescent : baseEnd_151417 < baseStart_151417 := by decide
  rcases family_descends (prefixWord ++ tailWord_151417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151454 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_151454 : Nat := 118140960795 + 151454 * 2 ^ 59
def prefixEnd_151454 : Nat := 4983230072969 + 3 ^ 40 * 151454 * 2
def baseEnd_151454 : Nat := 69127732485471705980873

theorem tailTrace_151454 : CollatzResearch.WordTrace tailWord_151454 prefixEnd_151454 69127732485471705980873 := by
  unfold tailWord_151454
  simp only [CollatzResearch.WordTrace]
  refine ⟨690497649164437391123677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3682654128876999419326277 690497649164437391123677)
  ·
    refine ⟨258936618436664021671379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 690497649164437391123677 258936618436664021671379)
    ·
      refine ⟨388404927654996032507069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258936618436664021671379 388404927654996032507069)
      ·
        refine ⟨145651847870623512190151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388404927654996032507069 145651847870623512190151)
        ·
          refine ⟨218477771805935268285227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145651847870623512190151 218477771805935268285227)
          ·
            refine ⟨327716657708902902427841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218477771805935268285227 327716657708902902427841)
            ·
              refine ⟨245787493281677176820881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327716657708902902427841 245787493281677176820881)
              ·
                refine ⟨184340619961257882615661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245787493281677176820881 184340619961257882615661)
                ·
                  refine ⟨69127732485471705980873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184340619961257882615661 69127732485471705980873)
                  ·
                    rfl

theorem cell20_151454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_151454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151454 prefixEnd_151454 := by exact prefixLift 151454
  have htrace : WordTrace (prefixWord ++ tailWord_151454) baseStart_151454 baseEnd_151454 := by
    simpa [prefixWord, tailWord_151454, baseEnd_151454] using wordTrace_append hprefix tailTrace_151454
  have hstable : (prefixWord ++ tailWord_151454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151454).length < 2 ^ (prefixWord ++ tailWord_151454).sum := by decide
  have hdescent : baseEnd_151454 < baseStart_151454 := by decide
  rcases family_descends (prefixWord ++ tailWord_151454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151455 : List Nat := [1, 1, 2, 5, 3, 8]
def baseStart_151455 : Nat := 118140960795 + 151455 * 2 ^ 59
def prefixEnd_151455 : Nat := 4983230072969 + 3 ^ 40 * 151455 * 2
def baseEnd_151455 : Nat := 2560303293063709146205

theorem tailTrace_151455 : CollatzResearch.WordTrace tailWord_151455 prefixEnd_151455 2560303293063709146205 := by
  unfold tailWord_151455
  simp only [CollatzResearch.WordTrace]
  refine ⟨5524017666311876299775819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3682678444207917533183879 5524017666311876299775819)
  ·
    refine ⟨8286026499467814449663729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5524017666311876299775819 8286026499467814449663729)
    ·
      refine ⟨6214519874600860837247797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8286026499467814449663729 6214519874600860837247797)
      ·
        refine ⟨582611238243830703491981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6214519874600860837247797 582611238243830703491981)
        ·
          refine ⟨218479214341436513809493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 582611238243830703491981 218479214341436513809493)
          ·
            refine ⟨2560303293063709146205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 218479214341436513809493 2560303293063709146205)
            ·
              rfl

theorem cell20_151455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 8].length) (baseStart_151455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151455 prefixEnd_151455 := by exact prefixLift 151455
  have htrace : WordTrace (prefixWord ++ tailWord_151455) baseStart_151455 baseEnd_151455 := by
    simpa [prefixWord, tailWord_151455, baseEnd_151455] using wordTrace_append hprefix tailTrace_151455
  have hstable : (prefixWord ++ tailWord_151455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151455).length < 2 ^ (prefixWord ++ tailWord_151455).sum := by decide
  have hdescent : baseEnd_151455 < baseStart_151455 := by decide
  rcases family_descends (prefixWord ++ tailWord_151455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151486 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_151486 : Nat := 118140960795 + 151486 * 2 ^ 59
def prefixEnd_151486 : Nat := 4983230072969 + 3 ^ 40 * 151486 * 2
def baseEnd_151486 : Nat := 69142338157421816914075

theorem tailTrace_151486 : CollatzResearch.WordTrace tailWord_151486 prefixEnd_151486 69142338157421816914075 := by
  unfold tailWord_151486
  simp only [CollatzResearch.WordTrace]
  refine ⟨690643541149946074269289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3683432219466379062769541 690643541149946074269289)
  ·
    refine ⟨517982655862459555701967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 690643541149946074269289 517982655862459555701967)
    ·
      refine ⟨776973983793689333552951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517982655862459555701967 776973983793689333552951)
      ·
        refine ⟨1165460975690534000329427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776973983793689333552951 1165460975690534000329427)
        ·
          refine ⟨1748191463535801000494141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165460975690534000329427 1748191463535801000494141)
          ·
            refine ⟨655571798825925375185303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1748191463535801000494141 655571798825925375185303)
            ·
              refine ⟨983357698238888062777955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655571798825925375185303 983357698238888062777955)
              ·
                refine ⟨1475036547358332094166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983357698238888062777955 1475036547358332094166933)
                ·
                  refine ⟨69142338157421816914075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1475036547358332094166933 69142338157421816914075)
                  ·
                    rfl

theorem cell20_151486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_151486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151486 prefixEnd_151486 := by exact prefixLift 151486
  have htrace : WordTrace (prefixWord ++ tailWord_151486) baseStart_151486 baseEnd_151486 := by
    simpa [prefixWord, tailWord_151486, baseEnd_151486] using wordTrace_append hprefix tailTrace_151486
  have hstable : (prefixWord ++ tailWord_151486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151486).length < 2 ^ (prefixWord ++ tailWord_151486).sum := by decide
  have hdescent : baseEnd_151486 < baseStart_151486 := by decide
  rcases family_descends (prefixWord ++ tailWord_151486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151503 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 2]
def baseStart_151503 : Nat := 118140960795 + 151503 * 2 ^ 59
def prefixEnd_151503 : Nat := 4983230072969 + 3 ^ 40 * 151503 * 2
def baseEnd_151503 : Nat := 69150097420645313347339

theorem tailTrace_151503 : CollatzResearch.WordTrace tailWord_151503 prefixEnd_151503 69150097420645313347339 := by
  unfold tailWord_151503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525768370137980497523163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3683845580091986998348775 5525768370137980497523163)
  ·
    refine ⟨8288652555206970746284745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5525768370137980497523163 8288652555206970746284745)
    ·
      refine ⟨6216489416405228059713559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8288652555206970746284745 6216489416405228059713559)
      ·
        refine ⟨9324734124607842089570339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6216489416405228059713559 9324734124607842089570339)
        ·
          refine ⟨13987101186911763134355509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9324734124607842089570339 13987101186911763134355509)
          ·
            refine ⟨1311290736272977793845829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13987101186911763134355509 1311290736272977793845829)
            ·
              refine ⟨245867013051183336346093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1311290736272977793845829 245867013051183336346093)
              ·
                refine ⟨92200129894193751129785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245867013051183336346093 92200129894193751129785)
                ·
                  refine ⟨69150097420645313347339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92200129894193751129785 69150097420645313347339)
                  ·
                    rfl

theorem cell20_151503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 2].length) (baseStart_151503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151503 prefixEnd_151503 := by exact prefixLift 151503
  have htrace : WordTrace (prefixWord ++ tailWord_151503) baseStart_151503 baseEnd_151503 := by
    simpa [prefixWord, tailWord_151503, baseEnd_151503] using wordTrace_append hprefix tailTrace_151503
  have hstable : (prefixWord ++ tailWord_151503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151503).length < 2 ^ (prefixWord ++ tailWord_151503).sum := by decide
  have hdescent : baseEnd_151503 < baseStart_151503 := by decide
  rcases family_descends (prefixWord ++ tailWord_151503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151513 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 3]
def baseStart_151513 : Nat := 118140960795 + 151513 * 2 ^ 59
def prefixEnd_151513 : Nat := 4983230072969 + 3 ^ 40 * 151513 * 2
def baseEnd_151513 : Nat := 69154661693129723013965

theorem tailTrace_151513 : CollatzResearch.WordTrace tailWord_151513 prefixEnd_151513 69154661693129723013965 := by
  unfold tailWord_151513
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526133100101752205387193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3684088733401168136924795 5526133100101752205387193)
  ·
    refine ⟨4144599825076314154040395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5526133100101752205387193 4144599825076314154040395)
    ·
      refine ⟨6216899737614471231060593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4144599825076314154040395 6216899737614471231060593)
      ·
        refine ⟨4662674803210853423295445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6216899737614471231060593 4662674803210853423295445)
        ·
          refine ⟨109281440700254377108487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4662674803210853423295445 109281440700254377108487)
          ·
            refine ⟨163922161050381565662731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109281440700254377108487 163922161050381565662731)
            ·
              refine ⟨245883241575572348494097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163922161050381565662731 245883241575572348494097)
              ·
                refine ⟨184412431181679261370573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245883241575572348494097 184412431181679261370573)
                ·
                  refine ⟨69154661693129723013965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184412431181679261370573 69154661693129723013965)
                  ·
                    rfl

theorem cell20_151513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_151513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151513 prefixEnd_151513 := by exact prefixLift 151513
  have htrace : WordTrace (prefixWord ++ tailWord_151513) baseStart_151513 baseEnd_151513 := by
    simpa [prefixWord, tailWord_151513, baseEnd_151513] using wordTrace_append hprefix tailTrace_151513
  have hstable : (prefixWord ++ tailWord_151513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151513).length < 2 ^ (prefixWord ++ tailWord_151513).sum := by decide
  have hdescent : baseEnd_151513 < baseStart_151513 := by decide
  rcases family_descends (prefixWord ++ tailWord_151513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151524 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_151524 : Nat := 118140960795 + 151524 * 2 ^ 59
def prefixEnd_151524 : Nat := 4983230072969 + 3 ^ 40 * 151524 * 2
def baseEnd_151524 : Nat := 69159682392862573647253

theorem tailTrace_151524 : CollatzResearch.WordTrace tailWord_151524 prefixEnd_151524 69159682392862573647253 := by
  unfold tailWord_151524
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763267151530950542018813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3684356202041267389358417 2763267151530950542018813)
  ·
    refine ⟨1036225181824106453257055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2763267151530950542018813 1036225181824106453257055)
    ·
      refine ⟨1554337772736159679885583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036225181824106453257055 1554337772736159679885583)
      ·
        refine ⟨2331506659104239519828375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554337772736159679885583 2331506659104239519828375)
        ·
          refine ⟨3497259988656359279742563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331506659104239519828375 3497259988656359279742563)
          ·
            refine ⟨5245889982984538919613845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497259988656359279742563 5245889982984538919613845)
            ·
              refine ⟨245901092952400261856899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5245889982984538919613845 245901092952400261856899)
              ·
                refine ⟨368851639428600392785349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245901092952400261856899 368851639428600392785349)
                ·
                  refine ⟨69159682392862573647253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368851639428600392785349 69159682392862573647253)
                  ·
                    rfl

theorem cell20_151524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_151524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151524 prefixEnd_151524 := by exact prefixLift 151524
  have htrace : WordTrace (prefixWord ++ tailWord_151524) baseStart_151524 baseEnd_151524 := by
    simpa [prefixWord, tailWord_151524, baseEnd_151524] using wordTrace_append hprefix tailTrace_151524
  have hstable : (prefixWord ++ tailWord_151524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151524).length < 2 ^ (prefixWord ++ tailWord_151524).sum := by decide
  have hdescent : baseEnd_151524 < baseStart_151524 := by decide
  rcases family_descends (prefixWord ++ tailWord_151524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151575 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 2]
def baseStart_151575 : Nat := 118140960795 + 151575 * 2 ^ 59
def prefixEnd_151575 : Nat := 4983230072969 + 3 ^ 40 * 151575 * 2
def baseEnd_151575 : Nat := 69182960182533062947045

theorem tailTrace_151575 : CollatzResearch.WordTrace tailWord_151575 prefixEnd_151575 69182960182533062947045 := by
  unfold tailWord_151575
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528394425877136794144179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3685596283918091196096119 5528394425877136794144179)
  ·
    refine ⟨8292591638815705191216269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528394425877136794144179 8292591638815705191216269)
    ·
      refine ⟨3109721864555889446706101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8292591638815705191216269 3109721864555889446706101)
      ·
        refine ⟨291536424802114635628697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3109721864555889446706101 291536424802114635628697)
        ·
          refine ⟨218652318601585976721523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291536424802114635628697 218652318601585976721523)
          ·
            refine ⟨327978477902378965082285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218652318601585976721523 327978477902378965082285)
            ·
              refine ⟨122991929213392111905857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327978477902378965082285 122991929213392111905857)
              ·
                refine ⟨92243946910044083929393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122991929213392111905857 92243946910044083929393)
                ·
                  refine ⟨69182960182533062947045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92243946910044083929393 69182960182533062947045)
                  ·
                    rfl

theorem cell20_151575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 2].length) (baseStart_151575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151575 prefixEnd_151575 := by exact prefixLift 151575
  have htrace : WordTrace (prefixWord ++ tailWord_151575) baseStart_151575 baseEnd_151575 := by
    simpa [prefixWord, tailWord_151575, baseEnd_151575] using wordTrace_append hprefix tailTrace_151575
  have hstable : (prefixWord ++ tailWord_151575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151575).length < 2 ^ (prefixWord ++ tailWord_151575).sum := by decide
  have hdescent : baseEnd_151575 < baseStart_151575 := by decide
  rcases family_descends (prefixWord ++ tailWord_151575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151576 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_151576 : Nat := 118140960795 + 151576 * 2 ^ 59
def prefixEnd_151576 : Nat := 4983230072969 + 3 ^ 40 * 151576 * 2
def baseEnd_151576 : Nat := 69183416609781503913707

theorem tailTrace_151576 : CollatzResearch.WordTrace tailWord_151576 prefixEnd_151576 69183416609781503913707 := by
  unfold tailWord_151576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764215449436756982465291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3685620599249009309953721 2764215449436756982465291)
  ·
    refine ⟨4146323174155135473697937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2764215449436756982465291 4146323174155135473697937)
    ·
      refine ⟨3109742380616351605273453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4146323174155135473697937 3109742380616351605273453)
      ·
        refine ⟨1166153392731131851977545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3109742380616351605273453 1166153392731131851977545)
        ·
          refine ⟨874615044548348888983159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166153392731131851977545 874615044548348888983159)
          ·
            refine ⟨1311922566822523333474739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874615044548348888983159 1311922566822523333474739)
            ·
              refine ⟨1967883850233785000212109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311922566822523333474739 1967883850233785000212109)
              ·
                refine ⟨737956443837669375079541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1967883850233785000212109 737956443837669375079541)
                ·
                  refine ⟨69183416609781503913707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 737956443837669375079541 69183416609781503913707)
                  ·
                    rfl

theorem cell20_151576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_151576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151576 prefixEnd_151576 := by exact prefixLift 151576
  have htrace : WordTrace (prefixWord ++ tailWord_151576) baseStart_151576 baseEnd_151576 := by
    simpa [prefixWord, tailWord_151576, baseEnd_151576] using wordTrace_append hprefix tailTrace_151576
  have hstable : (prefixWord ++ tailWord_151576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151576).length < 2 ^ (prefixWord ++ tailWord_151576).sum := by decide
  have hdescent : baseEnd_151576 < baseStart_151576 := by decide
  rcases family_descends (prefixWord ++ tailWord_151576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151634 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_151634 : Nat := 118140960795 + 151634 * 2 ^ 59
def prefixEnd_151634 : Nat := 4983230072969 + 3 ^ 40 * 151634 * 2
def baseEnd_151634 : Nat := 69209889390191079980137

theorem tailTrace_151634 : CollatzResearch.WordTrace tailWord_151634 prefixEnd_151634 69209889390191079980137 := by
  unfold tailWord_151634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382636583165847467635489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3687030888442259913694637 1382636583165847467635489)
  ·
    refine ⟨1036977437374385600726617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1382636583165847467635489 1036977437374385600726617)
    ·
      refine ⟨777733078030789200544963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1036977437374385600726617 777733078030789200544963)
      ·
        refine ⟨1166599617046183800817445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777733078030789200544963 1166599617046183800817445)
        ·
          refine ⟨218737428196159462653271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1166599617046183800817445 218737428196159462653271)
          ·
            refine ⟨328106142294239193979907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218737428196159462653271 328106142294239193979907)
            ·
              refine ⟨492159213441358790969861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328106142294239193979907 492159213441358790969861)
              ·
                refine ⟨92279852520254773306849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492159213441358790969861 92279852520254773306849)
                ·
                  refine ⟨69209889390191079980137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92279852520254773306849 69209889390191079980137)
                  ·
                    rfl

theorem cell20_151634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_151634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151634 prefixEnd_151634 := by exact prefixLift 151634
  have htrace : WordTrace (prefixWord ++ tailWord_151634) baseStart_151634 baseEnd_151634 := by
    simpa [prefixWord, tailWord_151634, baseEnd_151634] using wordTrace_append hprefix tailTrace_151634
  have hstable : (prefixWord ++ tailWord_151634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151634).length < 2 ^ (prefixWord ++ tailWord_151634).sum := by decide
  have hdescent : baseEnd_151634 < baseStart_151634 := by decide
  rcases family_descends (prefixWord ++ tailWord_151634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151662 : List Nat := [4, 1, 2, 2, 1, 1, 5, 4]
def baseStart_151662 : Nat := 118140960795 + 151662 * 2 ^ 59
def prefixEnd_151662 : Nat := 4983230072969 + 3 ^ 40 * 151662 * 2
def baseEnd_151662 : Nat := 23074223117715809015563

theorem tailTrace_151662 : CollatzResearch.WordTrace tailWord_151662 prefixEnd_151662 23074223117715809015563 := by
  unfold tailWord_151662
  simp only [CollatzResearch.WordTrace]
  refine ⟨691445947070243831570155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3687711717707967101707493 691445947070243831570155)
  ·
    refine ⟨1037168920605365747355233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691445947070243831570155 1037168920605365747355233)
    ·
      refine ⟨777876690454024310516425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037168920605365747355233 777876690454024310516425)
      ·
        refine ⟨583407517840518232887319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777876690454024310516425 583407517840518232887319)
        ·
          refine ⟨875111276760777349330979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583407517840518232887319 875111276760777349330979)
          ·
            refine ⟨1312666915141166023996469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875111276760777349330979 1312666915141166023996469)
            ·
              refine ⟨123062523294484314749669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1312666915141166023996469 123062523294484314749669)
              ·
                refine ⟨23074223117715809015563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123062523294484314749669 23074223117715809015563)
                ·
                  rfl

theorem cell20_151662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_151662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151662 prefixEnd_151662 := by exact prefixLift 151662
  have htrace : WordTrace (prefixWord ++ tailWord_151662) baseStart_151662 baseEnd_151662 := by
    simpa [prefixWord, tailWord_151662, baseEnd_151662] using wordTrace_append hprefix tailTrace_151662
  have hstable : (prefixWord ++ tailWord_151662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151662).length < 2 ^ (prefixWord ++ tailWord_151662).sum := by decide
  have hdescent : baseEnd_151662 < baseStart_151662 := by decide
  rcases family_descends (prefixWord ++ tailWord_151662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151762 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_151762 : Nat := 118140960795 + 151762 * 2 ^ 59
def prefixEnd_151762 : Nat := 4983230072969 + 3 ^ 40 * 151762 * 2
def baseEnd_151762 : Nat := 69268312077991523712947

theorem tailTrace_151762 : CollatzResearch.WordTrace tailWord_151762 prefixEnd_151762 69268312077991523712947 := by
  unfold tailWord_151762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383803719049916932800385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3690143250799778487467693 1383803719049916932800385)
  ·
    refine ⟨1037852789287437699600289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1383803719049916932800385 1037852789287437699600289)
    ·
      refine ⟨778389591965578274700217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037852789287437699600289 778389591965578274700217)
      ·
        refine ⟨583792193974183706025163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 778389591965578274700217 583792193974183706025163)
        ·
          refine ⟨875688290961275559037745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583792193974183706025163 875688290961275559037745)
          ·
            refine ⟨656766218220956669278309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875688290961275559037745 656766218220956669278309)
            ·
              refine ⟨123143665916429375489683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 656766218220956669278309 123143665916429375489683)
              ·
                refine ⟨184715498874644063234525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123143665916429375489683 184715498874644063234525)
                ·
                  refine ⟨69268312077991523712947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184715498874644063234525 69268312077991523712947)
                  ·
                    rfl

theorem cell20_151762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_151762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151762 prefixEnd_151762 := by exact prefixLift 151762
  have htrace : WordTrace (prefixWord ++ tailWord_151762) baseStart_151762 baseEnd_151762 := by
    simpa [prefixWord, tailWord_151762, baseEnd_151762] using wordTrace_append hprefix tailTrace_151762
  have hstable : (prefixWord ++ tailWord_151762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151762).length < 2 ^ (prefixWord ++ tailWord_151762).sum := by decide
  have hdescent : baseEnd_151762 < baseStart_151762 := by decide
  rcases family_descends (prefixWord ++ tailWord_151762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151811 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_151811 : Nat := 118140960795 + 151811 * 2 ^ 59
def prefixEnd_151811 : Nat := 4983230072969 + 3 ^ 40 * 151811 * 2
def baseEnd_151811 : Nat := 69290677013165131079413

theorem tailTrace_151811 : CollatzResearch.WordTrace tailWord_151811 prefixEnd_151811 69290677013165131079413 := by
  unfold tailWord_151811
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537002053022149099735287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3691334702014766066490191 5537002053022149099735287)
  ·
    refine ⟨8305503079533223649602931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5537002053022149099735287 8305503079533223649602931)
    ·
      refine ⟨12458254619299835474404397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8305503079533223649602931 12458254619299835474404397)
      ·
        refine ⟨4671845482237438302901649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12458254619299835474404397 4671845482237438302901649)
        ·
          refine ⟨3503884111678078727176237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4671845482237438302901649 3503884111678078727176237)
          ·
            refine ⟨1313956541879279522691089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3503884111678078727176237 1313956541879279522691089)
            ·
              refine ⟨985467406409459642018317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313956541879279522691089 985467406409459642018317)
              ·
                refine ⟨369550277403547365756869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 985467406409459642018317 369550277403547365756869)
                ·
                  refine ⟨69290677013165131079413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369550277403547365756869 69290677013165131079413)
                  ·
                    rfl

theorem cell20_151811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_151811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151811 prefixEnd_151811 := by exact prefixLift 151811
  have htrace : WordTrace (prefixWord ++ tailWord_151811) baseStart_151811 baseEnd_151811 := by
    simpa [prefixWord, tailWord_151811, baseEnd_151811] using wordTrace_append hprefix tailTrace_151811
  have hstable : (prefixWord ++ tailWord_151811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151811).length < 2 ^ (prefixWord ++ tailWord_151811).sum := by decide
  have hdescent : baseEnd_151811 < baseStart_151811 := by decide
  rcases family_descends (prefixWord ++ tailWord_151811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151866 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_151866 : Nat := 118140960795 + 151866 * 2 ^ 59
def prefixEnd_151866 : Nat := 4983230072969 + 3 ^ 40 * 151866 * 2
def baseEnd_151866 : Nat := 69315780511829384245855

theorem tailTrace_151866 : CollatzResearch.WordTrace tailWord_151866 prefixEnd_151866 69315780511829384245855 := by
  unfold tailWord_151866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384752016955723373246863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3692672045215262328658301 1384752016955723373246863)
  ·
    refine ⟨2077128025433585059870295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384752016955723373246863 2077128025433585059870295)
    ·
      refine ⟨3115692038150377589805443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077128025433585059870295 3115692038150377589805443)
      ·
        refine ⟨4673538057225566384708165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115692038150377589805443 4673538057225566384708165)
        ·
          refine ⟨876288385729793697132781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4673538057225566384708165 876288385729793697132781)
          ·
            refine ⟨328608144648672636424793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 876288385729793697132781 328608144648672636424793)
            ·
              refine ⟨246456108486504477318595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328608144648672636424793 246456108486504477318595)
              ·
                refine ⟨369684162729756715977893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246456108486504477318595 369684162729756715977893)
                ·
                  refine ⟨69315780511829384245855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369684162729756715977893 69315780511829384245855)
                  ·
                    rfl

theorem cell20_151866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_151866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151866 prefixEnd_151866 := by exact prefixLift 151866
  have htrace : WordTrace (prefixWord ++ tailWord_151866) baseStart_151866 baseEnd_151866 := by
    simpa [prefixWord, tailWord_151866, baseEnd_151866] using wordTrace_append hprefix tailTrace_151866
  have hstable : (prefixWord ++ tailWord_151866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151866).length < 2 ^ (prefixWord ++ tailWord_151866).sum := by decide
  have hdescent : baseEnd_151866 < baseStart_151866 := by decide
  rcases family_descends (prefixWord ++ tailWord_151866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151880 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_151880 : Nat := 118140960795 + 151880 * 2 ^ 59
def prefixEnd_151880 : Nat := 4983230072969 + 3 ^ 40 * 151880 * 2
def baseEnd_151880 : Nat := 69322170493307557779131

theorem tailTrace_151880 : CollatzResearch.WordTrace tailWord_151880 prefixEnd_151880 69322170493307557779131 := by
  unfold tailWord_151880
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769759344886086941998547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3693012459848115922664729 2769759344886086941998547)
  ·
    refine ⟨4154639017329130412997821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2769759344886086941998547 4154639017329130412997821)
    ·
      refine ⟨1557989631498423904874183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4154639017329130412997821 1557989631498423904874183)
      ·
        refine ⟨2336984447247635857311275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557989631498423904874183 2336984447247635857311275)
        ·
          refine ⟨3505476670871453785966913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336984447247635857311275 3505476670871453785966913)
          ·
            refine ⟨2629107503153590339475185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3505476670871453785966913 2629107503153590339475185)
            ·
              refine ⟨1971830627365192754606389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2629107503153590339475185 1971830627365192754606389)
              ·
                refine ⟨184859121315486820744349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1971830627365192754606389 184859121315486820744349)
                ·
                  refine ⟨69322170493307557779131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184859121315486820744349 69322170493307557779131)
                  ·
                    rfl

theorem cell20_151880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_151880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151880 prefixEnd_151880 := by exact prefixLift 151880
  have htrace : WordTrace (prefixWord ++ tailWord_151880) baseStart_151880 baseEnd_151880 := by
    simpa [prefixWord, tailWord_151880, baseEnd_151880] using wordTrace_append hprefix tailTrace_151880
  have hstable : (prefixWord ++ tailWord_151880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151880).length < 2 ^ (prefixWord ++ tailWord_151880).sum := by decide
  have hdescent : baseEnd_151880 < baseStart_151880 := by decide
  rcases family_descends (prefixWord ++ tailWord_151880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151911 : List Nat := [1, 1, 5, 1, 3, 3, 6]
def baseStart_151911 : Nat := 118140960795 + 151911 * 2 ^ 59
def prefixEnd_151911 : Nat := 4983230072969 + 3 ^ 40 * 151911 * 2
def baseEnd_151911 : Nat := 7704035526445469749519

theorem tailTrace_151911 : CollatzResearch.WordTrace tailWord_151911 prefixEnd_151911 7704035526445469749519 := by
  unfold tailWord_151911
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540649352659866178375587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3693766235106577452250391 5540649352659866178375587)
  ·
    refine ⟨8310974028989799267563381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5540649352659866178375587 8310974028989799267563381)
    ·
      refine ⟨779153815217793681334067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8310974028989799267563381 779153815217793681334067)
      ·
        refine ⟨1168730722826690522001101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 779153815217793681334067 1168730722826690522001101)
        ·
          refine ⟨438274021060008945750413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1168730722826690522001101 438274021060008945750413)
          ·
            refine ⟨164352757897503354656405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 438274021060008945750413 164352757897503354656405)
            ·
              refine ⟨7704035526445469749519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 164352757897503354656405 7704035526445469749519)
              ·
                rfl

theorem cell20_151911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_151911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151911 prefixEnd_151911 := by exact prefixLift 151911
  have htrace : WordTrace (prefixWord ++ tailWord_151911) baseStart_151911 baseEnd_151911 := by
    simpa [prefixWord, tailWord_151911, baseEnd_151911] using wordTrace_append hprefix tailTrace_151911
  have hstable : (prefixWord ++ tailWord_151911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151911).length < 2 ^ (prefixWord ++ tailWord_151911).sum := by decide
  have hdescent : baseEnd_151911 < baseStart_151911 := by decide
  rcases family_descends (prefixWord ++ tailWord_151911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151976 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 2]
def baseStart_151976 : Nat := 118140960795 + 151976 * 2 ^ 59
def prefixEnd_151976 : Nat := 4983230072969 + 3 ^ 40 * 151976 * 2
def baseEnd_151976 : Nat := 69365987509157890578739

theorem tailTrace_151976 : CollatzResearch.WordTrace tailWord_151976 prefixEnd_151976 69365987509157890578739 := by
  unfold tailWord_151976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771510048712191139745891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3695346731616254852994521 2771510048712191139745891)
  ·
    refine ⟨4157265073068286709618837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2771510048712191139745891 4157265073068286709618837)
    ·
      refine ⟨194871800300075939513383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4157265073068286709618837 194871800300075939513383)
      ·
        refine ⟨292307700450113909270075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194871800300075939513383 292307700450113909270075)
        ·
          refine ⟨438461550675170863905113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292307700450113909270075 438461550675170863905113)
          ·
            refine ⟨328846163006378147928835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438461550675170863905113 328846163006378147928835)
            ·
              refine ⟨493269244509567221893253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328846163006378147928835 493269244509567221893253)
              ·
                refine ⟨92487983345543854104985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493269244509567221893253 92487983345543854104985)
                ·
                  refine ⟨69365987509157890578739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92487983345543854104985 69365987509157890578739)
                  ·
                    rfl

theorem cell20_151976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_151976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151976 prefixEnd_151976 := by exact prefixLift 151976
  have htrace : WordTrace (prefixWord ++ tailWord_151976) baseStart_151976 baseEnd_151976 := by
    simpa [prefixWord, tailWord_151976, baseEnd_151976] using wordTrace_append hprefix tailTrace_151976
  have hstable : (prefixWord ++ tailWord_151976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151976).length < 2 ^ (prefixWord ++ tailWord_151976).sum := by decide
  have hdescent : baseEnd_151976 < baseStart_151976 := by decide
  rcases family_descends (prefixWord ++ tailWord_151976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151977 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_151977 : Nat := 118140960795 + 151977 * 2 ^ 59
def prefixEnd_151977 : Nat := 4983230072969 + 3 ^ 40 * 151977 * 2
def baseEnd_151977 : Nat := 69366443936406331545401

theorem tailTrace_151977 : CollatzResearch.WordTrace tailWord_151977 prefixEnd_151977 69366443936406331545401 := by
  unfold tailWord_151977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543056570420759450278185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3695371046947172966852123 5543056570420759450278185)
  ·
    refine ⟨4157292427815569587708639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5543056570420759450278185 4157292427815569587708639)
    ·
      refine ⟨6235938641723354381562959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157292427815569587708639 6235938641723354381562959)
      ·
        refine ⟨9353907962585031572344439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6235938641723354381562959 9353907962585031572344439)
        ·
          refine ⟨14030861943877547358516659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353907962585031572344439 14030861943877547358516659)
          ·
            refine ⟨21046292915816321037774989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030861943877547358516659 21046292915816321037774989)
            ·
              refine ⟨7892359843431120389165621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21046292915816321037774989 7892359843431120389165621)
              ·
                refine ⟨739908735321667536484277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7892359843431120389165621 739908735321667536484277)
                ·
                  refine ⟨69366443936406331545401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 739908735321667536484277 69366443936406331545401)
                  ·
                    rfl

theorem cell20_151977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_151977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_151977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_151977 prefixEnd_151977 := by exact prefixLift 151977
  have htrace : WordTrace (prefixWord ++ tailWord_151977) baseStart_151977 baseEnd_151977 := by
    simpa [prefixWord, tailWord_151977, baseEnd_151977] using wordTrace_append hprefix tailTrace_151977
  have hstable : (prefixWord ++ tailWord_151977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151977).length < 2 ^ (prefixWord ++ tailWord_151977).sum := by decide
  have hdescent : baseEnd_151977 < baseStart_151977 := by decide
  rcases family_descends (prefixWord ++ tailWord_151977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152015 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_152015 : Nat := 118140960795 + 152015 * 2 ^ 59
def prefixEnd_152015 : Nat := 4983230072969 + 3 ^ 40 * 152015 * 2
def baseEnd_152015 : Nat := 69383788171847088278579

theorem tailTrace_152015 : CollatzResearch.WordTrace tailWord_152015 prefixEnd_152015 69383788171847088278579 := by
  unfold tailWord_152015
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544442544283091940161499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3696295029522061293440999 5544442544283091940161499)
  ·
    refine ⟨8316663816424637910242249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544442544283091940161499 8316663816424637910242249)
    ·
      refine ⟨6237497862318478432681687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8316663816424637910242249 6237497862318478432681687)
      ·
        refine ⟨9356246793477717649022531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6237497862318478432681687 9356246793477717649022531)
        ·
          refine ⟨14034370190216576473533797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356246793477717649022531 14034370190216576473533797)
          ·
            refine ⟨2631444410665608088787587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14034370190216576473533797 2631444410665608088787587)
            ·
              refine ⟨3947166615998412133181381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631444410665608088787587 3947166615998412133181381)
              ·
                refine ⟨740093740499702274971509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3947166615998412133181381 740093740499702274971509)
                ·
                  refine ⟨69383788171847088278579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 740093740499702274971509 69383788171847088278579)
                  ·
                    rfl

theorem cell20_152015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_152015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152015 prefixEnd_152015 := by exact prefixLift 152015
  have htrace : WordTrace (prefixWord ++ tailWord_152015) baseStart_152015 baseEnd_152015 := by
    simpa [prefixWord, tailWord_152015, baseEnd_152015] using wordTrace_append hprefix tailTrace_152015
  have hstable : (prefixWord ++ tailWord_152015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152015).length < 2 ^ (prefixWord ++ tailWord_152015).sum := by decide
  have hdescent : baseEnd_152015 < baseStart_152015 := by decide
  rcases family_descends (prefixWord ++ tailWord_152015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152049 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 3]
def baseStart_152049 : Nat := 118140960795 + 152049 * 2 ^ 59
def prefixEnd_152049 : Nat := 4983230072969 + 3 ^ 40 * 152049 * 2
def baseEnd_152049 : Nat := 69399306698294081145107

theorem tailTrace_152049 : CollatzResearch.WordTrace tailWord_152049 prefixEnd_152049 69399306698294081145107 := by
  unfold tailWord_152049
  simp only [CollatzResearch.WordTrace]
  refine ⟨5545682626159915746899201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3697121750773277164599467 5545682626159915746899201)
  ·
    refine ⟨4159261969619936810174401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5545682626159915746899201 4159261969619936810174401)
    ·
      refine ⟨3119446477214952607630801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4159261969619936810174401 3119446477214952607630801)
      ·
        refine ⟨2339584857911214455723101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3119446477214952607630801 2339584857911214455723101)
        ·
          refine ⟨877344321716705420896163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2339584857911214455723101 877344321716705420896163)
          ·
            refine ⟨1316016482575058131344245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877344321716705420896163 1316016482575058131344245)
            ·
              refine ⟨123376545241411699813523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1316016482575058131344245 123376545241411699813523)
              ·
                refine ⟨185064817862117549720285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123376545241411699813523 185064817862117549720285)
                ·
                  refine ⟨69399306698294081145107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185064817862117549720285 69399306698294081145107)
                  ·
                    rfl

theorem cell20_152049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_152049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152049 prefixEnd_152049 := by exact prefixLift 152049
  have htrace : WordTrace (prefixWord ++ tailWord_152049) baseStart_152049 baseEnd_152049 := by
    simpa [prefixWord, tailWord_152049, baseEnd_152049] using wordTrace_append hprefix tailTrace_152049
  have hstable : (prefixWord ++ tailWord_152049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152049).length < 2 ^ (prefixWord ++ tailWord_152049).sum := by decide
  have hdescent : baseEnd_152049 < baseStart_152049 := by decide
  rcases family_descends (prefixWord ++ tailWord_152049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152100 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 3]
def baseStart_152100 : Nat := 118140960795 + 152100 * 2 ^ 59
def prefixEnd_152100 : Nat := 4983230072969 + 3 ^ 40 * 152100 * 2
def baseEnd_152100 : Nat := 69422584487964570444899

theorem tailTrace_152100 : CollatzResearch.WordTrace tailWord_152100 prefixEnd_152100 69422584487964570444899 := by
  unfold tailWord_152100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773771374487575728502877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3698361832650100971337169 2773771374487575728502877)
  ·
    refine ⟨1040164265432840898188579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2773771374487575728502877 1040164265432840898188579)
    ·
      refine ⟨1560246398149261347282869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1040164265432840898188579 1560246398149261347282869)
      ·
        refine ⟨146273099826493251307769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1560246398149261347282869 146273099826493251307769)
        ·
          refine ⟨109704824869869938480827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146273099826493251307769 109704824869869938480827)
          ·
            refine ⟨164557237304804907721241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109704824869869938480827 164557237304804907721241)
            ·
              refine ⟨123417927978603680790931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164557237304804907721241 123417927978603680790931)
              ·
                refine ⟨185126891967905521186397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123417927978603680790931 185126891967905521186397)
                ·
                  refine ⟨69422584487964570444899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185126891967905521186397 69422584487964570444899)
                  ·
                    rfl

theorem cell20_152100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_152100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152100 prefixEnd_152100 := by exact prefixLift 152100
  have htrace : WordTrace (prefixWord ++ tailWord_152100) baseStart_152100 baseEnd_152100 := by
    simpa [prefixWord, tailWord_152100, baseEnd_152100] using wordTrace_append hprefix tailTrace_152100
  have hstable : (prefixWord ++ tailWord_152100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152100).length < 2 ^ (prefixWord ++ tailWord_152100).sum := by decide
  have hdescent : baseEnd_152100 < baseStart_152100 := by decide
  rcases family_descends (prefixWord ++ tailWord_152100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152104 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_152104 : Nat := 118140960795 + 152104 * 2 ^ 59
def prefixEnd_152104 : Nat := 4983230072969 + 3 ^ 40 * 152104 * 2
def baseEnd_152104 : Nat := 69424410196958334311549

theorem tailTrace_152104 : CollatzResearch.WordTrace tailWord_152104 prefixEnd_152104 69424410196958334311549 := by
  unfold tailWord_152104
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773844320480330070075683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3698459093973773426767577 2773844320480330070075683)
  ·
    refine ⟨4160766480720495105113525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773844320480330070075683 4160766480720495105113525)
    ·
      refine ⟨390071857567546416104393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4160766480720495105113525 390071857567546416104393)
      ·
        refine ⟨292553893175659812078295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390071857567546416104393 292553893175659812078295)
        ·
          refine ⟨438830839763489718117443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292553893175659812078295 438830839763489718117443)
          ·
            refine ⟨658246259645234577176165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438830839763489718117443 658246259645234577176165)
            ·
              refine ⟨123421173683481483220531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 658246259645234577176165 123421173683481483220531)
              ·
                refine ⟨185131760525222224830797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123421173683481483220531 185131760525222224830797)
                ·
                  refine ⟨69424410196958334311549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185131760525222224830797 69424410196958334311549)
                  ·
                    rfl

theorem cell20_152104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_152104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152104 prefixEnd_152104 := by exact prefixLift 152104
  have htrace : WordTrace (prefixWord ++ tailWord_152104) baseStart_152104 baseEnd_152104 := by
    simpa [prefixWord, tailWord_152104, baseEnd_152104] using wordTrace_append hprefix tailTrace_152104
  have hstable : (prefixWord ++ tailWord_152104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152104).length < 2 ^ (prefixWord ++ tailWord_152104).sum := by decide
  have hdescent : baseEnd_152104 < baseStart_152104 := by decide
  rcases family_descends (prefixWord ++ tailWord_152104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152122 : List Nat := [3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_152122 : Nat := 118140960795 + 152122 * 2 ^ 59
def prefixEnd_152122 : Nat := 4983230072969 + 3 ^ 40 * 152122 * 2
def baseEnd_152122 : Nat := 23144208629143423903825

theorem tailTrace_152122 : CollatzResearch.WordTrace tailWord_152122 prefixEnd_152122 23144208629143423903825 := by
  unfold tailWord_152122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387086288723862303576655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3698896769930299476204413 1387086288723862303576655)
  ·
    refine ⟨2080629433085793455364983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1387086288723862303576655 2080629433085793455364983)
    ·
      refine ⟨3120944149628690183047475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2080629433085793455364983 3120944149628690183047475)
      ·
        refine ⟨4681416224443035274571213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120944149628690183047475 4681416224443035274571213)
        ·
          refine ⟨1755531084166138227964205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4681416224443035274571213 1755531084166138227964205)
          ·
            refine ⟨658324156562301835486577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1755531084166138227964205 658324156562301835486577)
            ·
              refine ⟨493743117421726376614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658324156562301835486577 493743117421726376614933)
              ·
                refine ⟨23144208629143423903825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 493743117421726376614933 23144208629143423903825)
                ·
                  rfl

theorem cell20_152122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_152122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152122 prefixEnd_152122 := by exact prefixLift 152122
  have htrace : WordTrace (prefixWord ++ tailWord_152122) baseStart_152122 baseEnd_152122 := by
    simpa [prefixWord, tailWord_152122, baseEnd_152122] using wordTrace_append hprefix tailTrace_152122
  have hstable : (prefixWord ++ tailWord_152122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152122).length < 2 ^ (prefixWord ++ tailWord_152122).sum := by decide
  have hdescent : baseEnd_152122 < baseStart_152122 := by decide
  rcases family_descends (prefixWord ++ tailWord_152122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152149 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 2]
def baseStart_152149 : Nat := 118140960795 + 152149 * 2 ^ 59
def prefixEnd_152149 : Nat := 4983230072969 + 3 ^ 40 * 152149 * 2
def baseEnd_152149 : Nat := 69444949423138177811365

theorem tailTrace_152149 : CollatzResearch.WordTrace tailWord_152149 prefixEnd_152149 69444949423138177811365 := by
  unfold tailWord_152149
  simp only [CollatzResearch.WordTrace]
  refine ⟨5549329925797632825539501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3699553283865088550359667 5549329925797632825539501)
  ·
    refine ⟨2080998722174112309577313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5549329925797632825539501 2080998722174112309577313)
    ·
      refine ⟨1560749041630584232182985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2080998722174112309577313 1560749041630584232182985)
      ·
        refine ⟨1170561781222938174137239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1560749041630584232182985 1170561781222938174137239)
        ·
          refine ⟨1755842671834407261205859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170561781222938174137239 1755842671834407261205859)
          ·
            refine ⟨2633764007751610891808789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755842671834407261205859 2633764007751610891808789)
            ·
              refine ⟨123457687863356760553537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2633764007751610891808789 123457687863356760553537)
              ·
                refine ⟨92593265897517570415153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123457687863356760553537 92593265897517570415153)
                ·
                  refine ⟨69444949423138177811365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92593265897517570415153 69444949423138177811365)
                  ·
                    rfl

theorem cell20_152149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_152149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152149 prefixEnd_152149 := by exact prefixLift 152149
  have htrace : WordTrace (prefixWord ++ tailWord_152149) baseStart_152149 baseEnd_152149 := by
    simpa [prefixWord, tailWord_152149, baseEnd_152149] using wordTrace_append hprefix tailTrace_152149
  have hstable : (prefixWord ++ tailWord_152149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152149).length < 2 ^ (prefixWord ++ tailWord_152149).sum := by decide
  have hdescent : baseEnd_152149 < baseStart_152149 := by decide
  rcases family_descends (prefixWord ++ tailWord_152149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152156 : List Nat := [2, 2, 4, 1, 3, 2, 1, 5]
def baseStart_152156 : Nat := 118140960795 + 152156 * 2 ^ 59
def prefixEnd_152156 : Nat := 4983230072969 + 3 ^ 40 * 152156 * 2
def baseEnd_152156 : Nat := 23149381471292421526001

theorem tailTrace_152156 : CollatzResearch.WordTrace tailWord_152156 prefixEnd_152156 23149381471292421526001 := by
  unfold tailWord_152156
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774792618386136510522161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3699723491181515347362881 2774792618386136510522161)
  ·
    refine ⟨2081094463789602382891621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2774792618386136510522161 2081094463789602382891621)
    ·
      refine ⟨390205211960550446792179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2081094463789602382891621 390205211960550446792179)
      ·
        refine ⟨585307817940825670188269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390205211960550446792179 585307817940825670188269)
        ·
          refine ⟨219490431727809626320601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 585307817940825670188269 219490431727809626320601)
          ·
            refine ⟨164617823795857219740451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219490431727809626320601 164617823795857219740451)
            ·
              refine ⟨246926735693785829610677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164617823795857219740451 246926735693785829610677)
              ·
                refine ⟨23149381471292421526001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246926735693785829610677 23149381471292421526001)
                ·
                  rfl

theorem cell20_152156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_152156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152156 prefixEnd_152156 := by exact prefixLift 152156
  have htrace : WordTrace (prefixWord ++ tailWord_152156) baseStart_152156 baseEnd_152156 := by
    simpa [prefixWord, tailWord_152156, baseEnd_152156] using wordTrace_append hprefix tailTrace_152156
  have hstable : (prefixWord ++ tailWord_152156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152156).length < 2 ^ (prefixWord ++ tailWord_152156).sum := by decide
  have hdescent : baseEnd_152156 < baseStart_152156 := by decide
  rcases family_descends (prefixWord ++ tailWord_152156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152160 : List Nat := [2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_152160 : Nat := 118140960795 + 152160 * 2 ^ 59
def prefixEnd_152160 : Nat := 4983230072969 + 3 ^ 40 * 152160 * 2
def baseEnd_152160 : Nat := 23149990040957009481551

theorem tailTrace_152160 : CollatzResearch.WordTrace tailWord_152160 prefixEnd_152160 23149990040957009481551 := by
  unfold tailWord_152160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774865564378890852094967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3699820752505187802793289 2774865564378890852094967)
  ·
    refine ⟨4162298346568336278142451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774865564378890852094967 4162298346568336278142451)
    ·
      refine ⟨6243447519852504417213677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4162298346568336278142451 6243447519852504417213677)
      ·
        refine ⟨2341292819944689156455129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6243447519852504417213677 2341292819944689156455129)
        ·
          refine ⟨1755969614958516867341347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2341292819944689156455129 1755969614958516867341347)
          ·
            refine ⟨2633954422437775301012021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755969614958516867341347 2633954422437775301012021)
            ·
              refine ⟨246933227103541434469877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2633954422437775301012021 246933227103541434469877)
              ·
                refine ⟨23149990040957009481551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246933227103541434469877 23149990040957009481551)
                ·
                  rfl

theorem cell20_152160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_152160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152160 prefixEnd_152160 := by exact prefixLift 152160
  have htrace : WordTrace (prefixWord ++ tailWord_152160) baseStart_152160 baseEnd_152160 := by
    simpa [prefixWord, tailWord_152160, baseEnd_152160] using wordTrace_append hprefix tailTrace_152160
  have hstable : (prefixWord ++ tailWord_152160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152160).length < 2 ^ (prefixWord ++ tailWord_152160).sum := by decide
  have hdescent : baseEnd_152160 < baseStart_152160 := by decide
  rcases family_descends (prefixWord ++ tailWord_152160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152167 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_152167 : Nat := 118140960795 + 152167 * 2 ^ 59
def prefixEnd_152167 : Nat := 4983230072969 + 3 ^ 40 * 152167 * 2
def baseEnd_152167 : Nat := 69453165113610115211291

theorem tailTrace_152167 : CollatzResearch.WordTrace tailWord_152167 prefixEnd_152167 69453165113610115211291 := by
  unfold tailWord_152167
  simp only [CollatzResearch.WordTrace]
  refine ⟨5549986439732421899694755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3699990959821614599796503 5549986439732421899694755)
  ·
    refine ⟨8324979659598632849542133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5549986439732421899694755 8324979659598632849542133)
    ·
      refine ⟨780466843087371829644575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8324979659598632849542133 780466843087371829644575)
      ·
        refine ⟨1170700264631057744466863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780466843087371829644575 1170700264631057744466863)
        ·
          refine ⟨1756050396946586616700295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170700264631057744466863 1756050396946586616700295)
          ·
            refine ⟨2634075595419879925050443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756050396946586616700295 2634075595419879925050443)
            ·
              refine ⟨3951113393129819887575665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634075595419879925050443 3951113393129819887575665)
              ·
                refine ⟨2963335044847364915681749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3951113393129819887575665 2963335044847364915681749)
                ·
                  refine ⟨69453165113610115211291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2963335044847364915681749 69453165113610115211291)
                  ·
                    rfl

theorem cell20_152167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_152167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152167 prefixEnd_152167 := by exact prefixLift 152167
  have htrace : WordTrace (prefixWord ++ tailWord_152167) baseStart_152167 baseEnd_152167 := by
    simpa [prefixWord, tailWord_152167, baseEnd_152167] using wordTrace_append hprefix tailTrace_152167
  have hstable : (prefixWord ++ tailWord_152167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152167).length < 2 ^ (prefixWord ++ tailWord_152167).sum := by decide
  have hdescent : baseEnd_152167 < baseStart_152167 := by decide
  rcases family_descends (prefixWord ++ tailWord_152167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152243 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_152243 : Nat := 118140960795 + 152243 * 2 ^ 59
def prefixEnd_152243 : Nat := 4983230072969 + 3 ^ 40 * 152243 * 2
def baseEnd_152243 : Nat := 69487853584491628677647

theorem tailTrace_152243 : CollatzResearch.WordTrace tailWord_152243 prefixEnd_152243 69487853584491628677647 := by
  unfold tailWord_152243
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552758387457086879461383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3701838924971391252974255 5552758387457086879461383)
  ·
    refine ⟨8329137581185630319192075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5552758387457086879461383 8329137581185630319192075)
    ·
      refine ⟨12493706371778445478788113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8329137581185630319192075 12493706371778445478788113)
      ·
        refine ⟨9370279778833834109091085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12493706371778445478788113 9370279778833834109091085)
        ·
          refine ⟨3513854917062687790909157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9370279778833834109091085 3513854917062687790909157)
          ·
            refine ⟨658847796949253960795467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3513854917062687790909157 658847796949253960795467)
            ·
              refine ⟨988271695423880941193201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658847796949253960795467 988271695423880941193201)
              ·
                refine ⟨741203771567910705894901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988271695423880941193201 741203771567910705894901)
                ·
                  refine ⟨69487853584491628677647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741203771567910705894901 69487853584491628677647)
                  ·
                    rfl

theorem cell20_152243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_152243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152243 prefixEnd_152243 := by exact prefixLift 152243
  have htrace : WordTrace (prefixWord ++ tailWord_152243) baseStart_152243 baseEnd_152243 := by
    simpa [prefixWord, tailWord_152243, baseEnd_152243] using wordTrace_append hprefix tailTrace_152243
  have hstable : (prefixWord ++ tailWord_152243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152243).length < 2 ^ (prefixWord ++ tailWord_152243).sum := by decide
  have hdescent : baseEnd_152243 < baseStart_152243 := by decide
  rcases family_descends (prefixWord ++ tailWord_152243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152260 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_152260 : Nat := 118140960795 + 152260 * 2 ^ 59
def prefixEnd_152260 : Nat := 4983230072969 + 3 ^ 40 * 152260 * 2
def baseEnd_152260 : Nat := 69495612847715125110911

theorem tailTrace_152260 : CollatzResearch.WordTrace tailWord_152260 prefixEnd_152260 69495612847715125110911 := by
  unfold tailWord_152260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776689214197749391415117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3702252285596999188553489 2776689214197749391415117)
  ·
    refine ⟨1041258455324156021780669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2776689214197749391415117 1041258455324156021780669)
    ·
      refine ⟨390471920746558508167751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1041258455324156021780669 390471920746558508167751)
      ·
        refine ⟨585707881119837762251627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390471920746558508167751 585707881119837762251627)
        ·
          refine ⟨878561821679756643377441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585707881119837762251627 878561821679756643377441)
          ·
            refine ⟨658921366259817482533081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878561821679756643377441 658921366259817482533081)
            ·
              refine ⟨494191024694863111899811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658921366259817482533081 494191024694863111899811)
              ·
                refine ⟨741286537042294667849717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494191024694863111899811 741286537042294667849717)
                ·
                  refine ⟨69495612847715125110911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741286537042294667849717 69495612847715125110911)
                  ·
                    rfl

theorem cell20_152260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_152260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152260 prefixEnd_152260 := by exact prefixLift 152260
  have htrace : WordTrace (prefixWord ++ tailWord_152260) baseStart_152260 baseEnd_152260 := by
    simpa [prefixWord, tailWord_152260, baseEnd_152260] using wordTrace_append hprefix tailTrace_152260
  have hstable : (prefixWord ++ tailWord_152260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152260).length < 2 ^ (prefixWord ++ tailWord_152260).sum := by decide
  have hdescent : baseEnd_152260 < baseStart_152260 := by decide
  rcases family_descends (prefixWord ++ tailWord_152260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152288 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_152288 : Nat := 118140960795 + 152288 * 2 ^ 59
def prefixEnd_152288 : Nat := 4983230072969 + 3 ^ 40 * 152288 * 2
def baseEnd_152288 : Nat := 69508392810671472177463

theorem tailTrace_152288 : CollatzResearch.WordTrace tailWord_152288 prefixEnd_152288 69508392810671472177463 := by
  unfold tailWord_152288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777199836147029782424759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3702933114862706376566345 2777199836147029782424759)
  ·
    refine ⟨4165799754220544673637139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777199836147029782424759 4165799754220544673637139)
    ·
      refine ⟨6248699631330817010455709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4165799754220544673637139 6248699631330817010455709)
      ·
        refine ⟨2343262361749056378920891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6248699631330817010455709 2343262361749056378920891)
        ·
          refine ⟨3514893542623584568381337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343262361749056378920891 3514893542623584568381337)
          ·
            refine ⟨2636170156967688426286003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3514893542623584568381337 2636170156967688426286003)
            ·
              refine ⟨3954255235451532639429005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636170156967688426286003 3954255235451532639429005)
              ·
                refine ⟨1482845713294324739785877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3954255235451532639429005 1482845713294324739785877)
                ·
                  refine ⟨69508392810671472177463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1482845713294324739785877 69508392810671472177463)
                  ·
                    rfl

theorem cell20_152288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_152288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152288 prefixEnd_152288 := by exact prefixLift 152288
  have htrace : WordTrace (prefixWord ++ tailWord_152288) baseStart_152288 baseEnd_152288 := by
    simpa [prefixWord, tailWord_152288, baseEnd_152288] using wordTrace_append hprefix tailTrace_152288
  have hstable : (prefixWord ++ tailWord_152288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152288).length < 2 ^ (prefixWord ++ tailWord_152288).sum := by decide
  have hdescent : baseEnd_152288 < baseStart_152288 := by decide
  rcases family_descends (prefixWord ++ tailWord_152288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152308 : List Nat := [2, 6, 1, 1, 2, 8]
def baseStart_152308 : Nat := 118140960795 + 152308 * 2 ^ 59
def prefixEnd_152308 : Nat := 4983230072969 + 3 ^ 40 * 152308 * 2
def baseEnd_152308 : Nat := 2574723013171862648545

theorem tailTrace_152308 : CollatzResearch.WordTrace tailWord_152308 prefixEnd_152308 2574723013171862648545 := by
  unfold tailWord_152308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777564566110801490288789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3703419421481068653718385 2777564566110801490288789)
  ·
    refine ⟨130198339036443819857287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2777564566110801490288789 130198339036443819857287)
    ·
      refine ⟨195297508554665729785931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130198339036443819857287 195297508554665729785931)
      ·
        refine ⟨292946262831998594678897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195297508554665729785931 292946262831998594678897)
        ·
          refine ⟨219709697123998946009173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292946262831998594678897 219709697123998946009173)
          ·
            refine ⟨2574723013171862648545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 219709697123998946009173 2574723013171862648545)
            ·
              rfl

theorem cell20_152308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 8].length) (baseStart_152308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152308 prefixEnd_152308 := by exact prefixLift 152308
  have htrace : WordTrace (prefixWord ++ tailWord_152308) baseStart_152308 baseEnd_152308 := by
    simpa [prefixWord, tailWord_152308, baseEnd_152308] using wordTrace_append hprefix tailTrace_152308
  have hstable : (prefixWord ++ tailWord_152308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152308).length < 2 ^ (prefixWord ++ tailWord_152308).sum := by decide
  have hdescent : baseEnd_152308 < baseStart_152308 := by decide
  rcases family_descends (prefixWord ++ tailWord_152308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152318 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_152318 : Nat := 118140960795 + 152318 * 2 ^ 59
def prefixEnd_152318 : Nat := 4983230072969 + 3 ^ 40 * 152318 * 2
def baseEnd_152318 : Nat := 69522085628124701177341

theorem tailTrace_152318 : CollatzResearch.WordTrace tailWord_152318 prefixEnd_152318 69522085628124701177341 := by
  unfold tailWord_152318
  simp only [CollatzResearch.WordTrace]
  refine ⟨694436732773171836055201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3703662574790249792294405 694436732773171836055201)
  ·
    refine ⟨520827549579878877041401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 694436732773171836055201 520827549579878877041401)
    ·
      refine ⟨390620662184909157781051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520827549579878877041401 390620662184909157781051)
      ·
        refine ⟨585930993277363736671577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390620662184909157781051 585930993277363736671577)
        ·
          refine ⟨439448244958022802503683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585930993277363736671577 439448244958022802503683)
          ·
            refine ⟨659172367437034203755525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439448244958022802503683 659172367437034203755525)
            ·
              refine ⟨123594818894443913204161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 659172367437034203755525 123594818894443913204161)
              ·
                refine ⟨92696114170832934903121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123594818894443913204161 92696114170832934903121)
                ·
                  refine ⟨69522085628124701177341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92696114170832934903121 69522085628124701177341)
                  ·
                    rfl

theorem cell20_152318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_152318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152318 prefixEnd_152318 := by exact prefixLift 152318
  have htrace : WordTrace (prefixWord ++ tailWord_152318) baseStart_152318 baseEnd_152318 := by
    simpa [prefixWord, tailWord_152318, baseEnd_152318] using wordTrace_append hprefix tailTrace_152318
  have hstable : (prefixWord ++ tailWord_152318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152318).length < 2 ^ (prefixWord ++ tailWord_152318).sum := by decide
  have hdescent : baseEnd_152318 < baseStart_152318 := by decide
  rcases family_descends (prefixWord ++ tailWord_152318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152357 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_152357 : Nat := 118140960795 + 152357 * 2 ^ 59
def prefixEnd_152357 : Nat := 4983230072969 + 3 ^ 40 * 152357 * 2
def baseEnd_152357 : Nat := 69539886290813898877181

theorem tailTrace_152357 : CollatzResearch.WordTrace tailWord_152357 prefixEnd_152357 69539886290813898877181 := by
  unfold tailWord_152357
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556916309044084349111325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3704610872696056232740883 5556916309044084349111325)
  ·
    refine ⟨2083843615891531630916747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5556916309044084349111325 2083843615891531630916747)
    ·
      refine ⟨3125765423837297446375121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083843615891531630916747 3125765423837297446375121)
      ·
        refine ⟨2344324067877973084781341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3125765423837297446375121 2344324067877973084781341)
        ·
          refine ⟨879121525454239906793003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2344324067877973084781341 879121525454239906793003)
          ·
            refine ⟨1318682288181359860189505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879121525454239906793003 1318682288181359860189505)
            ·
              refine ⟨989011716136019895142129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318682288181359860189505 989011716136019895142129)
              ·
                refine ⟨741758787102014921356597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989011716136019895142129 741758787102014921356597)
                ·
                  refine ⟨69539886290813898877181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741758787102014921356597 69539886290813898877181)
                  ·
                    rfl

theorem cell20_152357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_152357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152357 prefixEnd_152357 := by exact prefixLift 152357
  have htrace : WordTrace (prefixWord ++ tailWord_152357) baseStart_152357 baseEnd_152357 := by
    simpa [prefixWord, tailWord_152357, baseEnd_152357] using wordTrace_append hprefix tailTrace_152357
  have hstable : (prefixWord ++ tailWord_152357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152357).length < 2 ^ (prefixWord ++ tailWord_152357).sum := by decide
  have hdescent : baseEnd_152357 < baseStart_152357 := by decide
  rcases family_descends (prefixWord ++ tailWord_152357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152364 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_152364 : Nat := 118140960795 + 152364 * 2 ^ 59
def prefixEnd_152364 : Nat := 4983230072969 + 3 ^ 40 * 152364 * 2
def baseEnd_152364 : Nat := 69543081281552985643819

theorem tailTrace_152364 : CollatzResearch.WordTrace tailWord_152364 prefixEnd_152364 69543081281552985643819 := by
  unfold tailWord_152364
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778585810009362272308073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3704781080012483029744097 2778585810009362272308073)
  ·
    refine ⟨2083939357507021704231055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2778585810009362272308073 2083939357507021704231055)
    ·
      refine ⟨3125909036260532556346583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083939357507021704231055 3125909036260532556346583)
      ·
        refine ⟨4688863554390798834519875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125909036260532556346583 4688863554390798834519875)
        ·
          refine ⟨7033295331586198251779813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688863554390798834519875 7033295331586198251779813)
          ·
            refine ⟨1318742874672412172208715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7033295331586198251779813 1318742874672412172208715)
            ·
              refine ⟨1978114312008618258313073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318742874672412172208715 1978114312008618258313073)
              ·
                refine ⟨1483585734006463693734805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978114312008618258313073 1483585734006463693734805)
                ·
                  refine ⟨69543081281552985643819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1483585734006463693734805 69543081281552985643819)
                  ·
                    rfl

theorem cell20_152364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_152364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152364 prefixEnd_152364 := by exact prefixLift 152364
  have htrace : WordTrace (prefixWord ++ tailWord_152364) baseStart_152364 baseEnd_152364 := by
    simpa [prefixWord, tailWord_152364, baseEnd_152364] using wordTrace_append hprefix tailTrace_152364
  have hstable : (prefixWord ++ tailWord_152364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152364).length < 2 ^ (prefixWord ++ tailWord_152364).sum := by decide
  have hdescent : baseEnd_152364 < baseStart_152364 := by decide
  rcases family_descends (prefixWord ++ tailWord_152364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152412 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_152412 : Nat := 118140960795 + 152412 * 2 ^ 59
def prefixEnd_152412 : Nat := 4983230072969 + 3 ^ 40 * 152412 * 2
def baseEnd_152412 : Nat := 69564989789478152043623

theorem tailTrace_152412 : CollatzResearch.WordTrace tailWord_152412 prefixEnd_152412 69564989789478152043623 := by
  unfold tailWord_152412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779461161922414371181745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3705948215896552494908993 2779461161922414371181745)
  ·
    refine ⟨2084595871441810778386309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2779461161922414371181745 2084595871441810778386309)
    ·
      refine ⟨390861725895339520947433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2084595871441810778386309 390861725895339520947433)
      ·
        refine ⟨293146294421504640710575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390861725895339520947433 293146294421504640710575)
        ·
          refine ⟨439719441632256961065863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293146294421504640710575 439719441632256961065863)
          ·
            refine ⟨659579162448385441598795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439719441632256961065863 659579162448385441598795)
            ·
              refine ⟨989368743672578162398193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659579162448385441598795 989368743672578162398193)
              ·
                refine ⟨742026557754433621798645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989368743672578162398193 742026557754433621798645)
                ·
                  refine ⟨69564989789478152043623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742026557754433621798645 69564989789478152043623)
                  ·
                    rfl

theorem cell20_152412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_152412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152412 prefixEnd_152412 := by exact prefixLift 152412
  have htrace : WordTrace (prefixWord ++ tailWord_152412) baseStart_152412 baseEnd_152412 := by
    simpa [prefixWord, tailWord_152412, baseEnd_152412] using wordTrace_append hprefix tailTrace_152412
  have hstable : (prefixWord ++ tailWord_152412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152412).length < 2 ^ (prefixWord ++ tailWord_152412).sum := by decide
  have hdescent : baseEnd_152412 < baseStart_152412 := by decide
  rcases family_descends (prefixWord ++ tailWord_152412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152433 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_152433 : Nat := 118140960795 + 152433 * 2 ^ 59
def prefixEnd_152433 : Nat := 4983230072969 + 3 ^ 40 * 152433 * 2
def baseEnd_152433 : Nat := 69574574761695412343537

theorem tailTrace_152433 : CollatzResearch.WordTrace tailWord_152433 prefixEnd_152433 69574574761695412343537 := by
  unfold tailWord_152433
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559688256768749328877953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3706458837845832885918635 5559688256768749328877953)
  ·
    refine ⟨4169766192576561996658465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5559688256768749328877953 4169766192576561996658465)
    ·
      refine ⟨3127324644432421497493849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4169766192576561996658465 3127324644432421497493849)
      ·
        refine ⟨2345493483324316123120387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3127324644432421497493849 2345493483324316123120387)
        ·
          refine ⟨3518240224986474184680581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345493483324316123120387 3518240224986474184680581)
          ·
            refine ⟨659670042184963909627609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3518240224986474184680581 659670042184963909627609)
            ·
              refine ⟨494752531638722932220707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659670042184963909627609 494752531638722932220707)
              ·
                refine ⟨742128797458084398331061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494752531638722932220707 742128797458084398331061)
                ·
                  refine ⟨69574574761695412343537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742128797458084398331061 69574574761695412343537)
                  ·
                    rfl

theorem cell20_152433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_152433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152433 prefixEnd_152433 := by exact prefixLift 152433
  have htrace : WordTrace (prefixWord ++ tailWord_152433) baseStart_152433 baseEnd_152433 := by
    simpa [prefixWord, tailWord_152433, baseEnd_152433] using wordTrace_append hprefix tailTrace_152433
  have hstable : (prefixWord ++ tailWord_152433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152433).length < 2 ^ (prefixWord ++ tailWord_152433).sum := by decide
  have hdescent : baseEnd_152433 < baseStart_152433 := by decide
  rcases family_descends (prefixWord ++ tailWord_152433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152440 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_152440 : Nat := 118140960795 + 152440 * 2 ^ 59
def prefixEnd_152440 : Nat := 4983230072969 + 3 ^ 40 * 152440 * 2
def baseEnd_152440 : Nat := 69577769752434499110175

theorem tailTrace_152440 : CollatzResearch.WordTrace tailWord_152440 prefixEnd_152440 69577769752434499110175 := by
  unfold tailWord_152440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779971783871694762191387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3706629045162259682921849 2779971783871694762191387)
  ·
    refine ⟨4169957675807542143287081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2779971783871694762191387 4169957675807542143287081)
    ·
      refine ⟨3127468256855656607465311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4169957675807542143287081 3127468256855656607465311)
      ·
        refine ⟨4691202385283484911197967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127468256855656607465311 4691202385283484911197967)
        ·
          refine ⟨7036803577925227366796951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691202385283484911197967 7036803577925227366796951)
          ·
            refine ⟨10555205366887841050195427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036803577925227366796951 10555205366887841050195427)
            ·
              refine ⟨15832808050331761575293141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10555205366887841050195427 15832808050331761575293141)
              ·
                refine ⟨371081438679650661920933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15832808050331761575293141 371081438679650661920933)
                ·
                  refine ⟨69577769752434499110175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371081438679650661920933 69577769752434499110175)
                  ·
                    rfl

theorem cell20_152440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_152440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152440 prefixEnd_152440 := by exact prefixLift 152440
  have htrace : WordTrace (prefixWord ++ tailWord_152440) baseStart_152440 baseEnd_152440 := by
    simpa [prefixWord, tailWord_152440, baseEnd_152440] using wordTrace_append hprefix tailTrace_152440
  have hstable : (prefixWord ++ tailWord_152440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152440).length < 2 ^ (prefixWord ++ tailWord_152440).sum := by decide
  have hdescent : baseEnd_152440 < baseStart_152440 := by decide
  rcases family_descends (prefixWord ++ tailWord_152440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152446 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_152446 : Nat := 118140960795 + 152446 * 2 ^ 59
def prefixEnd_152446 : Nat := 4983230072969 + 3 ^ 40 * 152446 * 2
def baseEnd_152446 : Nat := 69580508315925144910151

theorem tailTrace_152446 : CollatzResearch.WordTrace tailWord_152446 prefixEnd_152446 69580508315925144910151 := by
  unfold tailWord_152446
  simp only [CollatzResearch.WordTrace]
  refine ⟨695020300715206568637649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3706774937147768366067461 695020300715206568637649)
  ·
    refine ⟨521265225536404926478237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 695020300715206568637649 521265225536404926478237)
    ·
      refine ⟨195474459576151847429339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 521265225536404926478237 195474459576151847429339)
      ·
        refine ⟨293211689364227771144009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195474459576151847429339 293211689364227771144009)
        ·
          refine ⟨219908767023170828358007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293211689364227771144009 219908767023170828358007)
          ·
            refine ⟨329863150534756242537011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219908767023170828358007 329863150534756242537011)
            ·
              refine ⟨494794725802134363805517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329863150534756242537011 494794725802134363805517)
              ·
                refine ⟨185548022175800386427069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494794725802134363805517 185548022175800386427069)
                ·
                  refine ⟨69580508315925144910151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185548022175800386427069 69580508315925144910151)
                  ·
                    rfl

theorem cell20_152446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_152446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152446 prefixEnd_152446 := by exact prefixLift 152446
  have htrace : WordTrace (prefixWord ++ tailWord_152446) baseStart_152446 baseEnd_152446 := by
    simpa [prefixWord, tailWord_152446, baseEnd_152446] using wordTrace_append hprefix tailTrace_152446
  have hstable : (prefixWord ++ tailWord_152446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152446).length < 2 ^ (prefixWord ++ tailWord_152446).sum := by decide
  have hdescent : baseEnd_152446 < baseStart_152446 := by decide
  rcases family_descends (prefixWord ++ tailWord_152446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152447 : List Nat := [1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_152447 : Nat := 118140960795 + 152447 * 2 ^ 59
def prefixEnd_152447 : Nat := 4983230072969 + 3 ^ 40 * 152447 * 2
def baseEnd_152447 : Nat := 23193654914391195292271

theorem tailTrace_152447 : CollatzResearch.WordTrace tailWord_152447 prefixEnd_152447 23193654914391195292271 := by
  unfold tailWord_152447
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560198878718029719887595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3706799252478686479925063 5560198878718029719887595)
  ·
    refine ⟨8340298318077044579831393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5560198878718029719887595 8340298318077044579831393)
    ·
      refine ⟨6255223738557783434873545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8340298318077044579831393 6255223738557783434873545)
      ·
        refine ⟨4691417803918337576155159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6255223738557783434873545 4691417803918337576155159)
        ·
          refine ⟨7037126705877506364232739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691417803918337576155159 7037126705877506364232739)
          ·
            refine ⟨10555690058816259546349109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7037126705877506364232739 10555690058816259546349109)
            ·
              refine ⟨989595943014024332470229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10555690058816259546349109 989595943014024332470229)
              ·
                refine ⟨23193654914391195292271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 989595943014024332470229 23193654914391195292271)
                ·
                  rfl

theorem cell20_152447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_152447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152447 prefixEnd_152447 := by exact prefixLift 152447
  have htrace : WordTrace (prefixWord ++ tailWord_152447) baseStart_152447 baseEnd_152447 := by
    simpa [prefixWord, tailWord_152447, baseEnd_152447] using wordTrace_append hprefix tailTrace_152447
  have hstable : (prefixWord ++ tailWord_152447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152447).length < 2 ^ (prefixWord ++ tailWord_152447).sum := by decide
  have hdescent : baseEnd_152447 < baseStart_152447 := by decide
  rcases family_descends (prefixWord ++ tailWord_152447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152487 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 2]
def baseStart_152487 : Nat := 118140960795 + 152487 * 2 ^ 59
def prefixEnd_152487 : Nat := 4983230072969 + 3 ^ 40 * 152487 * 2
def baseEnd_152487 : Nat := 69599221833111224543317

theorem tailTrace_152487 : CollatzResearch.WordTrace tailWord_152487 prefixEnd_152487 69599221833111224543317 := by
  unfold tailWord_152487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5561657798573116551343715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3707771865715411034229143 5561657798573116551343715)
  ·
    refine ⟨8342486697859674827015573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5561657798573116551343715 8342486697859674827015573)
    ·
      refine ⟨391054063962172257516355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8342486697859674827015573 391054063962172257516355)
      ·
        refine ⟨586581095943258386274533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391054063962172257516355 586581095943258386274533)
        ·
          refine ⟨109983955489360947426475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 586581095943258386274533 109983955489360947426475)
          ·
            refine ⟨164975933234041421139713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109983955489360947426475 164975933234041421139713)
            ·
              refine ⟨123731949925531065854785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164975933234041421139713 123731949925531065854785)
              ·
                refine ⟨92798962444148299391089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123731949925531065854785 92798962444148299391089)
                ·
                  refine ⟨69599221833111224543317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92798962444148299391089 69599221833111224543317)
                  ·
                    rfl

theorem cell20_152487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 2].length) (baseStart_152487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152487 prefixEnd_152487 := by exact prefixLift 152487
  have htrace : WordTrace (prefixWord ++ tailWord_152487) baseStart_152487 baseEnd_152487 := by
    simpa [prefixWord, tailWord_152487, baseEnd_152487] using wordTrace_append hprefix tailTrace_152487
  have hstable : (prefixWord ++ tailWord_152487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152487).length < 2 ^ (prefixWord ++ tailWord_152487).sum := by decide
  have hdescent : baseEnd_152487 < baseStart_152487 := by decide
  rcases family_descends (prefixWord ++ tailWord_152487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152543 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 3]
def baseStart_152543 : Nat := 118140960795 + 152543 * 2 ^ 59
def prefixEnd_152543 : Nat := 4983230072969 + 3 ^ 40 * 152543 * 2
def baseEnd_152543 : Nat := 69624781759023918676421

theorem tailTrace_152543 : CollatzResearch.WordTrace tailWord_152543 prefixEnd_152543 69624781759023918676421 := by
  unfold tailWord_152543
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563700286370238115382283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3709133524246825410254855 5563700286370238115382283)
  ·
    refine ⟨8345550429555357173073425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5563700286370238115382283 8345550429555357173073425)
    ·
      refine ⟨6259162822166517879805069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8345550429555357173073425 6259162822166517879805069)
      ·
        refine ⟨2347186058312444204926901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6259162822166517879805069 2347186058312444204926901)
        ·
          refine ⟨220048692966791644211897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2347186058312444204926901 220048692966791644211897)
          ·
            refine ⟨165036519725093733158923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220048692966791644211897 165036519725093733158923)
            ·
              refine ⟨247554779587640599738385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165036519725093733158923 247554779587640599738385)
              ·
                refine ⟨185666084690730449803789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247554779587640599738385 185666084690730449803789)
                ·
                  refine ⟨69624781759023918676421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185666084690730449803789 69624781759023918676421)
                  ·
                    rfl

theorem cell20_152543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_152543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152543 prefixEnd_152543 := by exact prefixLift 152543
  have htrace : WordTrace (prefixWord ++ tailWord_152543) baseStart_152543 baseEnd_152543 := by
    simpa [prefixWord, tailWord_152543, baseEnd_152543] using wordTrace_append hprefix tailTrace_152543
  have hstable : (prefixWord ++ tailWord_152543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152543).length < 2 ^ (prefixWord ++ tailWord_152543).sum := by decide
  have hdescent : baseEnd_152543 < baseStart_152543 := by decide
  rcases family_descends (prefixWord ++ tailWord_152543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152547 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_152547 : Nat := 118140960795 + 152547 * 2 ^ 59
def prefixEnd_152547 : Nat := 4983230072969 + 3 ^ 40 * 152547 * 2
def baseEnd_152547 : Nat := 69626607468017682543071

theorem tailTrace_152547 : CollatzResearch.WordTrace tailWord_152547 prefixEnd_152547 69626607468017682543071 := by
  unfold tailWord_152547
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563846178355746798527895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3709230785570497865685263 5563846178355746798527895)
  ·
    refine ⟨8345769267533620197791843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5563846178355746798527895 8345769267533620197791843)
    ·
      refine ⟨12518653901300430296687765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8345769267533620197791843 12518653901300430296687765)
      ·
        refine ⟨586811901623457670157239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12518653901300430296687765 586811901623457670157239)
        ·
          refine ⟨880217852435186505235859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586811901623457670157239 880217852435186505235859)
          ·
            refine ⟨1320326778652779757853789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880217852435186505235859 1320326778652779757853789)
            ·
              refine ⟨495122541994792409195171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1320326778652779757853789 495122541994792409195171)
              ·
                refine ⟨742683812992188613792757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495122541994792409195171 742683812992188613792757)
                ·
                  refine ⟨69626607468017682543071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742683812992188613792757 69626607468017682543071)
                  ·
                    rfl

theorem cell20_152547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_152547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152547 prefixEnd_152547 := by exact prefixLift 152547
  have htrace : WordTrace (prefixWord ++ tailWord_152547) baseStart_152547 baseEnd_152547 := by
    simpa [prefixWord, tailWord_152547, baseEnd_152547] using wordTrace_append hprefix tailTrace_152547
  have hstable : (prefixWord ++ tailWord_152547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152547).length < 2 ^ (prefixWord ++ tailWord_152547).sum := by decide
  have hdescent : baseEnd_152547 < baseStart_152547 := by decide
  rcases family_descends (prefixWord ++ tailWord_152547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152588 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 2]
def baseStart_152588 : Nat := 118140960795 + 152588 * 2 ^ 59
def prefixEnd_152588 : Nat := 4983230072969 + 3 ^ 40 * 152588 * 2
def baseEnd_152588 : Nat := 69645320985203762176237

theorem tailTrace_152588 : CollatzResearch.WordTrace tailWord_152588 prefixEnd_152588 69645320985203762176237 := by
  unfold tailWord_152588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782670785603605400385209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3710227714138140533846945 2782670785603605400385209)
  ·
    refine ⟨2087003089202704050288907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2782670785603605400385209 2087003089202704050288907)
    ·
      refine ⟨3130504633804056075433361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087003089202704050288907 3130504633804056075433361)
      ·
        refine ⟨2347878475353042056575021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3130504633804056075433361 2347878475353042056575021)
        ·
          refine ⟨880454428257390771215633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2347878475353042056575021 880454428257390771215633)
          ·
            refine ⟨660340821193043078411725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880454428257390771215633 660340821193043078411725)
            ·
              refine ⟨247627807947391154404397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660340821193043078411725 247627807947391154404397)
              ·
                refine ⟨92860427980271682901649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247627807947391154404397 92860427980271682901649)
                ·
                  refine ⟨69645320985203762176237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92860427980271682901649 69645320985203762176237)
                  ·
                    rfl

theorem cell20_152588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_152588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152588 prefixEnd_152588 := by exact prefixLift 152588
  have htrace : WordTrace (prefixWord ++ tailWord_152588) baseStart_152588 baseEnd_152588 := by
    simpa [prefixWord, tailWord_152588, baseEnd_152588] using wordTrace_append hprefix tailTrace_152588
  have hstable : (prefixWord ++ tailWord_152588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152588).length < 2 ^ (prefixWord ++ tailWord_152588).sum := by decide
  have hdescent : baseEnd_152588 < baseStart_152588 := by decide
  rcases family_descends (prefixWord ++ tailWord_152588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152605 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 4]
def baseStart_152605 : Nat := 118140960795 + 152605 * 2 ^ 59
def prefixEnd_152605 : Nat := 4983230072969 + 3 ^ 40 * 152605 * 2
def baseEnd_152605 : Nat := 69653080248427258609501

theorem tailTrace_152605 : CollatzResearch.WordTrace tailWord_152605 prefixEnd_152605 69653080248427258609501 := by
  unfold tailWord_152605
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565961612145622704139269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3710641074763748469426179 5565961612145622704139269)
  ·
    refine ⟨1043617802277304257026113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5565961612145622704139269 1043617802277304257026113)
    ·
      refine ⟨782713351707978192769585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1043617802277304257026113 782713351707978192769585)
      ·
        refine ⟨587035013780983644577189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782713351707978192769585 587035013780983644577189)
        ·
          refine ⟨110069065083934433358223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 587035013780983644577189 110069065083934433358223)
          ·
            refine ⟨165103597625901650037335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110069065083934433358223 165103597625901650037335)
            ·
              refine ⟨247655396438852475056003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165103597625901650037335 247655396438852475056003)
              ·
                refine ⟨371483094658278712584005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247655396438852475056003 371483094658278712584005)
                ·
                  refine ⟨69653080248427258609501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371483094658278712584005 69653080248427258609501)
                  ·
                    rfl

theorem cell20_152605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_152605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152605 prefixEnd_152605 := by exact prefixLift 152605
  have htrace : WordTrace (prefixWord ++ tailWord_152605) baseStart_152605 baseEnd_152605 := by
    simpa [prefixWord, tailWord_152605, baseEnd_152605] using wordTrace_append hprefix tailTrace_152605
  have hstable : (prefixWord ++ tailWord_152605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152605).length < 2 ^ (prefixWord ++ tailWord_152605).sum := by decide
  have hdescent : baseEnd_152605 < baseStart_152605 := by decide
  rcases family_descends (prefixWord ++ tailWord_152605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152609 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_152609 : Nat := 118140960795 + 152609 * 2 ^ 59
def prefixEnd_152609 : Nat := 4983230072969 + 3 ^ 40 * 152609 * 2
def baseEnd_152609 : Nat := 69654905957421022476151

theorem tailTrace_152609 : CollatzResearch.WordTrace tailWord_152609 prefixEnd_152609 69654905957421022476151 := by
  unfold tailWord_152609
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566107504131131387284881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3710738336087420924856587 5566107504131131387284881)
  ·
    refine ⟨4174580628098348540463661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5566107504131131387284881 4174580628098348540463661)
    ·
      refine ⟨1565467735536880702673873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4174580628098348540463661 1565467735536880702673873)
      ·
        refine ⟨1174100801652660527005405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1565467735536880702673873 1174100801652660527005405)
        ·
          refine ⟨440287800619747697627027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1174100801652660527005405 440287800619747697627027)
          ·
            refine ⟨660431700929621546440541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440287800619747697627027 660431700929621546440541)
            ·
              refine ⟨247661887848608079915203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660431700929621546440541 247661887848608079915203)
              ·
                refine ⟨371492831772912119872805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247661887848608079915203 371492831772912119872805)
                ·
                  refine ⟨69654905957421022476151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371492831772912119872805 69654905957421022476151)
                  ·
                    rfl

theorem cell20_152609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_152609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152609 prefixEnd_152609 := by exact prefixLift 152609
  have htrace : WordTrace (prefixWord ++ tailWord_152609) baseStart_152609 baseEnd_152609 := by
    simpa [prefixWord, tailWord_152609, baseEnd_152609] using wordTrace_append hprefix tailTrace_152609
  have hstable : (prefixWord ++ tailWord_152609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152609).length < 2 ^ (prefixWord ++ tailWord_152609).sum := by decide
  have hdescent : baseEnd_152609 < baseStart_152609 := by decide
  rcases family_descends (prefixWord ++ tailWord_152609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152685 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_152685 : Nat := 118140960795 + 152685 * 2 ^ 59
def prefixEnd_152685 : Nat := 4983230072969 + 3 ^ 40 * 152685 * 2
def baseEnd_152685 : Nat := 69689594428302535942507

theorem tailTrace_152685 : CollatzResearch.WordTrace tailWord_152685 prefixEnd_152685 69689594428302535942507 := by
  unfold tailWord_152685
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568879451855796367051509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3712586301237197578034339 5568879451855796367051509)
  ·
    refine ⟨522082448611480909411079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5568879451855796367051509 522082448611480909411079)
    ·
      refine ⟨783123672917221364116619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522082448611480909411079 783123672917221364116619)
      ·
        refine ⟨1174685509375832046174929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783123672917221364116619 1174685509375832046174929)
        ·
          refine ⟨881014132031874034631197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1174685509375832046174929 881014132031874034631197)
          ·
            refine ⟨330380299511952762986699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 881014132031874034631197 330380299511952762986699)
            ·
              refine ⟨495570449267929144480049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330380299511952762986699 495570449267929144480049)
              ·
                refine ⟨371677836950946858360037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495570449267929144480049 371677836950946858360037)
                ·
                  refine ⟨69689594428302535942507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371677836950946858360037 69689594428302535942507)
                  ·
                    rfl

theorem cell20_152685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_152685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152685 prefixEnd_152685 := by exact prefixLift 152685
  have htrace : WordTrace (prefixWord ++ tailWord_152685) baseStart_152685 baseEnd_152685 := by
    simpa [prefixWord, tailWord_152685, baseEnd_152685] using wordTrace_append hprefix tailTrace_152685
  have hstable : (prefixWord ++ tailWord_152685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152685).length < 2 ^ (prefixWord ++ tailWord_152685).sum := by decide
  have hdescent : baseEnd_152685 < baseStart_152685 := by decide
  rcases family_descends (prefixWord ++ tailWord_152685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152712 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 3]
def baseStart_152712 : Nat := 118140960795 + 152712 * 2 ^ 59
def prefixEnd_152712 : Nat := 4983230072969 + 3 ^ 40 * 152712 * 2
def baseEnd_152712 : Nat := 69701917964010442042397

theorem tailTrace_152712 : CollatzResearch.WordTrace tailWord_152712 prefixEnd_152712 69701917964010442042397 := by
  unfold tailWord_152712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784932111378989989142195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3713242815171986652189593 2784932111378989989142195)
  ·
    refine ⟨4177398167068484983713293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2784932111378989989142195 4177398167068484983713293)
    ·
      refine ⟨1566524312650681868892485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4177398167068484983713293 1566524312650681868892485)
      ·
        refine ⟨293723308622002850417341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1566524312650681868892485 293723308622002850417341)
        ·
          refine ⟨110146240733251068906503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293723308622002850417341 110146240733251068906503)
          ·
            refine ⟨165219361099876603359755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110146240733251068906503 165219361099876603359755)
            ·
              refine ⟨247829041649814905039633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165219361099876603359755 247829041649814905039633)
              ·
                refine ⟨185871781237361178779725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247829041649814905039633 185871781237361178779725)
                ·
                  refine ⟨69701917964010442042397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185871781237361178779725 69701917964010442042397)
                  ·
                    rfl

theorem cell20_152712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_152712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152712 prefixEnd_152712 := by exact prefixLift 152712
  have htrace : WordTrace (prefixWord ++ tailWord_152712) baseStart_152712 baseEnd_152712 := by
    simpa [prefixWord, tailWord_152712, baseEnd_152712] using wordTrace_append hprefix tailTrace_152712
  have hstable : (prefixWord ++ tailWord_152712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152712).length < 2 ^ (prefixWord ++ tailWord_152712).sum := by decide
  have hdescent : baseEnd_152712 < baseStart_152712 := by decide
  rcases family_descends (prefixWord ++ tailWord_152712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152713 : List Nat := [1, 2, 1, 1, 4, 4, 7]
def baseStart_152713 : Nat := 118140960795 + 152713 * 2 ^ 59
def prefixEnd_152713 : Nat := 4983230072969 + 3 ^ 40 * 152713 * 2
def baseEnd_152713 : Nat := 7744708265695431445451

theorem tailTrace_152713 : CollatzResearch.WordTrace tailWord_152713 prefixEnd_152713 7744708265695431445451 := by
  unfold tailWord_152713
  simp only [CollatzResearch.WordTrace]
  refine ⟨5569900695754357149070793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3713267130502904766047195 5569900695754357149070793)
  ·
    refine ⟨4177425521815767861803095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5569900695754357149070793 4177425521815767861803095)
    ·
      refine ⟨6266138282723651792704643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4177425521815767861803095 6266138282723651792704643)
      ·
        refine ⟨9399207424085477689056965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266138282723651792704643 9399207424085477689056965)
        ·
          refine ⟨1762351392016027066698181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9399207424085477689056965 1762351392016027066698181)
          ·
            refine ⟨330440886003005075005909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1762351392016027066698181 330440886003005075005909)
            ·
              refine ⟨7744708265695431445451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 330440886003005075005909 7744708265695431445451)
              ·
                rfl

theorem cell20_152713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_152713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152713 prefixEnd_152713 := by exact prefixLift 152713
  have htrace : WordTrace (prefixWord ++ tailWord_152713) baseStart_152713 baseEnd_152713 := by
    simpa [prefixWord, tailWord_152713, baseEnd_152713] using wordTrace_append hprefix tailTrace_152713
  have hstable : (prefixWord ++ tailWord_152713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152713).length < 2 ^ (prefixWord ++ tailWord_152713).sum := by decide
  have hdescent : baseEnd_152713 < baseStart_152713 := by decide
  rcases family_descends (prefixWord ++ tailWord_152713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152723 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 2]
def baseStart_152723 : Nat := 118140960795 + 152723 * 2 ^ 59
def prefixEnd_152723 : Nat := 4983230072969 + 3 ^ 40 * 152723 * 2
def baseEnd_152723 : Nat := 69706938663743292675685

theorem tailTrace_152723 : CollatzResearch.WordTrace tailWord_152723 prefixEnd_152723 69706938663743292675685 := by
  unfold tailWord_152723
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570265425718128856934823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3713510283812085904623215 5570265425718128856934823)
  ·
    refine ⟨8355398138577193285402235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5570265425718128856934823 8355398138577193285402235)
    ·
      refine ⟨12533097207865789928103353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8355398138577193285402235 12533097207865789928103353)
      ·
        refine ⟨9399822905899342446077515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12533097207865789928103353 9399822905899342446077515)
        ·
          refine ⟨14099734358849013669116273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9399822905899342446077515 14099734358849013669116273)
          ·
            refine ⟨10574800769136760251837205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14099734358849013669116273 10574800769136760251837205)
            ·
              refine ⟨495693786053285636804869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10574800769136760251837205 495693786053285636804869)
              ·
                refine ⟨92942584884991056900913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495693786053285636804869 92942584884991056900913)
                ·
                  refine ⟨69706938663743292675685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92942584884991056900913 69706938663743292675685)
                  ·
                    rfl

theorem cell20_152723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 2].length) (baseStart_152723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152723 prefixEnd_152723 := by exact prefixLift 152723
  have htrace : WordTrace (prefixWord ++ tailWord_152723) baseStart_152723 baseEnd_152723 := by
    simpa [prefixWord, tailWord_152723, baseEnd_152723] using wordTrace_append hprefix tailTrace_152723
  have hstable : (prefixWord ++ tailWord_152723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152723).length < 2 ^ (prefixWord ++ tailWord_152723).sum := by decide
  have hdescent : baseEnd_152723 < baseStart_152723 := by decide
  rcases family_descends (prefixWord ++ tailWord_152723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152768 : List Nat := [2, 1, 1, 2, 6, 2, 6]
def baseStart_152768 : Nat := 118140960795 + 152768 * 2 ^ 59
def prefixEnd_152768 : Nat := 4983230072969 + 3 ^ 40 * 152768 * 2
def baseEnd_152768 : Nat := 7747497543324792908389

theorem tailTrace_152768 : CollatzResearch.WordTrace tailWord_152768 prefixEnd_152768 7747497543324792908389 := by
  unfold tailWord_152768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785953355277550771161479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3714604473703401028215305 2785953355277550771161479)
  ·
    refine ⟨4178930032916326156742219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2785953355277550771161479 4178930032916326156742219)
    ·
      refine ⟨6268395049374489235113329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178930032916326156742219 6268395049374489235113329)
      ·
        refine ⟨4701296287030866926334997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268395049374489235113329 4701296287030866926334997)
        ·
          refine ⟨220373263454571887171953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4701296287030866926334997 220373263454571887171953)
          ·
            refine ⟨165279947590928915378965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220373263454571887171953 165279947590928915378965)
            ·
              refine ⟨7747497543324792908389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165279947590928915378965 7747497543324792908389)
              ·
                rfl

theorem cell20_152768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 6].length) (baseStart_152768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152768 prefixEnd_152768 := by exact prefixLift 152768
  have htrace : WordTrace (prefixWord ++ tailWord_152768) baseStart_152768 baseEnd_152768 := by
    simpa [prefixWord, tailWord_152768, baseEnd_152768] using wordTrace_append hprefix tailTrace_152768
  have hstable : (prefixWord ++ tailWord_152768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152768).length < 2 ^ (prefixWord ++ tailWord_152768).sum := by decide
  have hdescent : baseEnd_152768 < baseStart_152768 := by decide
  rcases family_descends (prefixWord ++ tailWord_152768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152792 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_152792 : Nat := 118140960795 + 152792 * 2 ^ 59
def prefixEnd_152792 : Nat := 4983230072969 + 3 ^ 40 * 152792 * 2
def baseEnd_152792 : Nat := 69738432143885719375403

theorem tailTrace_152792 : CollatzResearch.WordTrace tailWord_152792 prefixEnd_152792 69738432143885719375403 := by
  unfold tailWord_152792
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786391031234076820598315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3715188041645435760797753 2786391031234076820598315)
  ·
    refine ⟨4179586546851115230897473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2786391031234076820598315 4179586546851115230897473)
    ·
      refine ⟨3134689910138336423173105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4179586546851115230897473 3134689910138336423173105)
      ·
        refine ⟨2351017432603752317379829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3134689910138336423173105 2351017432603752317379829)
        ·
          refine ⟨220407884306601779754359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2351017432603752317379829 220407884306601779754359)
          ·
            refine ⟨330611826459902669631539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220407884306601779754359 330611826459902669631539)
            ·
              refine ⟨495917739689854004447309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330611826459902669631539 495917739689854004447309)
              ·
                refine ⟨185969152383695251667741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495917739689854004447309 185969152383695251667741)
                ·
                  refine ⟨69738432143885719375403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185969152383695251667741 69738432143885719375403)
                  ·
                    rfl

theorem cell20_152792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_152792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152792 prefixEnd_152792 := by exact prefixLift 152792
  have htrace : WordTrace (prefixWord ++ tailWord_152792) baseStart_152792 baseEnd_152792 := by
    simpa [prefixWord, tailWord_152792, baseEnd_152792] using wordTrace_append hprefix tailTrace_152792
  have hstable : (prefixWord ++ tailWord_152792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152792).length < 2 ^ (prefixWord ++ tailWord_152792).sum := by decide
  have hdescent : baseEnd_152792 < baseStart_152792 := by decide
  rcases family_descends (prefixWord ++ tailWord_152792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152830 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_152830 : Nat := 118140960795 + 152830 * 2 ^ 59
def prefixEnd_152830 : Nat := 4983230072969 + 3 ^ 40 * 152830 * 2
def baseEnd_152830 : Nat := 69755776379326476108581

theorem tailTrace_152830 : CollatzResearch.WordTrace tailWord_152830 prefixEnd_152830 69755776379326476108581 := by
  unfold tailWord_152830
  simp only [CollatzResearch.WordTrace]
  refine ⟨696771004541310766384993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3716112024220324087386629 696771004541310766384993)
  ·
    refine ⟨522578253405983074788745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 696771004541310766384993 522578253405983074788745)
    ·
      refine ⟨391933690054487306091559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 522578253405983074788745 391933690054487306091559)
      ·
        refine ⟨587900535081730959137339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391933690054487306091559 587900535081730959137339)
        ·
          refine ⟨881850802622596438706009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587900535081730959137339 881850802622596438706009)
          ·
            refine ⟨661388101966947329029507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881850802622596438706009 661388101966947329029507)
            ·
              refine ⟨992082152950420993544261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661388101966947329029507 992082152950420993544261)
              ·
                refine ⟨186015403678203936289549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 992082152950420993544261 186015403678203936289549)
                ·
                  refine ⟨69755776379326476108581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186015403678203936289549 69755776379326476108581)
                  ·
                    rfl

theorem cell20_152830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_152830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152830 prefixEnd_152830 := by exact prefixLift 152830
  have htrace : WordTrace (prefixWord ++ tailWord_152830) baseStart_152830 baseEnd_152830 := by
    simpa [prefixWord, tailWord_152830, baseEnd_152830] using wordTrace_append hprefix tailTrace_152830
  have hstable : (prefixWord ++ tailWord_152830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152830).length < 2 ^ (prefixWord ++ tailWord_152830).sum := by decide
  have hdescent : baseEnd_152830 < baseStart_152830 := by decide
  rcases family_descends (prefixWord ++ tailWord_152830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
