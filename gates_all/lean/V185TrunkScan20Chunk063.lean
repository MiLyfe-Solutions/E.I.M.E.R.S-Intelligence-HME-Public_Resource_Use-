import V185TrunkScan20Chunk062

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_384156 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 2]
def baseStart_384156 : Nat := 118140960795 + 384156 * 2 ^ 59
def prefixEnd_384156 : Nat := 4983230072969 + 3 ^ 40 * 384156 * 2
def baseEnd_384156 : Nat := 175339266052181530296271

theorem tailTrace_384156 : CollatzResearch.WordTrace tailWord_384156 prefixEnd_384156 175339266052181530296271 := by
  unfold tailWord_384156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7005660198137947733270161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9340880264183930311026881 7005660198137947733270161)
  ·
    refine ⟨5254245148603460799952621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7005660198137947733270161 5254245148603460799952621)
    ·
      refine ⟨1970341930726297799982233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5254245148603460799952621 1970341930726297799982233)
      ·
        refine ⟨1477756448044723349986675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1970341930726297799982233 1477756448044723349986675)
        ·
          refine ⟨2216634672067085024980013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477756448044723349986675 2216634672067085024980013)
          ·
            refine ⟨831238002025156884367505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2216634672067085024980013 831238002025156884367505)
            ·
              refine ⟨623428501518867663275629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831238002025156884367505 623428501518867663275629)
              ·
                refine ⟨233785688069575373728361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623428501518867663275629 233785688069575373728361)
                ·
                  refine ⟨175339266052181530296271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233785688069575373728361 175339266052181530296271)
                  ·
                    rfl

theorem cell20_384156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_384156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384156 prefixEnd_384156 := by exact prefixLift 384156
  have htrace : WordTrace (prefixWord ++ tailWord_384156) baseStart_384156 baseEnd_384156 := by
    simpa [prefixWord, tailWord_384156, baseEnd_384156] using wordTrace_append hprefix tailTrace_384156
  have hstable : (prefixWord ++ tailWord_384156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384156).length < 2 ^ (prefixWord ++ tailWord_384156).sum := by decide
  have hdescent : baseEnd_384156 < baseStart_384156 := by decide
  rcases family_descends (prefixWord ++ tailWord_384156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384170 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_384170 : Nat := 118140960795 + 384170 * 2 ^ 59
def prefixEnd_384170 : Nat := 4983230072969 + 3 ^ 40 * 384170 * 2
def baseEnd_384170 : Nat := 175345656033659703829547

theorem tailTrace_384170 : CollatzResearch.WordTrace tailWord_384170 prefixEnd_384170 175345656033659703829547 := by
  unfold tailWord_384170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502957754556293964387491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9341220678816783905033309 3502957754556293964387491)
  ·
    refine ⟨5254436631834440946581237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3502957754556293964387491 5254436631834440946581237)
    ·
      refine ⟨492603434234478838741991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5254436631834440946581237 492603434234478838741991)
      ·
        refine ⟨738905151351718258112987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492603434234478838741991 738905151351718258112987)
        ·
          refine ⟨1108357727027577387169481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738905151351718258112987 1108357727027577387169481)
          ·
            refine ⟨831268295270683040377111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108357727027577387169481 831268295270683040377111)
            ·
              refine ⟨1246902442906024560565667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831268295270683040377111 1246902442906024560565667)
              ·
                refine ⟨1870353664359036840848501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246902442906024560565667 1870353664359036840848501)
                ·
                  refine ⟨175345656033659703829547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1870353664359036840848501 175345656033659703829547)
                  ·
                    rfl

theorem cell20_384170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_384170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384170 prefixEnd_384170 := by exact prefixLift 384170
  have htrace : WordTrace (prefixWord ++ tailWord_384170) baseStart_384170 baseEnd_384170 := by
    simpa [prefixWord, tailWord_384170, baseEnd_384170] using wordTrace_append hprefix tailTrace_384170
  have hstable : (prefixWord ++ tailWord_384170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384170).length < 2 ^ (prefixWord ++ tailWord_384170).sum := by decide
  have hdescent : baseEnd_384170 < baseStart_384170 := by decide
  rcases family_descends (prefixWord ++ tailWord_384170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384177 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_384177 : Nat := 118140960795 + 384177 * 2 ^ 59
def prefixEnd_384177 : Nat := 4983230072969 + 3 ^ 40 * 384177 * 2
def baseEnd_384177 : Nat := 175348851024398790596185

theorem tailTrace_384177 : CollatzResearch.WordTrace tailWord_384177 prefixEnd_384177 175348851024398790596185 := by
  unfold tailWord_384177
  simp only [CollatzResearch.WordTrace]
  refine ⟨14012086329199816053054785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9341390886133210702036523 14012086329199816053054785)
  ·
    refine ⟨10509064746899862039791089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14012086329199816053054785 10509064746899862039791089)
    ·
      refine ⟨7881798560174896529843317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10509064746899862039791089 7881798560174896529843317)
      ·
        refine ⟨738918615016396549672811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7881798560174896529843317 738918615016396549672811)
        ·
          refine ⟨1108377922524594824509217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738918615016396549672811 1108377922524594824509217)
          ·
            refine ⟨831283441893446118381913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108377922524594824509217 831283441893446118381913)
            ·
              refine ⟨623462581420084588786435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831283441893446118381913 623462581420084588786435)
              ·
                refine ⟨935193872130126883179653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623462581420084588786435 935193872130126883179653)
                ·
                  refine ⟨175348851024398790596185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 935193872130126883179653 175348851024398790596185)
                  ·
                    rfl

theorem cell20_384177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_384177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384177 prefixEnd_384177 := by exact prefixLift 384177
  have htrace : WordTrace (prefixWord ++ tailWord_384177) baseStart_384177 baseEnd_384177 := by
    simpa [prefixWord, tailWord_384177, baseEnd_384177] using wordTrace_append hprefix tailTrace_384177
  have hstable : (prefixWord ++ tailWord_384177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384177).length < 2 ^ (prefixWord ++ tailWord_384177).sum := by decide
  have hdescent : baseEnd_384177 < baseStart_384177 := by decide
  rcases family_descends (prefixWord ++ tailWord_384177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384215 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 2]
def baseStart_384215 : Nat := 118140960795 + 384215 * 2 ^ 59
def prefixEnd_384215 : Nat := 4983230072969 + 3 ^ 40 * 384215 * 2
def baseEnd_384215 : Nat := 175366195259839547329363

theorem tailTrace_384215 : CollatzResearch.WordTrace tailWord_384215 prefixEnd_384215 175366195259839547329363 := by
  unfold tailWord_384215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013472303062148542938099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9342314868708099028625399 14013472303062148542938099)
  ·
    refine ⟨21020208454593222814407149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14013472303062148542938099 21020208454593222814407149)
    ·
      refine ⟨7882578170472458555402681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21020208454593222814407149 7882578170472458555402681)
      ·
        refine ⟨5911933627854343916552011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7882578170472458555402681 5911933627854343916552011)
        ·
          refine ⟨8867900441781515874828017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911933627854343916552011 8867900441781515874828017)
          ·
            refine ⟨6650925331336136906121013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8867900441781515874828017 6650925331336136906121013)
            ·
              refine ⟨623524249812762834948845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6650925331336136906121013 623524249812762834948845)
              ·
                refine ⟨233821593679786063105817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623524249812762834948845 233821593679786063105817)
                ·
                  refine ⟨175366195259839547329363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233821593679786063105817 175366195259839547329363)
                  ·
                    rfl

theorem cell20_384215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 2].length) (baseStart_384215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384215 prefixEnd_384215 := by exact prefixLift 384215
  have htrace : WordTrace (prefixWord ++ tailWord_384215) baseStart_384215 baseEnd_384215 := by
    simpa [prefixWord, tailWord_384215, baseEnd_384215] using wordTrace_append hprefix tailTrace_384215
  have hstable : (prefixWord ++ tailWord_384215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384215).length < 2 ^ (prefixWord ++ tailWord_384215).sum := by decide
  have hdescent : baseEnd_384215 < baseStart_384215 := by decide
  rcases family_descends (prefixWord ++ tailWord_384215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384232 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 2]
def baseStart_384232 : Nat := 118140960795 + 384232 * 2 ^ 59
def prefixEnd_384232 : Nat := 4983230072969 + 3 ^ 40 * 384232 * 2
def baseEnd_384232 : Nat := 175373954523063043762627

theorem tailTrace_384232 : CollatzResearch.WordTrace tailWord_384232 prefixEnd_384232 175373954523063043762627 := by
  unfold tailWord_384232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007046172000280223153475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9342728229333706964204633 7007046172000280223153475)
  ·
    refine ⟨10510569258000420334730213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7007046172000280223153475 10510569258000420334730213)
    ·
      refine ⟨1970731735875078812761915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10510569258000420334730213 1970731735875078812761915)
      ·
        refine ⟨2956097603812618219142873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970731735875078812761915 2956097603812618219142873)
        ·
          refine ⟨2217073202859463664357155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2956097603812618219142873 2217073202859463664357155)
          ·
            refine ⟨3325609804289195496535733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217073202859463664357155 3325609804289195496535733)
            ·
              refine ⟨311775919152112077800225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3325609804289195496535733 311775919152112077800225)
              ·
                refine ⟨233831939364084058350169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311775919152112077800225 233831939364084058350169)
                ·
                  refine ⟨175373954523063043762627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233831939364084058350169 175373954523063043762627)
                  ·
                    rfl

theorem cell20_384232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_384232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384232 prefixEnd_384232 := by exact prefixLift 384232
  have htrace : WordTrace (prefixWord ++ tailWord_384232) baseStart_384232 baseEnd_384232 := by
    simpa [prefixWord, tailWord_384232, baseEnd_384232] using wordTrace_append hprefix tailTrace_384232
  have hstable : (prefixWord ++ tailWord_384232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384232).length < 2 ^ (prefixWord ++ tailWord_384232).sum := by decide
  have hdescent : baseEnd_384232 < baseStart_384232 := by decide
  rcases family_descends (prefixWord ++ tailWord_384232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384236 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_384236 : Nat := 118140960795 + 384236 * 2 ^ 59
def prefixEnd_384236 : Nat := 4983230072969 + 3 ^ 40 * 384236 * 2
def baseEnd_384236 : Nat := 175375780232056807629277

theorem tailTrace_384236 : CollatzResearch.WordTrace tailWord_384236 prefixEnd_384236 175375780232056807629277 := by
  unfold tailWord_384236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007119117993034564726281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9342825490657379419635041 7007119117993034564726281)
  ·
    refine ⟨5255339338494775923544711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7007119117993034564726281 5255339338494775923544711)
    ·
      refine ⟨7883009007742163885317067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5255339338494775923544711 7883009007742163885317067)
      ·
        refine ⟨11824513511613245827975601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883009007742163885317067 11824513511613245827975601)
        ·
          refine ⟨8868385133709934370981701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11824513511613245827975601 8868385133709934370981701)
          ·
            refine ⟨1662822212570612694559069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8868385133709934370981701 1662822212570612694559069)
            ·
              refine ⟨623558329713979760459651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1662822212570612694559069 623558329713979760459651)
              ·
                refine ⟨935337494570969640689477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623558329713979760459651 935337494570969640689477)
                ·
                  refine ⟨175375780232056807629277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 935337494570969640689477 175375780232056807629277)
                  ·
                    rfl

theorem cell20_384236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_384236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384236 prefixEnd_384236 := by exact prefixLift 384236
  have htrace : WordTrace (prefixWord ++ tailWord_384236) baseStart_384236 baseEnd_384236 := by
    simpa [prefixWord, tailWord_384236, baseEnd_384236] using wordTrace_append hprefix tailTrace_384236
  have hstable : (prefixWord ++ tailWord_384236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384236).length < 2 ^ (prefixWord ++ tailWord_384236).sum := by decide
  have hdescent : baseEnd_384236 < baseStart_384236 := by decide
  rcases family_descends (prefixWord ++ tailWord_384236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384242 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_384242 : Nat := 118140960795 + 384242 * 2 ^ 59
def prefixEnd_384242 : Nat := 4983230072969 + 3 ^ 40 * 384242 * 2
def baseEnd_384242 : Nat := 175378518795547453429253

theorem tailTrace_384242 : CollatzResearch.WordTrace tailWord_384242 prefixEnd_384242 175378518795547453429253 := by
  unfold tailWord_384242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503614268491083038542745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9342971382642888102780653 3503614268491083038542745)
  ·
    refine ⟨2627710701368312278907059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3503614268491083038542745 2627710701368312278907059)
    ·
      refine ⟨3941566052052468418360589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627710701368312278907059 3941566052052468418360589)
      ·
        refine ⟨1478087269519675656885221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3941566052052468418360589 1478087269519675656885221)
        ·
          refine ⟨277141363034939185665979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1478087269519675656885221 277141363034939185665979)
          ·
            refine ⟨415712044552408778498969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277141363034939185665979 415712044552408778498969)
            ·
              refine ⟨311784033414306583874227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415712044552408778498969 311784033414306583874227)
              ·
                refine ⟨467676050121459875811341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311784033414306583874227 467676050121459875811341)
                ·
                  refine ⟨175378518795547453429253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467676050121459875811341 175378518795547453429253)
                  ·
                    rfl

theorem cell20_384242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_384242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384242 prefixEnd_384242 := by exact prefixLift 384242
  have htrace : WordTrace (prefixWord ++ tailWord_384242) baseStart_384242 baseEnd_384242 := by
    simpa [prefixWord, tailWord_384242, baseEnd_384242] using wordTrace_append hprefix tailTrace_384242
  have hstable : (prefixWord ++ tailWord_384242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384242).length < 2 ^ (prefixWord ++ tailWord_384242).sum := by decide
  have hdescent : baseEnd_384242 < baseStart_384242 := by decide
  rcases family_descends (prefixWord ++ tailWord_384242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384243 : List Nat := [1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_384243 : Nat := 118140960795 + 384243 * 2 ^ 59
def prefixEnd_384243 : Nat := 4983230072969 + 3 ^ 40 * 384243 * 2
def baseEnd_384243 : Nat := 58459658407598631465305

theorem tailTrace_384243 : CollatzResearch.WordTrace tailWord_384243 prefixEnd_384243 58459658407598631465305 := by
  unfold tailWord_384243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14014493546960709324957383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9342995697973806216638255 14014493546960709324957383)
  ·
    refine ⟨21021740320441063987436075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14014493546960709324957383 21021740320441063987436075)
    ·
      refine ⟨31532610480661595981154113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21021740320441063987436075 31532610480661595981154113)
      ·
        refine ⟨23649457860496196985865585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31532610480661595981154113 23649457860496196985865585)
        ·
          refine ⟨17737093395372147739399189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23649457860496196985865585 17737093395372147739399189)
          ·
            refine ⟨831426252908069425284337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17737093395372147739399189 831426252908069425284337)
            ·
              refine ⟨623569689681052068963253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831426252908069425284337 623569689681052068963253)
              ·
                refine ⟨58459658407598631465305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623569689681052068963253 58459658407598631465305)
                ·
                  rfl

theorem cell20_384243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_384243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384243 prefixEnd_384243 := by exact prefixLift 384243
  have htrace : WordTrace (prefixWord ++ tailWord_384243) baseStart_384243 baseEnd_384243 := by
    simpa [prefixWord, tailWord_384243, baseEnd_384243] using wordTrace_append hprefix tailTrace_384243
  have hstable : (prefixWord ++ tailWord_384243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384243).length < 2 ^ (prefixWord ++ tailWord_384243).sum := by decide
  have hdescent : baseEnd_384243 < baseStart_384243 := by decide
  rcases family_descends (prefixWord ++ tailWord_384243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384287 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 2]
def baseStart_384287 : Nat := 118140960795 + 384287 * 2 ^ 59
def prefixEnd_384287 : Nat := 4983230072969 + 3 ^ 40 * 384287 * 2
def baseEnd_384287 : Nat := 175399058021727296929069

theorem tailTrace_384287 : CollatzResearch.WordTrace tailWord_384287 prefixEnd_384287 175399058021727296929069 := by
  unfold tailWord_384287
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016098358801304839559115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9344065572534203226372743 14016098358801304839559115)
  ·
    refine ⟨21024147538201957259338673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14016098358801304839559115 21024147538201957259338673)
    ·
      refine ⟨15768110653651467944504005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21024147538201957259338673 15768110653651467944504005)
      ·
        refine ⟨2956520747559650239594501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15768110653651467944504005 2956520747559650239594501)
        ·
          refine ⟨554347640167434419923969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2956520747559650239594501 554347640167434419923969)
          ·
            refine ⟨415760730125575814942977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554347640167434419923969 415760730125575814942977)
            ·
              refine ⟨311820547594181861207233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415760730125575814942977 311820547594181861207233)
              ·
                refine ⟨233865410695636395905425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311820547594181861207233 233865410695636395905425)
                ·
                  refine ⟨175399058021727296929069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233865410695636395905425 175399058021727296929069)
                  ·
                    rfl

theorem cell20_384287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 2].length) (baseStart_384287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384287 prefixEnd_384287 := by exact prefixLift 384287
  have htrace : WordTrace (prefixWord ++ tailWord_384287) baseStart_384287 baseEnd_384287 := by
    simpa [prefixWord, tailWord_384287, baseEnd_384287] using wordTrace_append hprefix tailTrace_384287
  have hstable : (prefixWord ++ tailWord_384287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384287).length < 2 ^ (prefixWord ++ tailWord_384287).sum := by decide
  have hdescent : baseEnd_384287 < baseStart_384287 := by decide
  rcases family_descends (prefixWord ++ tailWord_384287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384291 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 2]
def baseStart_384291 : Nat := 118140960795 + 384291 * 2 ^ 59
def prefixEnd_384291 : Nat := 4983230072969 + 3 ^ 40 * 384291 * 2
def baseEnd_384291 : Nat := 175400883730721060795719

theorem tailTrace_384291 : CollatzResearch.WordTrace tailWord_384291 prefixEnd_384291 175400883730721060795719 := by
  unfold tailWord_384291
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016244250786813522704727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9344162833857875681803151 14016244250786813522704727)
  ·
    refine ⟨21024366376180220284057091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14016244250786813522704727 21024366376180220284057091)
    ·
      refine ⟨31536549564270330426085637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21024366376180220284057091 31536549564270330426085637)
      ·
        refine ⟨5913103043300686954891057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31536549564270330426085637 5913103043300686954891057)
        ·
          refine ⟨4434827282475515216168293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5913103043300686954891057 4434827282475515216168293)
          ·
            refine ⟨831530115464159103031555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4434827282475515216168293 831530115464159103031555)
            ·
              refine ⟨1247295173196238654547333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831530115464159103031555 1247295173196238654547333)
              ·
                refine ⟨233867844974294747727625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1247295173196238654547333 233867844974294747727625)
                ·
                  refine ⟨175400883730721060795719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233867844974294747727625 175400883730721060795719)
                  ·
                    rfl

theorem cell20_384291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 2].length) (baseStart_384291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384291 prefixEnd_384291 := by exact prefixLift 384291
  have htrace : WordTrace (prefixWord ++ tailWord_384291) baseStart_384291 baseEnd_384291 := by
    simpa [prefixWord, tailWord_384291, baseEnd_384291] using wordTrace_append hprefix tailTrace_384291
  have hstable : (prefixWord ++ tailWord_384291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384291).length < 2 ^ (prefixWord ++ tailWord_384291).sum := by decide
  have hdescent : baseEnd_384291 < baseStart_384291 := by decide
  rcases family_descends (prefixWord ++ tailWord_384291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384298 : List Nat := [3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_384298 : Nat := 118140960795 + 384298 * 2 ^ 59
def prefixEnd_384298 : Nat := 4983230072969 + 3 ^ 40 * 384298 * 2
def baseEnd_384298 : Nat := 58468026240486715854119

theorem tailTrace_384298 : CollatzResearch.WordTrace tailWord_384298 prefixEnd_384298 58468026240486715854119 := by
  unfold tailWord_384298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504124890440363429552387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9344333041174302478806365 3504124890440363429552387)
  ·
    refine ⟨5256187335660545144328581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3504124890440363429552387 5256187335660545144328581)
    ·
      refine ⟨985535125436352214561609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5256187335660545144328581 985535125436352214561609)
      ·
        refine ⟨739151344077264160921207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985535125436352214561609 739151344077264160921207)
        ·
          refine ⟨1108727016115896241381811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739151344077264160921207 1108727016115896241381811)
          ·
            refine ⟨1663090524173844362072717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108727016115896241381811 1663090524173844362072717)
            ·
              refine ⟨623658946565191635777269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1663090524173844362072717 623658946565191635777269)
              ·
                refine ⟨58468026240486715854119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623658946565191635777269 58468026240486715854119)
                ·
                  rfl

theorem cell20_384298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_384298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384298 prefixEnd_384298 := by exact prefixLift 384298
  have htrace : WordTrace (prefixWord ++ tailWord_384298) baseStart_384298 baseEnd_384298 := by
    simpa [prefixWord, tailWord_384298, baseEnd_384298] using wordTrace_append hprefix tailTrace_384298
  have hstable : (prefixWord ++ tailWord_384298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384298).length < 2 ^ (prefixWord ++ tailWord_384298).sum := by decide
  have hdescent : baseEnd_384298 < baseStart_384298 := by decide
  rcases family_descends (prefixWord ++ tailWord_384298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384305 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_384305 : Nat := 118140960795 + 384305 * 2 ^ 59
def prefixEnd_384305 : Nat := 4983230072969 + 3 ^ 40 * 384305 * 2
def baseEnd_384305 : Nat := 175407273712199234328995

theorem tailTrace_384305 : CollatzResearch.WordTrace tailWord_384305 prefixEnd_384305 175407273712199234328995 := by
  unfold tailWord_384305
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016754872736093913714369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9344503248490729275809579 14016754872736093913714369)
  ·
    refine ⟨10512566154552070435285777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14016754872736093913714369 10512566154552070435285777)
    ·
      refine ⟨7884424615914052826464333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10512566154552070435285777 7884424615914052826464333)
      ·
        refine ⟨2956659230967769809924125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7884424615914052826464333 2956659230967769809924125)
        ·
          refine ⟨1108747211612913678721547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2956659230967769809924125 1108747211612913678721547)
          ·
            refine ⟨1663120817419370518082321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108747211612913678721547 1663120817419370518082321)
            ·
              refine ⟨1247340613064527888561741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663120817419370518082321 1247340613064527888561741)
              ·
                refine ⟨467752729899197958210653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1247340613064527888561741 467752729899197958210653)
                ·
                  refine ⟨175407273712199234328995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467752729899197958210653 175407273712199234328995)
                  ·
                    rfl

theorem cell20_384305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_384305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384305 prefixEnd_384305 := by exact prefixLift 384305
  have htrace : WordTrace (prefixWord ++ tailWord_384305) baseStart_384305 baseEnd_384305 := by
    simpa [prefixWord, tailWord_384305, baseEnd_384305] using wordTrace_append hprefix tailTrace_384305
  have hstable : (prefixWord ++ tailWord_384305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384305).length < 2 ^ (prefixWord ++ tailWord_384305).sum := by decide
  have hdescent : baseEnd_384305 < baseStart_384305 := by decide
  rcases family_descends (prefixWord ++ tailWord_384305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384342 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_384342 : Nat := 118140960795 + 384342 * 2 ^ 59
def prefixEnd_384342 : Nat := 4983230072969 + 3 ^ 40 * 384342 * 2
def baseEnd_384342 : Nat := 175424161520391550095511

theorem tailTrace_384342 : CollatzResearch.WordTrace tailWord_384342 prefixEnd_384342 175424161520391550095511 := by
  unfold tailWord_384342
  simp only [CollatzResearch.WordTrace]
  refine ⟨876131523350128077050705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9345402915734699488540853 876131523350128077050705)
  ·
    refine ⟨657098642512596057788029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 876131523350128077050705 657098642512596057788029)
    ·
      refine ⟨246411990942223521670511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 657098642512596057788029 246411990942223521670511)
      ·
        refine ⟨369617986413335282505767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246411990942223521670511 369617986413335282505767)
        ·
          refine ⟨554426979620002923758651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369617986413335282505767 554426979620002923758651)
          ·
            refine ⟨831640469430004385637977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554426979620002923758651 831640469430004385637977)
            ·
              refine ⟨623730352072503289228483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831640469430004385637977 623730352072503289228483)
              ·
                refine ⟨935595528108754933842725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623730352072503289228483 935595528108754933842725)
                ·
                  refine ⟨175424161520391550095511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 935595528108754933842725 175424161520391550095511)
                  ·
                    rfl

theorem cell20_384342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_384342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384342 prefixEnd_384342 := by exact prefixLift 384342
  have htrace : WordTrace (prefixWord ++ tailWord_384342) baseStart_384342 baseEnd_384342 := by
    simpa [prefixWord, tailWord_384342, baseEnd_384342] using wordTrace_append hprefix tailTrace_384342
  have hstable : (prefixWord ++ tailWord_384342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384342).length < 2 ^ (prefixWord ++ tailWord_384342).sum := by decide
  have hdescent : baseEnd_384342 < baseStart_384342 := by decide
  rcases family_descends (prefixWord ++ tailWord_384342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384343 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_384343 : Nat := 118140960795 + 384343 * 2 ^ 59
def prefixEnd_384343 : Nat := 4983230072969 + 3 ^ 40 * 384343 * 2
def baseEnd_384343 : Nat := 175424617947639991062173

theorem tailTrace_384343 : CollatzResearch.WordTrace tailWord_384343 prefixEnd_384343 175424617947639991062173 := by
  unfold tailWord_384343
  simp only [CollatzResearch.WordTrace]
  refine ⟨14018140846598426403597683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9345427231065617602398455 14018140846598426403597683)
  ·
    refine ⟨21027211269897639605396525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14018140846598426403597683 21027211269897639605396525)
    ·
      refine ⟨7885204226211614852023697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21027211269897639605396525 7885204226211614852023697)
      ·
        refine ⟨5913903169658711139017773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7885204226211614852023697 5913903169658711139017773)
        ·
          refine ⟨2217713688622016677131665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5913903169658711139017773 2217713688622016677131665)
          ·
            refine ⟨1663285266466512507848749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2217713688622016677131665 1663285266466512507848749)
            ·
              refine ⟨623731974924942190443281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1663285266466512507848749 623731974924942190443281)
              ·
                refine ⟨467798981193706642832461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623731974924942190443281 467798981193706642832461)
                ·
                  refine ⟨175424617947639991062173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467798981193706642832461 175424617947639991062173)
                  ·
                    rfl

theorem cell20_384343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_384343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384343 prefixEnd_384343 := by exact prefixLift 384343
  have htrace : WordTrace (prefixWord ++ tailWord_384343) baseStart_384343 baseEnd_384343 := by
    simpa [prefixWord, tailWord_384343, baseEnd_384343] using wordTrace_append hprefix tailTrace_384343
  have hstable : (prefixWord ++ tailWord_384343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384343).length < 2 ^ (prefixWord ++ tailWord_384343).sum := by decide
  have hdescent : baseEnd_384343 < baseStart_384343 := by decide
  rcases family_descends (prefixWord ++ tailWord_384343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384378 : List Nat := [3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_384378 : Nat := 118140960795 + 384378 * 2 ^ 59
def prefixEnd_384378 : Nat := 4983230072969 + 3 ^ 40 * 384378 * 2
def baseEnd_384378 : Nat := 58480197633778474965121

theorem tailTrace_384378 : CollatzResearch.WordTrace tailWord_384378 prefixEnd_384378 58480197633778474965121 := by
  unfold tailWord_384378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504854350367906845280447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9346278267647751587414525 3504854350367906845280447)
  ·
    refine ⟨5257281525551860267920671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3504854350367906845280447 5257281525551860267920671)
    ·
      refine ⟨7885922288327790401881007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257281525551860267920671 7885922288327790401881007)
      ·
        refine ⟨11828883432491685602821511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7885922288327790401881007 11828883432491685602821511)
        ·
          refine ⟨17743325148737528404232267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11828883432491685602821511 17743325148737528404232267)
          ·
            refine ⟨26614987723106292606348401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17743325148737528404232267 26614987723106292606348401)
            ·
              refine ⟨19961240792329719454761301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26614987723106292606348401 19961240792329719454761301)
              ·
                refine ⟨58480197633778474965121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19961240792329719454761301 58480197633778474965121)
                ·
                  rfl

theorem cell20_384378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_384378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384378 prefixEnd_384378 := by exact prefixLift 384378
  have htrace : WordTrace (prefixWord ++ tailWord_384378) baseStart_384378 baseEnd_384378 := by
    simpa [prefixWord, tailWord_384378, baseEnd_384378] using wordTrace_append hprefix tailTrace_384378
  have hstable : (prefixWord ++ tailWord_384378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384378).length < 2 ^ (prefixWord ++ tailWord_384378).sum := by decide
  have hdescent : baseEnd_384378 < baseStart_384378 := by decide
  rcases family_descends (prefixWord ++ tailWord_384378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384460 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 2]
def baseStart_384460 : Nat := 118140960795 + 384460 * 2 ^ 59
def prefixEnd_384460 : Nat := 4983230072969 + 3 ^ 40 * 384460 * 2
def baseEnd_384460 : Nat := 175478019935707584161695

theorem tailTrace_384460 : CollatzResearch.WordTrace tailWord_384460 prefixEnd_384460 175478019935707584161695 := by
  unfold tailWord_384460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011204093587277692803417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9348272124783036923737889 7011204093587277692803417)
  ·
    refine ⟨5258403070190458269602563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7011204093587277692803417 5258403070190458269602563)
    ·
      refine ⟨7887604605285687404403845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5258403070190458269602563 7887604605285687404403845)
      ·
        refine ⟨1478925863491066388325721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7887604605285687404403845 1478925863491066388325721)
        ·
          refine ⟨1109194397618299791244291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478925863491066388325721 1109194397618299791244291)
          ·
            refine ⟨1663791596427449686866437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109194397618299791244291 1663791596427449686866437)
            ·
              refine ⟨311960924330146816287457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1663791596427449686866437 311960924330146816287457)
              ·
                refine ⟨233970693247610112215593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311960924330146816287457 233970693247610112215593)
                ·
                  refine ⟨175478019935707584161695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233970693247610112215593 175478019935707584161695)
                  ·
                    rfl

theorem cell20_384460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_384460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384460 prefixEnd_384460 := by exact prefixLift 384460
  have htrace : WordTrace (prefixWord ++ tailWord_384460) baseStart_384460 baseEnd_384460 := by
    simpa [prefixWord, tailWord_384460, baseEnd_384460] using wordTrace_append hprefix tailTrace_384460
  have hstable : (prefixWord ++ tailWord_384460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384460).length < 2 ^ (prefixWord ++ tailWord_384460).sum := by decide
  have hdescent : baseEnd_384460 < baseStart_384460 := by decide
  rcases family_descends (prefixWord ++ tailWord_384460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384464 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 2]
def baseStart_384464 : Nat := 118140960795 + 384464 * 2 ^ 59
def prefixEnd_384464 : Nat := 4983230072969 + 3 ^ 40 * 384464 * 2
def baseEnd_384464 : Nat := 175479845644701348028345

theorem tailTrace_384464 : CollatzResearch.WordTrace tailWord_384464 prefixEnd_384464 175479845644701348028345 := by
  unfold tailWord_384464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011277039580032034376223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9348369386106709379168297 7011277039580032034376223)
  ·
    refine ⟨10516915559370048051564335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7011277039580032034376223 10516915559370048051564335)
    ·
      refine ⟨15775373339055072077346503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10516915559370048051564335 15775373339055072077346503)
      ·
        refine ⟨23663060008582608116019755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15775373339055072077346503 23663060008582608116019755)
        ·
          refine ⟨35494590012873912174029633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23663060008582608116019755 35494590012873912174029633)
          ·
            refine ⟨26620942509655434130522225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35494590012873912174029633 26620942509655434130522225)
            ·
              refine ⟨19965706882241575597891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26620942509655434130522225 19965706882241575597891669)
              ·
                refine ⟨233973127526268464037793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19965706882241575597891669 233973127526268464037793)
                ·
                  refine ⟨175479845644701348028345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233973127526268464037793 175479845644701348028345)
                  ·
                    rfl

theorem cell20_384464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_384464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384464 prefixEnd_384464 := by exact prefixLift 384464
  have htrace : WordTrace (prefixWord ++ tailWord_384464) baseStart_384464 baseEnd_384464 := by
    simpa [prefixWord, tailWord_384464, baseEnd_384464] using wordTrace_append hprefix tailTrace_384464
  have hstable : (prefixWord ++ tailWord_384464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384464).length < 2 ^ (prefixWord ++ tailWord_384464).sum := by decide
  have hdescent : baseEnd_384464 < baseStart_384464 := by decide
  rcases family_descends (prefixWord ++ tailWord_384464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384498 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_384498 : Nat := 118140960795 + 384498 * 2 ^ 59
def prefixEnd_384498 : Nat := 4983230072969 + 3 ^ 40 * 384498 * 2
def baseEnd_384498 : Nat := 175495364171148340894873

theorem tailTrace_384498 : CollatzResearch.WordTrace tailWord_384498 prefixEnd_384498 175495364171148340894873 := by
  unfold tailWord_384498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505948540259221968872537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9349196107357925250326765 3505948540259221968872537)
  ·
    refine ⟨2629461405194416476654403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3505948540259221968872537 2629461405194416476654403)
    ·
      refine ⟨3944192107791624714981605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629461405194416476654403 3944192107791624714981605)
      ·
        refine ⟨739536020210929634059051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3944192107791624714981605 739536020210929634059051)
        ·
          refine ⟨1109304030316394451088577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739536020210929634059051 1109304030316394451088577)
          ·
            refine ⟨831978022737295838316433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109304030316394451088577 831978022737295838316433)
            ·
              refine ⟨623983517052971878737325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831978022737295838316433 623983517052971878737325)
              ·
                refine ⟨233993818894864454526497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623983517052971878737325 233993818894864454526497)
                ·
                  refine ⟨175495364171148340894873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233993818894864454526497 175495364171148340894873)
                  ·
                    rfl

theorem cell20_384498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_384498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384498 prefixEnd_384498 := by exact prefixLift 384498
  have htrace : WordTrace (prefixWord ++ tailWord_384498) baseStart_384498 baseEnd_384498 := by
    simpa [prefixWord, tailWord_384498, baseEnd_384498] using wordTrace_append hprefix tailTrace_384498
  have hstable : (prefixWord ++ tailWord_384498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384498).length < 2 ^ (prefixWord ++ tailWord_384498).sum := by decide
  have hdescent : baseEnd_384498 < baseStart_384498 := by decide
  rcases family_descends (prefixWord ++ tailWord_384498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384519 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 2]
def baseStart_384519 : Nat := 118140960795 + 384519 * 2 ^ 59
def prefixEnd_384519 : Nat := 4983230072969 + 3 ^ 40 * 384519 * 2
def baseEnd_384519 : Nat := 175504949143365601194787

theorem tailTrace_384519 : CollatzResearch.WordTrace tailWord_384519 prefixEnd_384519 175504949143365601194787 := by
  unfold tailWord_384519
  simp only [CollatzResearch.WordTrace]
  refine ⟨14024560093960808462004611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9349706729307205641336407 14024560093960808462004611)
  ·
    refine ⟨21036840140941212693006917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14024560093960808462004611 21036840140941212693006917)
    ·
      refine ⟨3944407526426477379938797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21036840140941212693006917 3944407526426477379938797)
      ·
        refine ⟨1479152822409929017477049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3944407526426477379938797 1479152822409929017477049)
        ·
          refine ⟨1109364616807446763107787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479152822409929017477049 1109364616807446763107787)
          ·
            refine ⟨1664046925211170144661681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109364616807446763107787 1664046925211170144661681)
            ·
              refine ⟨1248035193908377608496261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1664046925211170144661681 1248035193908377608496261)
              ·
                refine ⟨234006598857820801593049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1248035193908377608496261 234006598857820801593049)
                ·
                  refine ⟨175504949143365601194787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234006598857820801593049 175504949143365601194787)
                  ·
                    rfl

theorem cell20_384519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 2].length) (baseStart_384519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384519 prefixEnd_384519 := by exact prefixLift 384519
  have htrace : WordTrace (prefixWord ++ tailWord_384519) baseStart_384519 baseEnd_384519 := by
    simpa [prefixWord, tailWord_384519, baseEnd_384519] using wordTrace_append hprefix tailTrace_384519
  have hstable : (prefixWord ++ tailWord_384519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384519).length < 2 ^ (prefixWord ++ tailWord_384519).sum := by decide
  have hdescent : baseEnd_384519 < baseStart_384519 := by decide
  rcases family_descends (prefixWord ++ tailWord_384519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384537 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_384537 : Nat := 118140960795 + 384537 * 2 ^ 59
def prefixEnd_384537 : Nat := 4983230072969 + 3 ^ 40 * 384537 * 2
def baseEnd_384537 : Nat := 175513164833837538594713

theorem tailTrace_384537 : CollatzResearch.WordTrace tailWord_384537 prefixEnd_384537 175513164833837538594713 := by
  unfold tailWord_384537
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025216607895597536159865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9350144405263731690773243 14025216607895597536159865)
  ·
    refine ⟨10518912455921698152119899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14025216607895597536159865 10518912455921698152119899)
    ·
      refine ⟨15778368683882547228179849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10518912455921698152119899 15778368683882547228179849)
      ·
        refine ⟨11833776512911910421134887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15778368683882547228179849 11833776512911910421134887)
        ·
          refine ⟨17750664769367865631702331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11833776512911910421134887 17750664769367865631702331)
          ·
            refine ⟨26625997154051798447553497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17750664769367865631702331 26625997154051798447553497)
            ·
              refine ⟨19969497865538848835665123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26625997154051798447553497 19969497865538848835665123)
              ·
                refine ⟨29954246798308273253497685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19969497865538848835665123 29954246798308273253497685)
                ·
                  refine ⟨175513164833837538594713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29954246798308273253497685 175513164833837538594713)
                  ·
                    rfl

theorem cell20_384537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_384537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384537 prefixEnd_384537 := by exact prefixLift 384537
  have htrace : WordTrace (prefixWord ++ tailWord_384537) baseStart_384537 baseEnd_384537 := by
    simpa [prefixWord, tailWord_384537, baseEnd_384537] using wordTrace_append hprefix tailTrace_384537
  have hstable : (prefixWord ++ tailWord_384537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384537).length < 2 ^ (prefixWord ++ tailWord_384537).sum := by decide
  have hdescent : baseEnd_384537 < baseStart_384537 := by decide
  rcases family_descends (prefixWord ++ tailWord_384537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384547 : List Nat := [1, 1, 1, 4, 5, 1, 1, 6]
def baseStart_384547 : Nat := 118140960795 + 384547 * 2 ^ 59
def prefixEnd_384547 : Nat := 4983230072969 + 3 ^ 40 * 384547 * 2
def baseEnd_384547 : Nat := 58505909702107316087113

theorem tailTrace_384547 : CollatzResearch.WordTrace tailWord_384547 prefixEnd_384547 58505909702107316087113 := by
  unfold tailWord_384547
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025581337859369244023895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9350387558572912829349263 14025581337859369244023895)
  ·
    refine ⟨21038372006789053866035843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14025581337859369244023895 21038372006789053866035843)
    ·
      refine ⟨31557558010183580799053765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21038372006789053866035843 31557558010183580799053765)
      ·
        refine ⟨5917042126909421399822581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31557558010183580799053765 5917042126909421399822581)
        ·
          refine ⟨554722699397758256233367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5917042126909421399822581 554722699397758256233367)
          ·
            refine ⟨832084049096637384350051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554722699397758256233367 832084049096637384350051)
            ·
              refine ⟨1248126073644956076525077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832084049096637384350051 1248126073644956076525077)
              ·
                refine ⟨58505909702107316087113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1248126073644956076525077 58505909702107316087113)
                ·
                  rfl

theorem cell20_384547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_384547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384547 prefixEnd_384547 := by exact prefixLift 384547
  have htrace : WordTrace (prefixWord ++ tailWord_384547) baseStart_384547 baseEnd_384547 := by
    simpa [prefixWord, tailWord_384547, baseEnd_384547] using wordTrace_append hprefix tailTrace_384547
  have hstable : (prefixWord ++ tailWord_384547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384547).length < 2 ^ (prefixWord ++ tailWord_384547).sum := by decide
  have hdescent : baseEnd_384547 < baseStart_384547 := by decide
  rcases family_descends (prefixWord ++ tailWord_384547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384554 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_384554 : Nat := 118140960795 + 384554 * 2 ^ 59
def prefixEnd_384554 : Nat := 4983230072969 + 3 ^ 40 * 384554 * 2
def baseEnd_384554 : Nat := 175520924097061035027977

theorem tailTrace_384554 : CollatzResearch.WordTrace tailWord_384554 prefixEnd_384554 175520924097061035027977 := by
  unfold tailWord_384554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506459162208502359882179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9350557765889339626352477 3506459162208502359882179)
  ·
    refine ⟨5259688743312753539823269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3506459162208502359882179 5259688743312753539823269)
    ·
      refine ⟨986191639371141288716863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5259688743312753539823269 986191639371141288716863)
      ·
        refine ⟨1479287459056711933075295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986191639371141288716863 1479287459056711933075295)
        ·
          refine ⟨2218931188585067899612943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479287459056711933075295 2218931188585067899612943)
          ·
            refine ⟨3328396782877601849419415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218931188585067899612943 3328396782877601849419415)
            ·
              refine ⟨4992595174316402774129123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328396782877601849419415 4992595174316402774129123)
              ·
                refine ⟨7488892761474604161193685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992595174316402774129123 7488892761474604161193685)
                ·
                  refine ⟨175520924097061035027977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7488892761474604161193685 175520924097061035027977)
                  ·
                    rfl

theorem cell20_384554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_384554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384554 prefixEnd_384554 := by exact prefixLift 384554
  have htrace : WordTrace (prefixWord ++ tailWord_384554) baseStart_384554 baseEnd_384554 := by
    simpa [prefixWord, tailWord_384554, baseEnd_384554] using wordTrace_append hprefix tailTrace_384554
  have hstable : (prefixWord ++ tailWord_384554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384554).length < 2 ^ (prefixWord ++ tailWord_384554).sum := by decide
  have hdescent : baseEnd_384554 < baseStart_384554 := by decide
  rcases family_descends (prefixWord ++ tailWord_384554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384568 : List Nat := [2, 1, 2, 1, 4, 2, 8]
def baseStart_384568 : Nat := 118140960795 + 384568 * 2 ^ 59
def prefixEnd_384568 : Nat := 4983230072969 + 3 ^ 40 * 384568 * 2
def baseEnd_384568 : Nat := 19503034897615467617917

theorem tailTrace_384568 : CollatzResearch.WordTrace tailWord_384568 prefixEnd_384568 19503034897615467617917 := by
  unfold tailWord_384568
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013173635391644915269179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9350898180522193220358905 7013173635391644915269179)
  ·
    refine ⟨10519760453087467372903769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7013173635391644915269179 10519760453087467372903769)
    ·
      refine ⟨7889820339815600529677827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10519760453087467372903769 7889820339815600529677827)
      ·
        refine ⟨11834730509723400794516741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889820339815600529677827 11834730509723400794516741)
        ·
          refine ⟨2219011970573137648971889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11834730509723400794516741 2219011970573137648971889)
          ·
            refine ⟨1664258977929853236728917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2219011970573137648971889 1664258977929853236728917)
            ·
              refine ⟨19503034897615467617917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1664258977929853236728917 19503034897615467617917)
              ·
                rfl

theorem cell20_384568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_384568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384568 prefixEnd_384568 := by exact prefixLift 384568
  have htrace : WordTrace (prefixWord ++ tailWord_384568) baseStart_384568 baseEnd_384568 := by
    simpa [prefixWord, tailWord_384568, baseEnd_384568] using wordTrace_append hprefix tailTrace_384568
  have hstable : (prefixWord ++ tailWord_384568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384568).length < 2 ^ (prefixWord ++ tailWord_384568).sum := by decide
  have hdescent : baseEnd_384568 < baseStart_384568 := by decide
  rcases family_descends (prefixWord ++ tailWord_384568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384588 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_384588 : Nat := 118140960795 + 384588 * 2 ^ 59
def prefixEnd_384588 : Nat := 4983230072969 + 3 ^ 40 * 384588 * 2
def baseEnd_384588 : Nat := 175536442623508027894505

theorem tailTrace_384588 : CollatzResearch.WordTrace tailWord_384588 prefixEnd_384588 175536442623508027894505 := by
  unfold tailWord_384588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013538365355416623133209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9351384487140555497510945 7013538365355416623133209)
  ·
    refine ⟨5260153774016562467349907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7013538365355416623133209 5260153774016562467349907)
    ·
      refine ⟨7890230661024843701024861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5260153774016562467349907 7890230661024843701024861)
      ·
        refine ⟨2958836497884316387884323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7890230661024843701024861 2958836497884316387884323)
        ·
          refine ⟨4438254746826474581826485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958836497884316387884323 4438254746826474581826485)
          ·
            refine ⟨416086382514981992046233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4438254746826474581826485 416086382514981992046233)
            ·
              refine ⟨312064786886236494034675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416086382514981992046233 312064786886236494034675)
              ·
                refine ⟨468097180329354741052013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312064786886236494034675 468097180329354741052013)
                ·
                  refine ⟨175536442623508027894505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468097180329354741052013 175536442623508027894505)
                  ·
                    rfl

theorem cell20_384588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_384588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384588 prefixEnd_384588 := by exact prefixLift 384588
  have htrace : WordTrace (prefixWord ++ tailWord_384588) baseStart_384588 baseEnd_384588 := by
    simpa [prefixWord, tailWord_384588, baseEnd_384588] using wordTrace_append hprefix tailTrace_384588
  have hstable : (prefixWord ++ tailWord_384588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384588).length < 2 ^ (prefixWord ++ tailWord_384588).sum := by decide
  have hdescent : baseEnd_384588 < baseStart_384588 := by decide
  rcases family_descends (prefixWord ++ tailWord_384588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384592 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_384592 : Nat := 118140960795 + 384592 * 2 ^ 59
def prefixEnd_384592 : Nat := 4983230072969 + 3 ^ 40 * 384592 * 2
def baseEnd_384592 : Nat := 175538268332501791761155

theorem tailTrace_384592 : CollatzResearch.WordTrace tailWord_384592 prefixEnd_384592 175538268332501791761155 := by
  unfold tailWord_384592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013611311348170964706015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9351481748464227952941353 7013611311348170964706015)
  ·
    refine ⟨10520416967022256447059023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7013611311348170964706015 10520416967022256447059023)
    ·
      refine ⟨15780625450533384670588535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10520416967022256447059023 15780625450533384670588535)
      ·
        refine ⟨23670938175800077005882803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15780625450533384670588535 23670938175800077005882803)
        ·
          refine ⟨35506407263700115508824205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23670938175800077005882803 35506407263700115508824205)
          ·
            refine ⟨13314902723887543315809077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35506407263700115508824205 13314902723887543315809077)
            ·
              refine ⟨1248272130364457185857101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13314902723887543315809077 1248272130364457185857101)
              ·
                refine ⟨468102048886671444696413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1248272130364457185857101 468102048886671444696413)
                ·
                  refine ⟨175538268332501791761155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468102048886671444696413 175538268332501791761155)
                  ·
                    rfl

theorem cell20_384592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_384592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384592 prefixEnd_384592 := by exact prefixLift 384592
  have htrace : WordTrace (prefixWord ++ tailWord_384592) baseStart_384592 baseEnd_384592 := by
    simpa [prefixWord, tailWord_384592, baseEnd_384592] using wordTrace_append hprefix tailTrace_384592
  have hstable : (prefixWord ++ tailWord_384592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384592).length < 2 ^ (prefixWord ++ tailWord_384592).sum := by decide
  have hdescent : baseEnd_384592 < baseStart_384592 := by decide
  rcases family_descends (prefixWord ++ tailWord_384592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384629 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 2]
def baseStart_384629 : Nat := 118140960795 + 384629 * 2 ^ 59
def prefixEnd_384629 : Nat := 4983230072969 + 3 ^ 40 * 384629 * 2
def baseEnd_384629 : Nat := 175555156140694107527671

theorem tailTrace_384629 : CollatzResearch.WordTrace tailWord_384629 prefixEnd_384629 175555156140694107527671 := by
  unfold tailWord_384629
  simp only [CollatzResearch.WordTrace]
  refine ⟨14028572123562297248508941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9352381415708198165672627 14028572123562297248508941)
  ·
    refine ⟨5260714546335861468190853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14028572123562297248508941 5260714546335861468190853)
    ·
      refine ⟨986383977437974025285785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5260714546335861468190853 986383977437974025285785)
      ·
        refine ⟨739787983078480518964339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 986383977437974025285785 739787983078480518964339)
        ·
          refine ⟨1109681974617720778446509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739787983078480518964339 1109681974617720778446509)
          ·
            refine ⟨416130740481645291917441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1109681974617720778446509 416130740481645291917441)
            ·
              refine ⟨312098055361233968938081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416130740481645291917441 312098055361233968938081)
              ·
                refine ⟨234073541520925476703561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312098055361233968938081 234073541520925476703561)
                ·
                  refine ⟨175555156140694107527671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234073541520925476703561 175555156140694107527671)
                  ·
                    rfl

theorem cell20_384629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_384629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384629 prefixEnd_384629 := by exact prefixLift 384629
  have htrace : WordTrace (prefixWord ++ tailWord_384629) baseStart_384629 baseEnd_384629 := by
    simpa [prefixWord, tailWord_384629, baseEnd_384629] using wordTrace_append hprefix tailTrace_384629
  have hstable : (prefixWord ++ tailWord_384629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384629).length < 2 ^ (prefixWord ++ tailWord_384629).sum := by decide
  have hdescent : baseEnd_384629 < baseStart_384629 := by decide
  rcases family_descends (prefixWord ++ tailWord_384629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384654 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_384654 : Nat := 118140960795 + 384654 * 2 ^ 59
def prefixEnd_384654 : Nat := 4983230072969 + 3 ^ 40 * 384654 * 2
def baseEnd_384654 : Nat := 175566566821905131694235

theorem tailTrace_384654 : CollatzResearch.WordTrace tailWord_384654 prefixEnd_384654 175566566821905131694235 := by
  unfold tailWord_384654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753685493558965814771127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9352989298981151012112677 1753685493558965814771127)
  ·
    refine ⟨2630528240338448722156691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753685493558965814771127 2630528240338448722156691)
    ·
      refine ⟨3945792360507673083235037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630528240338448722156691 3945792360507673083235037)
      ·
        refine ⟨1479672135190377406213139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3945792360507673083235037 1479672135190377406213139)
        ·
          refine ⟨2219508202785566109319709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479672135190377406213139 2219508202785566109319709)
          ·
            refine ⟨832315576044587290994891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2219508202785566109319709 832315576044587290994891)
            ·
              refine ⟨1248473364066880936492337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832315576044587290994891 1248473364066880936492337)
              ·
                refine ⟨936355023050160702369253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248473364066880936492337 936355023050160702369253)
                ·
                  refine ⟨175566566821905131694235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936355023050160702369253 175566566821905131694235)
                  ·
                    rfl

theorem cell20_384654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_384654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384654 prefixEnd_384654 := by exact prefixLift 384654
  have htrace : WordTrace (prefixWord ++ tailWord_384654) baseStart_384654 baseEnd_384654 := by
    simpa [prefixWord, tailWord_384654, baseEnd_384654] using wordTrace_append hprefix tailTrace_384654
  have hstable : (prefixWord ++ tailWord_384654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384654).length < 2 ^ (prefixWord ++ tailWord_384654).sum := by decide
  have hdescent : baseEnd_384654 < baseStart_384654 := by decide
  rcases family_descends (prefixWord ++ tailWord_384654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384702 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_384702 : Nat := 118140960795 + 384702 * 2 ^ 59
def prefixEnd_384702 : Nat := 4983230072969 + 3 ^ 40 * 384702 * 2
def baseEnd_384702 : Nat := 175588475329830298094039

theorem tailTrace_384702 : CollatzResearch.WordTrace tailWord_384702 prefixEnd_384702 175588475329830298094039 := by
  unfold tailWord_384702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753904331537228839489545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9354156434865220477277573 1753904331537228839489545)
  ·
    refine ⟨1315428248652921629617159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1753904331537228839489545 1315428248652921629617159)
    ·
      refine ⟨1973142372979382444425739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315428248652921629617159 1973142372979382444425739)
      ·
        refine ⟨2959713559469073666638609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973142372979382444425739 2959713559469073666638609)
        ·
          refine ⟨2219785169601805249978957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2959713559469073666638609 2219785169601805249978957)
          ·
            refine ⟨832419438600676968742109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2219785169601805249978957 832419438600676968742109)
            ·
              refine ⟨312157289475253863278291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832419438600676968742109 312157289475253863278291)
              ·
                refine ⟨468235934212880794917437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312157289475253863278291 468235934212880794917437)
                ·
                  refine ⟨175588475329830298094039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468235934212880794917437 175588475329830298094039)
                  ·
                    rfl

theorem cell20_384702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_384702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384702 prefixEnd_384702 := by exact prefixLift 384702
  have htrace : WordTrace (prefixWord ++ tailWord_384702) baseStart_384702 baseEnd_384702 := by
    simpa [prefixWord, tailWord_384702, baseEnd_384702] using wordTrace_append hprefix tailTrace_384702
  have hstable : (prefixWord ++ tailWord_384702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384702).length < 2 ^ (prefixWord ++ tailWord_384702).sum := by decide
  have hdescent : baseEnd_384702 < baseStart_384702 := by decide
  rcases family_descends (prefixWord ++ tailWord_384702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384727 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_384727 : Nat := 118140960795 + 384727 * 2 ^ 59
def prefixEnd_384727 : Nat := 4983230072969 + 3 ^ 40 * 384727 * 2
def baseEnd_384727 : Nat := 175599886011041322260603

theorem tailTrace_384727 : CollatzResearch.WordTrace tailWord_384727 prefixEnd_384727 175599886011041322260603 := by
  unfold tailWord_384727
  simp only [CollatzResearch.WordTrace]
  refine ⟨14032146477207259985576435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9354764318138173323717623 14032146477207259985576435)
  ·
    refine ⟨21048219715810889978364653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14032146477207259985576435 21048219715810889978364653)
    ·
      refine ⟨7893082393429083741886745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21048219715810889978364653 7893082393429083741886745)
      ·
        refine ⟨5919811795071812806415059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7893082393429083741886745 5919811795071812806415059)
        ·
          refine ⟨8879717692607719209622589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919811795071812806415059 8879717692607719209622589)
          ·
            refine ⟨3329894134727894703608471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8879717692607719209622589 3329894134727894703608471)
            ·
              refine ⟨4994841202091842055412707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329894134727894703608471 4994841202091842055412707)
              ·
                refine ⟨7492261803137763083119061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994841202091842055412707 7492261803137763083119061)
                ·
                  refine ⟨175599886011041322260603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7492261803137763083119061 175599886011041322260603)
                  ·
                    rfl

theorem cell20_384727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_384727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384727 prefixEnd_384727 := by exact prefixLift 384727
  have htrace : WordTrace (prefixWord ++ tailWord_384727) baseStart_384727 baseEnd_384727 := by
    simpa [prefixWord, tailWord_384727, baseEnd_384727] using wordTrace_append hprefix tailTrace_384727
  have hstable : (prefixWord ++ tailWord_384727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384727).length < 2 ^ (prefixWord ++ tailWord_384727).sum := by decide
  have hdescent : baseEnd_384727 < baseStart_384727 := by decide
  rcases family_descends (prefixWord ++ tailWord_384727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384733 : List Nat := [1, 4, 3, 3, 2, 1, 6]
def baseStart_384733 : Nat := 118140960795 + 384733 * 2 ^ 59
def prefixEnd_384733 : Nat := 4983230072969 + 3 ^ 40 * 384733 * 2
def baseEnd_384733 : Nat := 19511402730503552006731

theorem tailTrace_384733 : CollatzResearch.WordTrace tailWord_384733 prefixEnd_384733 19511402730503552006731 := by
  unfold tailWord_384733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14032365315185523010294853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9354910210123682006863235 14032365315185523010294853)
  ·
    refine ⟨2631068496597285564430285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14032365315185523010294853 2631068496597285564430285)
    ·
      refine ⟨986650686223982086661357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2631068496597285564430285 986650686223982086661357)
      ·
        refine ⟨369994007333993282498009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 986650686223982086661357 369994007333993282498009)
        ·
          refine ⟨277495505500494961873507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369994007333993282498009 277495505500494961873507)
          ·
            refine ⟨416243258250742442810261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277495505500494961873507 416243258250742442810261)
            ·
              refine ⟨19511402730503552006731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 416243258250742442810261 19511402730503552006731)
              ·
                rfl

theorem cell20_384733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 6].length) (baseStart_384733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384733 prefixEnd_384733 := by exact prefixLift 384733
  have htrace : WordTrace (prefixWord ++ tailWord_384733) baseStart_384733 baseEnd_384733 := by
    simpa [prefixWord, tailWord_384733, baseEnd_384733] using wordTrace_append hprefix tailTrace_384733
  have hstable : (prefixWord ++ tailWord_384733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384733).length < 2 ^ (prefixWord ++ tailWord_384733).sum := by decide
  have hdescent : baseEnd_384733 < baseStart_384733 := by decide
  rcases family_descends (prefixWord ++ tailWord_384733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384737 : List Nat := [1, 2, 3, 1, 5, 2, 6]
def baseStart_384737 : Nat := 118140960795 + 384737 * 2 ^ 59
def prefixEnd_384737 : Nat := 4983230072969 + 3 ^ 40 * 384737 * 2
def baseEnd_384737 : Nat := 19511605587058414658581

theorem tailTrace_384737 : CollatzResearch.WordTrace tailWord_384737 prefixEnd_384737 19511605587058414658581 := by
  unfold tailWord_384737
  simp only [CollatzResearch.WordTrace]
  refine ⟨14032511207171031693440465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9355007471447354462293643 14032511207171031693440465)
  ·
    refine ⟨10524383405378273770080349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14032511207171031693440465 10524383405378273770080349)
    ·
      refine ⟨3946643777016852663780131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10524383405378273770080349 3946643777016852663780131)
      ·
        refine ⟨5919965665525278995670197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946643777016852663780131 5919965665525278995670197)
        ·
          refine ⟨554996781142994905844081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5919965665525278995670197 554996781142994905844081)
          ·
            refine ⟨416247585857246179383061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554996781142994905844081 416247585857246179383061)
            ·
              refine ⟨19511605587058414658581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 416247585857246179383061 19511605587058414658581)
              ·
                rfl

theorem cell20_384737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_384737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384737 prefixEnd_384737 := by exact prefixLift 384737
  have htrace : WordTrace (prefixWord ++ tailWord_384737) baseStart_384737 baseEnd_384737 := by
    simpa [prefixWord, tailWord_384737, baseEnd_384737] using wordTrace_append hprefix tailTrace_384737
  have hstable : (prefixWord ++ tailWord_384737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384737).length < 2 ^ (prefixWord ++ tailWord_384737).sum := by decide
  have hdescent : baseEnd_384737 < baseStart_384737 := by decide
  rcases family_descends (prefixWord ++ tailWord_384737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384743 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 2]
def baseStart_384743 : Nat := 118140960795 + 384743 * 2 ^ 59
def prefixEnd_384743 : Nat := 4983230072969 + 3 ^ 40 * 384743 * 2
def baseEnd_384743 : Nat := 175607188847016377727205

theorem tailTrace_384743 : CollatzResearch.WordTrace tailWord_384743 prefixEnd_384743 175607188847016377727205 := by
  unfold tailWord_384743
  simp only [CollatzResearch.WordTrace]
  refine ⟨14032730045149294718158883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9355153363432863145439255 14032730045149294718158883)
  ·
    refine ⟨21049095067723942077238325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14032730045149294718158883 21049095067723942077238325)
    ·
      refine ⟨1973352662599119569741093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21049095067723942077238325 1973352662599119569741093)
      ·
        refine ⟨370003624237334919326455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1973352662599119569741093 370003624237334919326455)
        ·
          refine ⟨555005436356002378989683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370003624237334919326455 555005436356002378989683)
          ·
            refine ⟨832508154534003568484525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555005436356002378989683 832508154534003568484525)
            ·
              refine ⟨312190557950251338181697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832508154534003568484525 312190557950251338181697)
              ·
                refine ⟨234142918462688503636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312190557950251338181697 234142918462688503636273)
                ·
                  refine ⟨175607188847016377727205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234142918462688503636273 175607188847016377727205)
                  ·
                    rfl

theorem cell20_384743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 2].length) (baseStart_384743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384743 prefixEnd_384743 := by exact prefixLift 384743
  have htrace : WordTrace (prefixWord ++ tailWord_384743) baseStart_384743 baseEnd_384743 := by
    simpa [prefixWord, tailWord_384743, baseEnd_384743] using wordTrace_append hprefix tailTrace_384743
  have hstable : (prefixWord ++ tailWord_384743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384743).length < 2 ^ (prefixWord ++ tailWord_384743).sum := by decide
  have hdescent : baseEnd_384743 < baseStart_384743 := by decide
  rcases family_descends (prefixWord ++ tailWord_384743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384744 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_384744 : Nat := 118140960795 + 384744 * 2 ^ 59
def prefixEnd_384744 : Nat := 4983230072969 + 3 ^ 40 * 384744 * 2
def baseEnd_384744 : Nat := 175607645274264818693867

theorem tailTrace_384744 : CollatzResearch.WordTrace tailWord_384744 prefixEnd_384744 175607645274264818693867 := by
  unfold tailWord_384744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7016383259072835944472643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9355177678763781259296857 7016383259072835944472643)
  ·
    refine ⟨10524574888609253916708965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7016383259072835944472643 10524574888609253916708965)
    ·
      refine ⟨1973357791614235109382931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10524574888609253916708965 1973357791614235109382931)
      ·
        refine ⟨2960036687421352664074397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973357791614235109382931 2960036687421352664074397)
        ·
          refine ⟨1110013757783007249027899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2960036687421352664074397 1110013757783007249027899)
          ·
            refine ⟨1665020636674510873541849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110013757783007249027899 1665020636674510873541849)
            ·
              refine ⟨1248765477505883155156387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665020636674510873541849 1248765477505883155156387)
              ·
                refine ⟨1873148216258824732734581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248765477505883155156387 1873148216258824732734581)
                ·
                  refine ⟨175607645274264818693867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873148216258824732734581 175607645274264818693867)
                  ·
                    rfl

theorem cell20_384744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_384744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384744 prefixEnd_384744 := by exact prefixLift 384744
  have htrace : WordTrace (prefixWord ++ tailWord_384744) baseStart_384744 baseEnd_384744 := by
    simpa [prefixWord, tailWord_384744, baseEnd_384744] using wordTrace_append hprefix tailTrace_384744
  have hstable : (prefixWord ++ tailWord_384744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384744).length < 2 ^ (prefixWord ++ tailWord_384744).sum := by decide
  have hdescent : baseEnd_384744 < baseStart_384744 := by decide
  rcases family_descends (prefixWord ++ tailWord_384744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384765 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_384765 : Nat := 118140960795 + 384765 * 2 ^ 59
def prefixEnd_384765 : Nat := 4983230072969 + 3 ^ 40 * 384765 * 2
def baseEnd_384765 : Nat := 175617230246482078993781

theorem tailTrace_384765 : CollatzResearch.WordTrace tailWord_384765 prefixEnd_384765 175617230246482078993781 := by
  unfold tailWord_384765
  simp only [CollatzResearch.WordTrace]
  refine ⟨14033532451069592475459749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9355688300713061650306499 14033532451069592475459749)
  ·
    refine ⟨2631287334575548589148703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14033532451069592475459749 2631287334575548589148703)
    ·
      refine ⟨3946931001863322883723055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2631287334575548589148703 3946931001863322883723055)
      ·
        refine ⟨5920396502794984325584583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946931001863322883723055 5920396502794984325584583)
        ·
          refine ⟨8880594754192476488376875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920396502794984325584583 8880594754192476488376875)
          ·
            refine ⟨13320892131288714732565313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8880594754192476488376875 13320892131288714732565313)
            ·
              refine ⟨9990669098466536049423985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13320892131288714732565313 9990669098466536049423985)
              ·
                refine ⟨7493001823849902037067989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9990669098466536049423985 7493001823849902037067989)
                ·
                  refine ⟨175617230246482078993781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7493001823849902037067989 175617230246482078993781)
                  ·
                    rfl

theorem cell20_384765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_384765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384765 prefixEnd_384765 := by exact prefixLift 384765
  have htrace : WordTrace (prefixWord ++ tailWord_384765) baseStart_384765 baseEnd_384765 := by
    simpa [prefixWord, tailWord_384765, baseEnd_384765] using wordTrace_append hprefix tailTrace_384765
  have hstable : (prefixWord ++ tailWord_384765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384765).length < 2 ^ (prefixWord ++ tailWord_384765).sum := by decide
  have hdescent : baseEnd_384765 < baseStart_384765 := by decide
  rcases family_descends (prefixWord ++ tailWord_384765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384803 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_384803 : Nat := 118140960795 + 384803 * 2 ^ 59
def prefixEnd_384803 : Nat := 4983230072969 + 3 ^ 40 * 384803 * 2
def baseEnd_384803 : Nat := 175634574481922835726959

theorem tailTrace_384803 : CollatzResearch.WordTrace tailWord_384803 prefixEnd_384803 175634574481922835726959 := by
  unfold tailWord_384803
  simp only [CollatzResearch.WordTrace]
  refine ⟨14034918424931924965343063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9356612283287949976895375 14034918424931924965343063)
  ·
    refine ⟨21052377637397887448014595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14034918424931924965343063 21052377637397887448014595)
    ·
      refine ⟨31578566456096831172021893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21052377637397887448014595 31578566456096831172021893)
      ·
        refine ⟨5920981210518155844754105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31578566456096831172021893 5920981210518155844754105)
        ·
          refine ⟨4440735907888616883565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5920981210518155844754105 4440735907888616883565579)
          ·
            refine ⟨6661103861832925325348369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440735907888616883565579 6661103861832925325348369)
            ·
              refine ⟨4995827896374693994011277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6661103861832925325348369 4995827896374693994011277)
              ·
                refine ⟨1873435461140510247754229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4995827896374693994011277 1873435461140510247754229)
                ·
                  refine ⟨175634574481922835726959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873435461140510247754229 175634574481922835726959)
                  ·
                    rfl

theorem cell20_384803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_384803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384803 prefixEnd_384803 := by exact prefixLift 384803
  have htrace : WordTrace (prefixWord ++ tailWord_384803) baseStart_384803 baseEnd_384803 := by
    simpa [prefixWord, tailWord_384803, baseEnd_384803] using wordTrace_append hprefix tailTrace_384803
  have hstable : (prefixWord ++ tailWord_384803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384803).length < 2 ^ (prefixWord ++ tailWord_384803).sum := by decide
  have hdescent : baseEnd_384803 < baseStart_384803 := by decide
  rcases family_descends (prefixWord ++ tailWord_384803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384830 : List Nat := [4, 2, 1, 2, 2, 2, 3, 4]
def baseStart_384830 : Nat := 118140960795 + 384830 * 2 ^ 59
def prefixEnd_384830 : Nat := 4983230072969 + 3 ^ 40 * 384830 * 2
def baseEnd_384830 : Nat := 58548966005876913942283

theorem tailTrace_384830 : CollatzResearch.WordTrace tailWord_384830 prefixEnd_384830 58548966005876913942283 := by
  unfold tailWord_384830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754487899479263572071993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9357268797222739051050629 1754487899479263572071993)
  ·
    refine ⟨1315865924609447679053995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1754487899479263572071993 1315865924609447679053995)
    ·
      refine ⟨1973798886914171518580993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315865924609447679053995 1973798886914171518580993)
      ·
        refine ⟨1480349165185628638935745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1973798886914171518580993 1480349165185628638935745)
        ·
          refine ⟨1110261873889221479201809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480349165185628638935745 1110261873889221479201809)
          ·
            refine ⟨832696405416916109401357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110261873889221479201809 832696405416916109401357)
            ·
              refine ⟨312261152031343541025509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832696405416916109401357 312261152031343541025509)
              ·
                refine ⟨58548966005876913942283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312261152031343541025509 58548966005876913942283)
                ·
                  rfl

theorem cell20_384830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_384830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384830 prefixEnd_384830 := by exact prefixLift 384830
  have htrace : WordTrace (prefixWord ++ tailWord_384830) baseStart_384830 baseEnd_384830 := by
    simpa [prefixWord, tailWord_384830, baseEnd_384830] using wordTrace_append hprefix tailTrace_384830
  have hstable : (prefixWord ++ tailWord_384830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384830).length < 2 ^ (prefixWord ++ tailWord_384830).sum := by decide
  have hdescent : baseEnd_384830 < baseStart_384830 := by decide
  rcases family_descends (prefixWord ++ tailWord_384830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384841 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_384841 : Nat := 118140960795 + 384841 * 2 ^ 59
def prefixEnd_384841 : Nat := 4983230072969 + 3 ^ 40 * 384841 * 2
def baseEnd_384841 : Nat := 175651918717363592460137

theorem tailTrace_384841 : CollatzResearch.WordTrace tailWord_384841 prefixEnd_384841 175651918717363592460137 := by
  unfold tailWord_384841
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036304398794257455226377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9357536265862838303484251 14036304398794257455226377)
  ·
    refine ⟨10527228299095693091419783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14036304398794257455226377 10527228299095693091419783)
    ·
      refine ⟨15790842448643539637129675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527228299095693091419783 15790842448643539637129675)
      ·
        refine ⟨23686263672965309455694513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15790842448643539637129675 23686263672965309455694513)
        ·
          refine ⟨17764697754723982091770885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23686263672965309455694513 17764697754723982091770885)
          ·
            refine ⟨3330880829010746642207041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17764697754723982091770885 3330880829010746642207041)
            ·
              refine ⟨2498160621758059981655281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330880829010746642207041 2498160621758059981655281)
              ·
                refine ⟨1873620466318544986241461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498160621758059981655281 1873620466318544986241461)
                ·
                  refine ⟨175651918717363592460137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873620466318544986241461 175651918717363592460137)
                  ·
                    rfl

theorem cell20_384841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_384841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384841 prefixEnd_384841 := by exact prefixLift 384841
  have htrace : WordTrace (prefixWord ++ tailWord_384841) baseStart_384841 baseEnd_384841 := by
    simpa [prefixWord, tailWord_384841, baseEnd_384841] using wordTrace_append hprefix tailTrace_384841
  have hstable : (prefixWord ++ tailWord_384841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384841).length < 2 ^ (prefixWord ++ tailWord_384841).sum := by decide
  have hdescent : baseEnd_384841 < baseStart_384841 := by decide
  rcases family_descends (prefixWord ++ tailWord_384841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384848 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_384848 : Nat := 118140960795 + 384848 * 2 ^ 59
def prefixEnd_384848 : Nat := 4983230072969 + 3 ^ 40 * 384848 * 2
def baseEnd_384848 : Nat := 175655113708102679226775

theorem tailTrace_384848 : CollatzResearch.WordTrace tailWord_384848 prefixEnd_384848 175655113708102679226775 := by
  unfold tailWord_384848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018279854884448825365599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9357706473179265100487465 7018279854884448825365599)
  ·
    refine ⟨10527419782326673238048399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018279854884448825365599 10527419782326673238048399)
    ·
      refine ⟨15791129673490009857072599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527419782326673238048399 15791129673490009857072599)
      ·
        refine ⟨23686694510235014785608899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791129673490009857072599 23686694510235014785608899)
        ·
          refine ⟨35530041765352522178413349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23686694510235014785608899 35530041765352522178413349)
          ·
            refine ⟨6661882831003597908452503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35530041765352522178413349 6661882831003597908452503)
            ·
              refine ⟨9992824246505396862678755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661882831003597908452503 9992824246505396862678755)
              ·
                refine ⟨14989236369758095294018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9992824246505396862678755 14989236369758095294018133)
                ·
                  refine ⟨175655113708102679226775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14989236369758095294018133 175655113708102679226775)
                  ·
                    rfl

theorem cell20_384848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_384848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384848 prefixEnd_384848 := by exact prefixLift 384848
  have htrace : WordTrace (prefixWord ++ tailWord_384848) baseStart_384848 baseEnd_384848 := by
    simpa [prefixWord, tailWord_384848, baseEnd_384848] using wordTrace_append hprefix tailTrace_384848
  have hstable : (prefixWord ++ tailWord_384848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384848).length < 2 ^ (prefixWord ++ tailWord_384848).sum := by decide
  have hdescent : baseEnd_384848 < baseStart_384848 := by decide
  rcases family_descends (prefixWord ++ tailWord_384848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384865 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_384865 : Nat := 118140960795 + 384865 * 2 ^ 59
def prefixEnd_384865 : Nat := 4983230072969 + 3 ^ 40 * 384865 * 2
def baseEnd_384865 : Nat := 175662872971326175660039

theorem tailTrace_384865 : CollatzResearch.WordTrace tailWord_384865 prefixEnd_384865 175662872971326175660039 := by
  unfold tailWord_384865
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037179750707309554100049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9358119833804873036066699 14037179750707309554100049)
  ·
    refine ⟨10527884813030482165575037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14037179750707309554100049 10527884813030482165575037)
    ·
      refine ⟨3947956804886430812090639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10527884813030482165575037 3947956804886430812090639)
      ·
        refine ⟨5921935207329646218135959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3947956804886430812090639 5921935207329646218135959)
        ·
          refine ⟨8882902810994469327203939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921935207329646218135959 8882902810994469327203939)
          ·
            refine ⟨13324354216491703990805909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882902810994469327203939 13324354216491703990805909)
            ·
              refine ⟨624579103898048624569027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13324354216491703990805909 624579103898048624569027)
              ·
                refine ⟨936868655847072936853541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624579103898048624569027 936868655847072936853541)
                ·
                  refine ⟨175662872971326175660039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936868655847072936853541 175662872971326175660039)
                  ·
                    rfl

theorem cell20_384865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_384865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384865 prefixEnd_384865 := by exact prefixLift 384865
  have htrace : WordTrace (prefixWord ++ tailWord_384865) baseStart_384865 baseEnd_384865 := by
    simpa [prefixWord, tailWord_384865, baseEnd_384865] using wordTrace_append hprefix tailTrace_384865
  have hstable : (prefixWord ++ tailWord_384865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384865).length < 2 ^ (prefixWord ++ tailWord_384865).sum := by decide
  have hdescent : baseEnd_384865 < baseStart_384865 := by decide
  rcases family_descends (prefixWord ++ tailWord_384865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384872 : List Nat := [2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_384872 : Nat := 118140960795 + 384872 * 2 ^ 59
def prefixEnd_384872 : Nat := 4983230072969 + 3 ^ 40 * 384872 * 2
def baseEnd_384872 : Nat := 58555355987355087475559

theorem tailTrace_384872 : CollatzResearch.WordTrace tailWord_384872 prefixEnd_384872 58555355987355087475559 := by
  unfold tailWord_384872
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018717530840974874802435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9358290041121299833069913 7018717530840974874802435)
  ·
    refine ⟨10528076296261462312203653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018717530840974874802435 10528076296261462312203653)
    ·
      refine ⟨1974014305549024183538185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10528076296261462312203653 1974014305549024183538185)
      ·
        refine ⟨1480510729161768137653639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1974014305549024183538185 1480510729161768137653639)
        ·
          refine ⟨2220766093742652206480459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480510729161768137653639 2220766093742652206480459)
          ·
            refine ⟨3331149140613978309720689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220766093742652206480459 3331149140613978309720689)
            ·
              refine ⟨2498361855460483732290517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3331149140613978309720689 2498361855460483732290517)
              ·
                refine ⟨58555355987355087475559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2498361855460483732290517 58555355987355087475559)
                ·
                  rfl

theorem cell20_384872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_384872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384872 prefixEnd_384872 := by exact prefixLift 384872
  have htrace : WordTrace (prefixWord ++ tailWord_384872) baseStart_384872 baseEnd_384872 := by
    simpa [prefixWord, tailWord_384872, baseEnd_384872] using wordTrace_append hprefix tailTrace_384872
  have hstable : (prefixWord ++ tailWord_384872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384872).length < 2 ^ (prefixWord ++ tailWord_384872).sum := by decide
  have hdescent : baseEnd_384872 < baseStart_384872 := by decide
  rcases family_descends (prefixWord ++ tailWord_384872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384899 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 2]
def baseStart_384899 : Nat := 118140960795 + 384899 * 2 ^ 59
def prefixEnd_384899 : Nat := 4983230072969 + 3 ^ 40 * 384899 * 2
def baseEnd_384899 : Nat := 175678391497773168526567

theorem tailTrace_384899 : CollatzResearch.WordTrace tailWord_384899 prefixEnd_384899 175678391497773168526567 := by
  unfold tailWord_384899
  simp only [CollatzResearch.WordTrace]
  refine ⟨14038419832584133360837751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9358946555056088907225167 14038419832584133360837751)
  ·
    refine ⟨21057629748876200041256627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14038419832584133360837751 21057629748876200041256627)
    ·
      refine ⟨31586444623314300061884941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21057629748876200041256627 31586444623314300061884941)
      ·
        refine ⟨11844916733742862523206853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31586444623314300061884941 11844916733742862523206853)
        ·
          refine ⟨2220921887576786723101285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11844916733742862523206853 2220921887576786723101285)
          ·
            refine ⟨416422853920647510581491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2220921887576786723101285 416422853920647510581491)
            ·
              refine ⟨624634280880971265872237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416422853920647510581491 624634280880971265872237)
              ·
                refine ⟨234237855330364224702089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624634280880971265872237 234237855330364224702089)
                ·
                  refine ⟨175678391497773168526567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234237855330364224702089 175678391497773168526567)
                  ·
                    rfl

theorem cell20_384899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 2].length) (baseStart_384899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384899 prefixEnd_384899 := by exact prefixLift 384899
  have htrace : WordTrace (prefixWord ++ tailWord_384899) baseStart_384899 baseEnd_384899 := by
    simpa [prefixWord, tailWord_384899, baseEnd_384899] using wordTrace_append hprefix tailTrace_384899
  have hstable : (prefixWord ++ tailWord_384899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384899).length < 2 ^ (prefixWord ++ tailWord_384899).sum := by decide
  have hdescent : baseEnd_384899 < baseStart_384899 := by decide
  rcases family_descends (prefixWord ++ tailWord_384899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384906 : List Nat := [3, 1, 2, 4, 3, 1, 6]
def baseStart_384906 : Nat := 118140960795 + 384906 * 2 ^ 59
def prefixEnd_384906 : Nat := 4983230072969 + 3 ^ 40 * 384906 * 2
def baseEnd_384906 : Nat := 19520176276501361699245

theorem tailTrace_384906 : CollatzResearch.WordTrace tailWord_384906 prefixEnd_384906 19520176276501361699245 := by
  unfold tailWord_384906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509668785889693389085643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9359116762372515704228381 3509668785889693389085643)
  ·
    refine ⟨5264503178834540083628465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509668785889693389085643 5264503178834540083628465)
    ·
      refine ⟨3948377384125905062721349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5264503178834540083628465 3948377384125905062721349)
      ·
        refine ⟨740320759523607199260253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3948377384125905062721349 740320759523607199260253)
        ·
          refine ⟨277620284821352699722595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740320759523607199260253 277620284821352699722595)
          ·
            refine ⟨416430427232029049583893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277620284821352699722595 416430427232029049583893)
            ·
              refine ⟨19520176276501361699245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 416430427232029049583893 19520176276501361699245)
              ·
                rfl

theorem cell20_384906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 6].length) (baseStart_384906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384906 prefixEnd_384906 := by exact prefixLift 384906
  have htrace : WordTrace (prefixWord ++ tailWord_384906) baseStart_384906 baseEnd_384906 := by
    simpa [prefixWord, tailWord_384906, baseEnd_384906] using wordTrace_append hprefix tailTrace_384906
  have hstable : (prefixWord ++ tailWord_384906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384906).length < 2 ^ (prefixWord ++ tailWord_384906).sum := by decide
  have hdescent : baseEnd_384906 < baseStart_384906 := by decide
  rcases family_descends (prefixWord ++ tailWord_384906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384916 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 2]
def baseStart_384916 : Nat := 118140960795 + 384916 * 2 ^ 59
def prefixEnd_384916 : Nat := 4983230072969 + 3 ^ 40 * 384916 * 2
def baseEnd_384916 : Nat := 175686150760996664959831

theorem tailTrace_384916 : CollatzResearch.WordTrace tailWord_384916 prefixEnd_384916 175686150760996664959831 := by
  unfold tailWord_384916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7019519936761272632103301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9359359915681696842804401 7019519936761272632103301)
  ·
    refine ⟨1316159988142738618519369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7019519936761272632103301 1316159988142738618519369)
    ·
      refine ⟨987119991107053963889527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1316159988142738618519369 987119991107053963889527)
      ·
        refine ⟨1480679986660580945834291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987119991107053963889527 1480679986660580945834291)
        ·
          refine ⟨2221019979990871418751437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480679986660580945834291 2221019979990871418751437)
          ·
            refine ⟨832882492496576782031789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2221019979990871418751437 832882492496576782031789)
            ·
              refine ⟨312330934686216293261921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832882492496576782031789 312330934686216293261921)
              ·
                refine ⟨234248201014662219946441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312330934686216293261921 234248201014662219946441)
                ·
                  refine ⟨175686150760996664959831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234248201014662219946441 175686150760996664959831)
                  ·
                    rfl

theorem cell20_384916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_384916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384916 prefixEnd_384916 := by exact prefixLift 384916
  have htrace : WordTrace (prefixWord ++ tailWord_384916) baseStart_384916 baseEnd_384916 := by
    simpa [prefixWord, tailWord_384916, baseEnd_384916] using wordTrace_append hprefix tailTrace_384916
  have hstable : (prefixWord ++ tailWord_384916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384916).length < 2 ^ (prefixWord ++ tailWord_384916).sum := by decide
  have hdescent : baseEnd_384916 < baseStart_384916 := by decide
  rcases family_descends (prefixWord ++ tailWord_384916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384917 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_384917 : Nat := 118140960795 + 384917 * 2 ^ 59
def prefixEnd_384917 : Nat := 4983230072969 + 3 ^ 40 * 384917 * 2
def baseEnd_384917 : Nat := 175686607188245105926493

theorem tailTrace_384917 : CollatzResearch.WordTrace tailWord_384917 prefixEnd_384917 175686607188245105926493 := by
  unfold tailWord_384917
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039076346518922434993005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9359384231012614956662003 14039076346518922434993005)
  ·
    refine ⟨5264653629944595913122377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14039076346518922434993005 5264653629944595913122377)
    ·
      refine ⟨3948490222458446934841783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5264653629944595913122377 3948490222458446934841783)
      ·
        refine ⟨5922735333687670402262675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3948490222458446934841783 5922735333687670402262675)
        ·
          refine ⟨8884103000531505603394013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5922735333687670402262675 8884103000531505603394013)
          ·
            refine ⟨3331538625199314601272755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8884103000531505603394013 3331538625199314601272755)
            ·
              refine ⟨4997307937798971901909133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331538625199314601272755 4997307937798971901909133)
              ·
                refine ⟨1873990476674614463215925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4997307937798971901909133 1873990476674614463215925)
                ·
                  refine ⟨175686607188245105926493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873990476674614463215925 175686607188245105926493)
                  ·
                    rfl

theorem cell20_384917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_384917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384917 prefixEnd_384917 := by exact prefixLift 384917
  have htrace : WordTrace (prefixWord ++ tailWord_384917) baseStart_384917 baseEnd_384917 := by
    simpa [prefixWord, tailWord_384917, baseEnd_384917] using wordTrace_append hprefix tailTrace_384917
  have hstable : (prefixWord ++ tailWord_384917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384917).length < 2 ^ (prefixWord ++ tailWord_384917).sum := by decide
  have hdescent : baseEnd_384917 < baseStart_384917 := by decide
  rcases family_descends (prefixWord ++ tailWord_384917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384926 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_384926 : Nat := 118140960795 + 384926 * 2 ^ 59
def prefixEnd_384926 : Nat := 4983230072969 + 3 ^ 40 * 384926 * 2
def baseEnd_384926 : Nat := 175690715033481074626457

theorem tailTrace_384926 : CollatzResearch.WordTrace tailWord_384926 prefixEnd_384926 175690715033481074626457 := by
  unfold tailWord_384926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754925575435789621508829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9359603068990877981380421 1754925575435789621508829)
  ·
    refine ⟨658097090788421108065811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1754925575435789621508829 658097090788421108065811)
    ·
      refine ⟨987145636182631662098717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658097090788421108065811 987145636182631662098717)
      ·
        refine ⟨370179613568486873287019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 987145636182631662098717 370179613568486873287019)
        ·
          refine ⟨555269420352730309930529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370179613568486873287019 555269420352730309930529)
          ·
            refine ⟨416452065264547732447897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555269420352730309930529 416452065264547732447897)
            ·
              refine ⟨312339048948410799335923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416452065264547732447897 312339048948410799335923)
              ·
                refine ⟨468508573422616199003885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312339048948410799335923 468508573422616199003885)
                ·
                  refine ⟨175690715033481074626457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468508573422616199003885 175690715033481074626457)
                  ·
                    rfl

theorem cell20_384926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_384926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384926 prefixEnd_384926 := by exact prefixLift 384926
  have htrace : WordTrace (prefixWord ++ tailWord_384926) baseStart_384926 baseEnd_384926 := by
    simpa [prefixWord, tailWord_384926, baseEnd_384926] using wordTrace_append hprefix tailTrace_384926
  have hstable : (prefixWord ++ tailWord_384926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384926).length < 2 ^ (prefixWord ++ tailWord_384926).sum := by decide
  have hdescent : baseEnd_384926 < baseStart_384926 := by decide
  rcases family_descends (prefixWord ++ tailWord_384926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384927 : List Nat := [1, 1, 2, 5, 3, 1, 2, 5]
def baseStart_384927 : Nat := 118140960795 + 384927 * 2 ^ 59
def prefixEnd_384927 : Nat := 4983230072969 + 3 ^ 40 * 384927 * 2
def baseEnd_384927 : Nat := 58563723820243171864373

theorem tailTrace_384927 : CollatzResearch.WordTrace tailWord_384927 prefixEnd_384927 58563723820243171864373 := by
  unfold tailWord_384927
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039441076482694142857035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9359627384321796095238023 14039441076482694142857035)
  ·
    refine ⟨21059161614724041214285553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14039441076482694142857035 21059161614724041214285553)
    ·
      refine ⟨15794371211043030910714165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21059161614724041214285553 15794371211043030910714165)
      ·
        refine ⟨1480722301035284147879453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15794371211043030910714165 1480722301035284147879453)
        ·
          refine ⟨555270862888231555454795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1480722301035284147879453 555270862888231555454795)
          ·
            refine ⟨832906294332347333182193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555270862888231555454795 832906294332347333182193)
            ·
              refine ⟨624679720749260499886645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832906294332347333182193 624679720749260499886645)
              ·
                refine ⟨58563723820243171864373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624679720749260499886645 58563723820243171864373)
                ·
                  rfl

theorem cell20_384927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_384927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384927 prefixEnd_384927 := by exact prefixLift 384927
  have htrace : WordTrace (prefixWord ++ tailWord_384927) baseStart_384927 baseEnd_384927 := by
    simpa [prefixWord, tailWord_384927, baseEnd_384927] using wordTrace_append hprefix tailTrace_384927
  have hstable : (prefixWord ++ tailWord_384927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384927).length < 2 ^ (prefixWord ++ tailWord_384927).sum := by decide
  have hdescent : baseEnd_384927 < baseStart_384927 := by decide
  rcases family_descends (prefixWord ++ tailWord_384927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384972 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_384972 : Nat := 118140960795 + 384972 * 2 ^ 59
def prefixEnd_384972 : Nat := 4983230072969 + 3 ^ 40 * 384972 * 2
def baseEnd_384972 : Nat := 175711710686909359092935

theorem tailTrace_384972 : CollatzResearch.WordTrace tailWord_384972 prefixEnd_384972 175711710686909359092935 := by
  unfold tailWord_384972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020541180659833414122585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9360721574213111218830113 7020541180659833414122585)
  ·
    refine ⟨5265405885494875060591939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7020541180659833414122585 5265405885494875060591939)
    ·
      refine ⟨7898108828242312590887909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5265405885494875060591939 7898108828242312590887909)
      ·
        refine ⟨1480895405295433610791483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7898108828242312590887909 1480895405295433610791483)
        ·
          refine ⟨2221343107943150416187225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480895405295433610791483 2221343107943150416187225)
          ·
            refine ⟨1666007330957362812140419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221343107943150416187225 1666007330957362812140419)
            ·
              refine ⟨2499010996436044218210629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666007330957362812140419 2499010996436044218210629)
              ·
                refine ⟨468564561831758290914493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2499010996436044218210629 468564561831758290914493)
                ·
                  refine ⟨175711710686909359092935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468564561831758290914493 175711710686909359092935)
                  ·
                    rfl

theorem cell20_384972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_384972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384972 prefixEnd_384972 := by exact prefixLift 384972
  have htrace : WordTrace (prefixWord ++ tailWord_384972) baseStart_384972 baseEnd_384972 := by
    simpa [prefixWord, tailWord_384972, baseEnd_384972] using wordTrace_append hprefix tailTrace_384972
  have hstable : (prefixWord ++ tailWord_384972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384972).length < 2 ^ (prefixWord ++ tailWord_384972).sum := by decide
  have hdescent : baseEnd_384972 < baseStart_384972 := by decide
  rcases family_descends (prefixWord ++ tailWord_384972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385034 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_385034 : Nat := 118140960795 + 385034 * 2 ^ 59
def prefixEnd_385034 : Nat := 4983230072969 + 3 ^ 40 * 385034 * 2
def baseEnd_385034 : Nat := 175740009176312699026015

theorem tailTrace_385034 : CollatzResearch.WordTrace tailWord_385034 prefixEnd_385034 175740009176312699026015 := by
  unfold tailWord_385034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510835921773762854250539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9362229124730034278001437 3510835921773762854250539)
  ·
    refine ⟨5266253882660644281375809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3510835921773762854250539 5266253882660644281375809)
    ·
      refine ⟨3949690411995483211031857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5266253882660644281375809 3949690411995483211031857)
      ·
        refine ⟨2962267808996612408273893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3949690411995483211031857 2962267808996612408273893)
        ·
          refine ⟨555425214186864826551355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2962267808996612408273893 555425214186864826551355)
          ·
            refine ⟨833137821280297239827033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555425214186864826551355 833137821280297239827033)
            ·
              refine ⟨624853365960222929870275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833137821280297239827033 624853365960222929870275)
              ·
                refine ⟨937280048940334394805413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624853365960222929870275 937280048940334394805413)
                ·
                  refine ⟨175740009176312699026015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937280048940334394805413 175740009176312699026015)
                  ·
                    rfl

theorem cell20_385034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_385034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385034 prefixEnd_385034 := by exact prefixLift 385034
  have htrace : WordTrace (prefixWord ++ tailWord_385034) baseStart_385034 baseEnd_385034 := by
    simpa [prefixWord, tailWord_385034, baseEnd_385034] using wordTrace_append hprefix tailTrace_385034
  have hstable : (prefixWord ++ tailWord_385034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385034).length < 2 ^ (prefixWord ++ tailWord_385034).sum := by decide
  have hdescent : baseEnd_385034 < baseStart_385034 := by decide
  rcases family_descends (prefixWord ++ tailWord_385034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385072 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 2]
def baseStart_385072 : Nat := 118140960795 + 385072 * 2 ^ 59
def prefixEnd_385072 : Nat := 4983230072969 + 3 ^ 40 * 385072 * 2
def baseEnd_385072 : Nat := 175757353411753455759193

theorem tailTrace_385072 : CollatzResearch.WordTrace tailWord_385072 prefixEnd_385072 175757353411753455759193 := by
  unfold tailWord_385072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022364830478691953442735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9363153107304922604590313 7022364830478691953442735)
  ·
    refine ⟨10533547245718037930164103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7022364830478691953442735 10533547245718037930164103)
    ·
      refine ⟨15800320868577056895246155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10533547245718037930164103 15800320868577056895246155)
      ·
        refine ⟨23700481302865585342869233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15800320868577056895246155 23700481302865585342869233)
        ·
          refine ⟨17775360977149189007151925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23700481302865585342869233 17775360977149189007151925)
          ·
            refine ⟨1666440091607736469420493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17775360977149189007151925 1666440091607736469420493)
            ·
              refine ⟨624915034352901176032685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666440091607736469420493 624915034352901176032685)
              ·
                refine ⟨234343137882337941012257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624915034352901176032685 234343137882337941012257)
                ·
                  refine ⟨175757353411753455759193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234343137882337941012257 175757353411753455759193)
                  ·
                    rfl

theorem cell20_385072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_385072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385072 prefixEnd_385072 := by exact prefixLift 385072
  have htrace : WordTrace (prefixWord ++ tailWord_385072) baseStart_385072 baseEnd_385072 := by
    simpa [prefixWord, tailWord_385072, baseEnd_385072] using wordTrace_append hprefix tailTrace_385072
  have hstable : (prefixWord ++ tailWord_385072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385072).length < 2 ^ (prefixWord ++ tailWord_385072).sum := by decide
  have hdescent : baseEnd_385072 < baseStart_385072 := by decide
  rcases family_descends (prefixWord ++ tailWord_385072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385114 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_385114 : Nat := 118140960795 + 385114 * 2 ^ 59
def prefixEnd_385114 : Nat := 4983230072969 + 3 ^ 40 * 385114 * 2
def baseEnd_385114 : Nat := 175776523356187976359021

theorem tailTrace_385114 : CollatzResearch.WordTrace tailWord_385114 prefixEnd_385114 175776523356187976359021 := by
  unfold tailWord_385114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511565381701306269978599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9364174351203483386609597 3511565381701306269978599)
  ·
    refine ⟨5267348072551959404967899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3511565381701306269978599 5267348072551959404967899)
    ·
      refine ⟨7901022108827939107451849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5267348072551959404967899 7901022108827939107451849)
      ·
        refine ⟨5925766581620954330588887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7901022108827939107451849 5925766581620954330588887)
        ·
          refine ⟨8888649872431431495883331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5925766581620954330588887 8888649872431431495883331)
          ·
            refine ⟨13332974808647147243824997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888649872431431495883331 13332974808647147243824997)
            ·
              refine ⟨2499932776621340108217187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13332974808647147243824997 2499932776621340108217187)
              ·
                refine ⟨3749899164932010162325781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499932776621340108217187 3749899164932010162325781)
                ·
                  refine ⟨175776523356187976359021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3749899164932010162325781 175776523356187976359021)
                  ·
                    rfl

theorem cell20_385114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_385114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385114 prefixEnd_385114 := by exact prefixLift 385114
  have htrace : WordTrace (prefixWord ++ tailWord_385114) baseStart_385114 baseEnd_385114 := by
    simpa [prefixWord, tailWord_385114, baseEnd_385114] using wordTrace_append hprefix tailTrace_385114
  have hstable : (prefixWord ++ tailWord_385114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385114).length < 2 ^ (prefixWord ++ tailWord_385114).sum := by decide
  have hdescent : baseEnd_385114 < baseStart_385114 := by decide
  rcases family_descends (prefixWord ++ tailWord_385114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385117 : List Nat := [1, 4, 4, 1, 1, 1, 2, 6]
def baseStart_385117 : Nat := 118140960795 + 385117 * 2 ^ 59
def prefixEnd_385117 : Nat := 4983230072969 + 3 ^ 40 * 385117 * 2
def baseEnd_385117 : Nat := 58592630879311099753003

theorem tailTrace_385117 : CollatzResearch.WordTrace tailWord_385117 prefixEnd_385117 58592630879311099753003 := by
  unfold tailWord_385117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14046370945794356592273605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9364247297196237728182403 14046370945794356592273605)
  ·
    refine ⟨2633694552336441861051301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14046370945794356592273605 2633694552336441861051301)
    ·
      refine ⟨493817728563082848947119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2633694552336441861051301 493817728563082848947119)
      ·
        refine ⟨740726592844624273420679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493817728563082848947119 740726592844624273420679)
        ·
          refine ⟨1111089889266936410131019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740726592844624273420679 1111089889266936410131019)
          ·
            refine ⟨1666634833900404615196529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111089889266936410131019 1666634833900404615196529)
            ·
              refine ⟨1249976125425303461397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666634833900404615196529 1249976125425303461397397)
              ·
                refine ⟨58592630879311099753003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1249976125425303461397397 58592630879311099753003)
                ·
                  rfl

theorem cell20_385117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_385117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385117 prefixEnd_385117 := by exact prefixLift 385117
  have htrace : WordTrace (prefixWord ++ tailWord_385117) baseStart_385117 baseEnd_385117 := by
    simpa [prefixWord, tailWord_385117, baseEnd_385117] using wordTrace_append hprefix tailTrace_385117
  have hstable : (prefixWord ++ tailWord_385117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385117).length < 2 ^ (prefixWord ++ tailWord_385117).sum := by decide
  have hdescent : baseEnd_385117 < baseStart_385117 := by decide
  rcases family_descends (prefixWord ++ tailWord_385117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385148 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 2]
def baseStart_385148 : Nat := 118140960795 + 385148 * 2 ^ 59
def prefixEnd_385148 : Nat := 4983230072969 + 3 ^ 40 * 385148 * 2
def baseEnd_385148 : Nat := 175792041882634969225549

theorem tailTrace_385148 : CollatzResearch.WordTrace tailWord_385148 prefixEnd_385148 175792041882634969225549 := by
  unfold tailWord_385148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7023750804341024443326049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9365001072454699257768065 7023750804341024443326049)
  ·
    refine ⟨5267813103255768332494537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7023750804341024443326049 5267813103255768332494537)
    ·
      refine ⟨3950859827441826249370903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5267813103255768332494537 3950859827441826249370903)
      ·
        refine ⟨5926289741162739374056355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950859827441826249370903 5926289741162739374056355)
        ·
          refine ⟨8889434611744109061084533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5926289741162739374056355 8889434611744109061084533)
          ·
            refine ⟨833384494851010224476675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8889434611744109061084533 833384494851010224476675)
            ·
              refine ⟨1250076742276515336715013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833384494851010224476675 1250076742276515336715013)
              ·
                refine ⟨234389389176846625634065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1250076742276515336715013 234389389176846625634065)
                ·
                  refine ⟨175792041882634969225549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234389389176846625634065 175792041882634969225549)
                  ·
                    rfl

theorem cell20_385148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_385148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385148 prefixEnd_385148 := by exact prefixLift 385148
  have htrace : WordTrace (prefixWord ++ tailWord_385148) baseStart_385148 baseEnd_385148 := by
    simpa [prefixWord, tailWord_385148, baseEnd_385148] using wordTrace_append hprefix tailTrace_385148
  have hstable : (prefixWord ++ tailWord_385148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385148).length < 2 ^ (prefixWord ++ tailWord_385148).sum := by decide
  have hdescent : baseEnd_385148 < baseStart_385148 := by decide
  rcases family_descends (prefixWord ++ tailWord_385148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385152 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_385152 : Nat := 118140960795 + 385152 * 2 ^ 59
def prefixEnd_385152 : Nat := 4983230072969 + 3 ^ 40 * 385152 * 2
def baseEnd_385152 : Nat := 175793867591628733092199

theorem tailTrace_385152 : CollatzResearch.WordTrace tailWord_385152 prefixEnd_385152 175793867591628733092199 := by
  unfold tailWord_385152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7023823750333778784898855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9365098333778371713198473 7023823750333778784898855)
  ·
    refine ⟨10535735625500668177348283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7023823750333778784898855 10535735625500668177348283)
    ·
      refine ⟨15803603438251002266022425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10535735625500668177348283 15803603438251002266022425)
      ·
        refine ⟨11852702578688251699516819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15803603438251002266022425 11852702578688251699516819)
        ·
          refine ⟨17779053868032377549275229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11852702578688251699516819 17779053868032377549275229)
          ·
            refine ⟨6667145200512141580978211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17779053868032377549275229 6667145200512141580978211)
            ·
              refine ⟨10000717800768212371467317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667145200512141580978211 10000717800768212371467317)
              ·
                refine ⟨937567293822019909825061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10000717800768212371467317 937567293822019909825061)
                ·
                  refine ⟨175793867591628733092199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937567293822019909825061 175793867591628733092199)
                  ·
                    rfl

theorem cell20_385152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_385152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385152 prefixEnd_385152 := by exact prefixLift 385152
  have htrace : WordTrace (prefixWord ++ tailWord_385152) baseStart_385152 baseEnd_385152 := by
    simpa [prefixWord, tailWord_385152, baseEnd_385152] using wordTrace_append hprefix tailTrace_385152
  have hstable : (prefixWord ++ tailWord_385152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385152).length < 2 ^ (prefixWord ++ tailWord_385152).sum := by decide
  have hdescent : baseEnd_385152 < baseStart_385152 := by decide
  rcases family_descends (prefixWord ++ tailWord_385152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385162 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_385162 : Nat := 118140960795 + 385162 * 2 ^ 59
def prefixEnd_385162 : Nat := 4983230072969 + 3 ^ 40 * 385162 * 2
def baseEnd_385162 : Nat := 175798431864113142758825

theorem tailTrace_385162 : CollatzResearch.WordTrace tailWord_385162 prefixEnd_385162 175798431864113142758825 := by
  unfold tailWord_385162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512003057657832319415435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9365341487087552851774493 3512003057657832319415435)
  ·
    refine ⟨5268004586486748479123153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512003057657832319415435 5268004586486748479123153)
    ·
      refine ⟨3951003439865061359342365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5268004586486748479123153 3951003439865061359342365)
      ·
        refine ⟨1481626289949398009753387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3951003439865061359342365 1481626289949398009753387)
        ·
          refine ⟨2222439434924097014630081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481626289949398009753387 2222439434924097014630081)
          ·
            refine ⟨1666829576193072760972561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222439434924097014630081 1666829576193072760972561)
            ·
              refine ⟨1250122182144804570729421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666829576193072760972561 1250122182144804570729421)
              ·
                refine ⟨468795818304301714023533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250122182144804570729421 468795818304301714023533)
                ·
                  refine ⟨175798431864113142758825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468795818304301714023533 175798431864113142758825)
                  ·
                    rfl

theorem cell20_385162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_385162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385162 prefixEnd_385162 := by exact prefixLift 385162
  have htrace : WordTrace (prefixWord ++ tailWord_385162) baseStart_385162 baseEnd_385162 := by
    simpa [prefixWord, tailWord_385162, baseEnd_385162] using wordTrace_append hprefix tailTrace_385162
  have hstable : (prefixWord ++ tailWord_385162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385162).length < 2 ^ (prefixWord ++ tailWord_385162).sum := by decide
  have hdescent : baseEnd_385162 < baseStart_385162 := by decide
  rcases family_descends (prefixWord ++ tailWord_385162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385182 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_385182 : Nat := 118140960795 + 385182 * 2 ^ 59
def prefixEnd_385182 : Nat := 4983230072969 + 3 ^ 40 * 385182 * 2
def baseEnd_385182 : Nat := 175807560409081962092077

theorem tailTrace_385182 : CollatzResearch.WordTrace tailWord_385182 prefixEnd_385182 175807560409081962092077 := by
  unfold tailWord_385182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756092711319859086673725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9365827793705915128926533 1756092711319859086673725)
  ·
    refine ⟨658534766744947157502647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1756092711319859086673725 658534766744947157502647)
    ·
      refine ⟨987802150117420736253971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658534766744947157502647 987802150117420736253971)
      ·
        refine ⟨1481703225176131104380957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987802150117420736253971 1481703225176131104380957)
        ·
          refine ⟨555638709441049164142859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1481703225176131104380957 555638709441049164142859)
          ·
            refine ⟨833458064161573746214289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555638709441049164142859 833458064161573746214289)
            ·
              refine ⟨625093548121180309660717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833458064161573746214289 625093548121180309660717)
              ·
                refine ⟨234410080545442616122769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 625093548121180309660717 234410080545442616122769)
                ·
                  refine ⟨175807560409081962092077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234410080545442616122769 175807560409081962092077)
                  ·
                    rfl

theorem cell20_385182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_385182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385182 prefixEnd_385182 := by exact prefixLift 385182
  have htrace : WordTrace (prefixWord ++ tailWord_385182) baseStart_385182 baseEnd_385182 := by
    simpa [prefixWord, tailWord_385182, baseEnd_385182] using wordTrace_append hprefix tailTrace_385182
  have hstable : (prefixWord ++ tailWord_385182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385182).length < 2 ^ (prefixWord ++ tailWord_385182).sum := by decide
  have hdescent : baseEnd_385182 < baseStart_385182 := by decide
  rcases family_descends (prefixWord ++ tailWord_385182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385207 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_385207 : Nat := 118140960795 + 385207 * 2 ^ 59
def prefixEnd_385207 : Nat := 4983230072969 + 3 ^ 40 * 385207 * 2
def baseEnd_385207 : Nat := 175818971090292986258641

theorem tailTrace_385207 : CollatzResearch.WordTrace tailWord_385207 prefixEnd_385207 175818971090292986258641 := by
  unfold tailWord_385207
  simp only [CollatzResearch.WordTrace]
  refine ⟨14049653515468301963049875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9366435676978867975366583 14049653515468301963049875)
  ·
    refine ⟨21074480273202452944574813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14049653515468301963049875 21074480273202452944574813)
    ·
      refine ⟨7902930102450919854215555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21074480273202452944574813 7902930102450919854215555)
      ·
        refine ⟨11854395153676379781323333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7902930102450919854215555 11854395153676379781323333)
        ·
          refine ⟨2222699091314321208998125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11854395153676379781323333 2222699091314321208998125)
          ·
            refine ⟨833512159242870453374297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2222699091314321208998125 833512159242870453374297)
            ·
              refine ⟨625134119432152840030723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833512159242870453374297 625134119432152840030723)
              ·
                refine ⟨937701179148229260046085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625134119432152840030723 937701179148229260046085)
                ·
                  refine ⟨175818971090292986258641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937701179148229260046085 175818971090292986258641)
                  ·
                    rfl

theorem cell20_385207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_385207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385207 prefixEnd_385207 := by exact prefixLift 385207
  have htrace : WordTrace (prefixWord ++ tailWord_385207) baseStart_385207 baseEnd_385207 := by
    simpa [prefixWord, tailWord_385207, baseEnd_385207] using wordTrace_append hprefix tailTrace_385207
  have hstable : (prefixWord ++ tailWord_385207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385207).length < 2 ^ (prefixWord ++ tailWord_385207).sum := by decide
  have hdescent : baseEnd_385207 < baseStart_385207 := by decide
  rcases family_descends (prefixWord ++ tailWord_385207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385221 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_385221 : Nat := 118140960795 + 385221 * 2 ^ 59
def prefixEnd_385221 : Nat := 4983230072969 + 3 ^ 40 * 385221 * 2
def baseEnd_385221 : Nat := 175825361071771159791917

theorem tailTrace_385221 : CollatzResearch.WordTrace tailWord_385221 prefixEnd_385221 175825361071771159791917 := by
  unfold tailWord_385221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050164137417582354059517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9366776091611721569373011 14050164137417582354059517)
  ·
    refine ⟨5268811551531593382772319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14050164137417582354059517 5268811551531593382772319)
    ·
      refine ⟨7903217327297390074158479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268811551531593382772319 7903217327297390074158479)
      ·
        refine ⟨11854825990946085111237719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903217327297390074158479 11854825990946085111237719)
        ·
          refine ⟨17782238986419127666856579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11854825990946085111237719 17782238986419127666856579)
          ·
            refine ⟨26673358479628691500284869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17782238986419127666856579 26673358479628691500284869)
            ·
              refine ⟨5001254714930379656303413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26673358479628691500284869 5001254714930379656303413)
              ·
                refine ⟨468867629524723092778445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5001254714930379656303413 468867629524723092778445)
                ·
                  refine ⟨175825361071771159791917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468867629524723092778445 175825361071771159791917)
                  ·
                    rfl

theorem cell20_385221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_385221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385221 prefixEnd_385221 := by exact prefixLift 385221
  have htrace : WordTrace (prefixWord ++ tailWord_385221) baseStart_385221 baseEnd_385221 := by
    simpa [prefixWord, tailWord_385221, baseEnd_385221] using wordTrace_append hprefix tailTrace_385221
  have hstable : (prefixWord ++ tailWord_385221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385221).length < 2 ^ (prefixWord ++ tailWord_385221).sum := by decide
  have hdescent : baseEnd_385221 < baseStart_385221 := by decide
  rcases family_descends (prefixWord ++ tailWord_385221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385259 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_385259 : Nat := 118140960795 + 385259 * 2 ^ 59
def prefixEnd_385259 : Nat := 4983230072969 + 3 ^ 40 * 385259 * 2
def baseEnd_385259 : Nat := 175842705307211916525095

theorem tailTrace_385259 : CollatzResearch.WordTrace tailWord_385259 prefixEnd_385259 175842705307211916525095 := by
  unfold tailWord_385259
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051550111279914843942831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9367700074186609895961887 14051550111279914843942831)
  ·
    refine ⟨21077325166919872265914247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14051550111279914843942831 21077325166919872265914247)
    ·
      refine ⟨31615987750379808398871371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21077325166919872265914247 31615987750379808398871371)
      ·
        refine ⟨47423981625569712598307057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31615987750379808398871371 47423981625569712598307057)
        ·
          refine ⟨35567986219177284448730293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47423981625569712598307057 35567986219177284448730293)
          ·
            refine ⟨3334498708047870417068465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35567986219177284448730293 3334498708047870417068465)
            ·
              refine ⟨2500874031035902812801349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3334498708047870417068465 2500874031035902812801349)
              ·
                refine ⟨468913880819231777400253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2500874031035902812801349 468913880819231777400253)
                ·
                  refine ⟨175842705307211916525095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468913880819231777400253 175842705307211916525095)
                  ·
                    rfl

theorem cell20_385259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_385259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385259 prefixEnd_385259 := by exact prefixLift 385259
  have htrace : WordTrace (prefixWord ++ tailWord_385259) baseStart_385259 baseEnd_385259 := by
    simpa [prefixWord, tailWord_385259, baseEnd_385259] using wordTrace_append hprefix tailTrace_385259
  have hstable : (prefixWord ++ tailWord_385259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385259).length < 2 ^ (prefixWord ++ tailWord_385259).sum := by decide
  have hdescent : baseEnd_385259 < baseStart_385259 := by decide
  rcases family_descends (prefixWord ++ tailWord_385259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385276 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_385276 : Nat := 118140960795 + 385276 * 2 ^ 59
def prefixEnd_385276 : Nat := 4983230072969 + 3 ^ 40 * 385276 * 2
def baseEnd_385276 : Nat := 175850464570435412958359

theorem tailTrace_385276 : CollatzResearch.WordTrace tailWord_385276 prefixEnd_385276 175850464570435412958359 := by
  unfold tailWord_385276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026085076109163373655841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9368113434812217831541121 7026085076109163373655841)
  ·
    refine ⟨5269563807081872530241881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7026085076109163373655841 5269563807081872530241881)
    ·
      refine ⟨3952172855311404397681411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5269563807081872530241881 3952172855311404397681411)
      ·
        refine ⟨5928259282967106596522117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952172855311404397681411 5928259282967106596522117)
        ·
          refine ⟨1111548615556332486847897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5928259282967106596522117 1111548615556332486847897)
          ·
            refine ⟨833661461667249365135923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1111548615556332486847897 833661461667249365135923)
            ·
              refine ⟨1250492192500874047703885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833661461667249365135923 1250492192500874047703885)
              ·
                refine ⟨468934572187827767888957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250492192500874047703885 468934572187827767888957)
                ·
                  refine ⟨175850464570435412958359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468934572187827767888957 175850464570435412958359)
                  ·
                    rfl

theorem cell20_385276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_385276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385276 prefixEnd_385276 := by exact prefixLift 385276
  have htrace : WordTrace (prefixWord ++ tailWord_385276) baseStart_385276 baseEnd_385276 := by
    simpa [prefixWord, tailWord_385276, baseEnd_385276] using wordTrace_append hprefix tailTrace_385276
  have hstable : (prefixWord ++ tailWord_385276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385276).length < 2 ^ (prefixWord ++ tailWord_385276).sum := by decide
  have hdescent : baseEnd_385276 < baseStart_385276 := by decide
  rcases family_descends (prefixWord ++ tailWord_385276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385310 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_385310 : Nat := 118140960795 + 385310 * 2 ^ 59
def prefixEnd_385310 : Nat := 4983230072969 + 3 ^ 40 * 385310 * 2
def baseEnd_385310 : Nat := 175865983096882405824887

theorem tailTrace_385310 : CollatzResearch.WordTrace tailWord_385310 prefixEnd_385310 175865983096882405824887 := by
  unfold tailWord_385310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756676279261893819256173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9368940156063433702699589 1756676279261893819256173)
  ·
    refine ⟨658753604723210182221065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1756676279261893819256173 658753604723210182221065)
    ·
      refine ⟨494065203542407636665799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 658753604723210182221065 494065203542407636665799)
      ·
        refine ⟨741097805313611454998699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494065203542407636665799 741097805313611454998699)
        ·
          refine ⟨1111646707970417182498049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741097805313611454998699 1111646707970417182498049)
          ·
            refine ⟨833735030977812886873537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1111646707970417182498049 833735030977812886873537)
            ·
              refine ⟨625301273233359665155153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833735030977812886873537 625301273233359665155153)
              ·
                refine ⟨468975954925019748866365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625301273233359665155153 468975954925019748866365)
                ·
                  refine ⟨175865983096882405824887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468975954925019748866365 175865983096882405824887)
                  ·
                    rfl

theorem cell20_385310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_385310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385310 prefixEnd_385310 := by exact prefixLift 385310
  have htrace : WordTrace (prefixWord ++ tailWord_385310) baseStart_385310 baseEnd_385310 := by
    simpa [prefixWord, tailWord_385310, baseEnd_385310] using wordTrace_append hprefix tailTrace_385310
  have hstable : (prefixWord ++ tailWord_385310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385310).length < 2 ^ (prefixWord ++ tailWord_385310).sum := by decide
  have hdescent : baseEnd_385310 < baseStart_385310 := by decide
  rcases family_descends (prefixWord ++ tailWord_385310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385311 : List Nat := [1, 1, 2, 4, 3, 9]
def baseStart_385311 : Nat := 118140960795 + 385311 * 2 ^ 59
def prefixEnd_385311 : Nat := 4983230072969 + 3 ^ 40 * 385311 * 2
def baseEnd_385311 : Nat := 6513571834227068399687

theorem tailTrace_385311 : CollatzResearch.WordTrace tailWord_385311 prefixEnd_385311 6513571834227068399687 := by
  unfold tailWord_385311
  simp only [CollatzResearch.WordTrace]
  refine ⟨14053446707091527724835787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9368964471394351816557191 14053446707091527724835787)
  ·
    refine ⟨21080170060637291587253681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14053446707091527724835787 21080170060637291587253681)
    ·
      refine ⟨15810127545477968690440261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21080170060637291587253681 15810127545477968690440261)
      ·
        refine ⟨2964398914777119129457549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15810127545477968690440261 2964398914777119129457549)
        ·
          refine ⟨1111649593041419673546581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2964398914777119129457549 1111649593041419673546581)
          ·
            refine ⟨6513571834227068399687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1111649593041419673546581 6513571834227068399687)
            ·
              rfl

theorem cell20_385311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 9].length) (baseStart_385311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385311 prefixEnd_385311 := by exact prefixLift 385311
  have htrace : WordTrace (prefixWord ++ tailWord_385311) baseStart_385311 baseEnd_385311 := by
    simpa [prefixWord, tailWord_385311, baseEnd_385311] using wordTrace_append hprefix tailTrace_385311
  have hstable : (prefixWord ++ tailWord_385311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385311).length < 2 ^ (prefixWord ++ tailWord_385311).sum := by decide
  have hdescent : baseEnd_385311 < baseStart_385311 := by decide
  rcases family_descends (prefixWord ++ tailWord_385311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385314 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_385314 : Nat := 118140960795 + 385314 * 2 ^ 59
def prefixEnd_385314 : Nat := 4983230072969 + 3 ^ 40 * 385314 * 2
def baseEnd_385314 : Nat := 175867808805876169691537

theorem tailTrace_385314 : CollatzResearch.WordTrace tailWord_385314 prefixEnd_385314 175867808805876169691537 := by
  unfold tailWord_385314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513389031520164809298749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9369037417387106158129997 3513389031520164809298749)
  ·
    refine ⟨1317520886820061803487031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3513389031520164809298749 1317520886820061803487031)
    ·
      refine ⟨1976281330230092705230547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317520886820061803487031 1976281330230092705230547)
      ·
        refine ⟨2964421995345139057845821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976281330230092705230547 2964421995345139057845821)
        ·
          refine ⟨1111658248254427146692183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2964421995345139057845821 1111658248254427146692183)
          ·
            refine ⟨1667487372381640720038275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111658248254427146692183 1667487372381640720038275)
            ·
              refine ⟨2501231058572461080057413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667487372381640720038275 2501231058572461080057413)
              ·
                refine ⟨468980823482336452510765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2501231058572461080057413 468980823482336452510765)
                ·
                  refine ⟨175867808805876169691537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468980823482336452510765 175867808805876169691537)
                  ·
                    rfl

theorem cell20_385314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_385314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385314 prefixEnd_385314 := by exact prefixLift 385314
  have htrace : WordTrace (prefixWord ++ tailWord_385314) baseStart_385314 baseEnd_385314 := by
    simpa [prefixWord, tailWord_385314, baseEnd_385314] using wordTrace_append hprefix tailTrace_385314
  have hstable : (prefixWord ++ tailWord_385314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385314).length < 2 ^ (prefixWord ++ tailWord_385314).sum := by decide
  have hdescent : baseEnd_385314 < baseStart_385314 := by decide
  rcases family_descends (prefixWord ++ tailWord_385314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385397 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_385397 : Nat := 118140960795 + 385397 * 2 ^ 59
def prefixEnd_385397 : Nat := 4983230072969 + 3 ^ 40 * 385397 * 2
def baseEnd_385397 : Nat := 175905692267496769924531

theorem tailTrace_385397 : CollatzResearch.WordTrace tailWord_385397 prefixEnd_385397 175905692267496769924531 := by
  unfold tailWord_385397
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056583384779964412466445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9371055589853309608310963 14056583384779964412466445)
  ·
    refine ⟨5271218769292486654674917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14056583384779964412466445 5271218769292486654674917)
    ·
      refine ⟨988353519242341247751547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5271218769292486654674917 988353519242341247751547)
      ·
        refine ⟨1482530278863511871627321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988353519242341247751547 1482530278863511871627321)
        ·
          refine ⟨1111897709147633903720491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1482530278863511871627321 1111897709147633903720491)
          ·
            refine ⟨1667846563721450855580737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111897709147633903720491 1667846563721450855580737)
            ·
              refine ⟨1250884922791088141685553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667846563721450855580737 1250884922791088141685553)
              ·
                refine ⟨938163692093316106264165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250884922791088141685553 938163692093316106264165)
                ·
                  refine ⟨175905692267496769924531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938163692093316106264165 175905692267496769924531)
                  ·
                    rfl

theorem cell20_385397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_385397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385397 prefixEnd_385397 := by exact prefixLift 385397
  have htrace : WordTrace (prefixWord ++ tailWord_385397) baseStart_385397 baseEnd_385397 := by
    simpa [prefixWord, tailWord_385397, baseEnd_385397] using wordTrace_append hprefix tailTrace_385397
  have hstable : (prefixWord ++ tailWord_385397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385397).length < 2 ^ (prefixWord ++ tailWord_385397).sum := by decide
  have hdescent : baseEnd_385397 < baseStart_385397 := by decide
  rcases family_descends (prefixWord ++ tailWord_385397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385441 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 3]
def baseStart_385441 : Nat := 118140960795 + 385441 * 2 ^ 59
def prefixEnd_385441 : Nat := 4983230072969 + 3 ^ 40 * 385441 * 2
def baseEnd_385441 : Nat := 175925775066428172457685

theorem tailTrace_385441 : CollatzResearch.WordTrace tailWord_385441 prefixEnd_385441 175925775066428172457685 := by
  unfold tailWord_385441
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058188196620559927068177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9372125464413706618045451 14058188196620559927068177)
  ·
    refine ⟨10543641147465419945301133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14058188196620559927068177 10543641147465419945301133)
    ·
      refine ⟨3953865430299532479487925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10543641147465419945301133 3953865430299532479487925)
      ·
        refine ⟨370674884090581169951993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3953865430299532479487925 370674884090581169951993)
        ·
          refine ⟨278006163067935877463995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370674884090581169951993 278006163067935877463995)
          ·
            refine ⟨417009244601903816195993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278006163067935877463995 417009244601903816195993)
            ·
              refine ⟨312756933451427862146995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417009244601903816195993 312756933451427862146995)
              ·
                refine ⟨469135400177141793220493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312756933451427862146995 469135400177141793220493)
                ·
                  refine ⟨175925775066428172457685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469135400177141793220493 175925775066428172457685)
                  ·
                    rfl

theorem cell20_385441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_385441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385441 prefixEnd_385441 := by exact prefixLift 385441
  have htrace : WordTrace (prefixWord ++ tailWord_385441) baseStart_385441 baseEnd_385441 := by
    simpa [prefixWord, tailWord_385441, baseEnd_385441] using wordTrace_append hprefix tailTrace_385441
  have hstable : (prefixWord ++ tailWord_385441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385441).length < 2 ^ (prefixWord ++ tailWord_385441).sum := by decide
  have hdescent : baseEnd_385441 < baseStart_385441 := by decide
  rcases family_descends (prefixWord ++ tailWord_385441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385442 : List Nat := [3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_385442 : Nat := 118140960795 + 385442 * 2 ^ 59
def prefixEnd_385442 : Nat := 4983230072969 + 3 ^ 40 * 385442 * 2
def baseEnd_385442 : Nat := 58642077164558871141449

theorem tailTrace_385442 : CollatzResearch.WordTrace tailWord_385442 prefixEnd_385442 58642077164558871141449 := by
  unfold tailWord_385442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514556167404234274463645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9372149779744624731903053 3514556167404234274463645)
  ·
    refine ⟨1317958562776587852923867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3514556167404234274463645 1317958562776587852923867)
    ·
      refine ⟨1976937844164881779385801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317958562776587852923867 1976937844164881779385801)
      ·
        refine ⟨1482703383123661334539351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1976937844164881779385801 1482703383123661334539351)
        ·
          refine ⟨2224055074685492001809027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482703383123661334539351 2224055074685492001809027)
          ·
            refine ⟨3336082612028238002713541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224055074685492001809027 3336082612028238002713541)
            ·
              refine ⟨625515489755294625508789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3336082612028238002713541 625515489755294625508789)
              ·
                refine ⟨58642077164558871141449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 625515489755294625508789 58642077164558871141449)
                ·
                  rfl

theorem cell20_385442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_385442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385442 prefixEnd_385442 := by exact prefixLift 385442
  have htrace : WordTrace (prefixWord ++ tailWord_385442) baseStart_385442 baseEnd_385442 := by
    simpa [prefixWord, tailWord_385442, baseEnd_385442] using wordTrace_append hprefix tailTrace_385442
  have hstable : (prefixWord ++ tailWord_385442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385442).length < 2 ^ (prefixWord ++ tailWord_385442).sum := by decide
  have hdescent : baseEnd_385442 < baseStart_385442 := by decide
  rcases family_descends (prefixWord ++ tailWord_385442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385463 : List Nat := [1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_385463 : Nat := 118140960795 + 385463 * 2 ^ 59
def prefixEnd_385463 : Nat := 4983230072969 + 3 ^ 40 * 385463 * 2
def baseEnd_385463 : Nat := 58645272155297957908087

theorem tailTrace_385463 : CollatzResearch.WordTrace tailWord_385463 prefixEnd_385463 58645272155297957908087 := by
  unfold tailWord_385463
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058990602540857684369043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9372660401693905122912695 14058990602540857684369043)
  ·
    refine ⟨21088485903811286526553565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058990602540857684369043 21088485903811286526553565)
    ·
      refine ⟨7908182213929232447457587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21088485903811286526553565 7908182213929232447457587)
      ·
        refine ⟨11862273320893848671186381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7908182213929232447457587 11862273320893848671186381)
        ·
          refine ⟨4448352495335193251694893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11862273320893848671186381 4448352495335193251694893)
          ·
            refine ⟨1668132185750697469385585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4448352495335193251694893 1668132185750697469385585)
            ·
              refine ⟨1251099139313023102039189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668132185750697469385585 1251099139313023102039189)
              ·
                refine ⟨58645272155297957908087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1251099139313023102039189 58645272155297957908087)
                ·
                  rfl

theorem cell20_385463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_385463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385463 prefixEnd_385463 := by exact prefixLift 385463
  have htrace : WordTrace (prefixWord ++ tailWord_385463) baseStart_385463 baseEnd_385463 := by
    simpa [prefixWord, tailWord_385463, baseEnd_385463] using wordTrace_append hprefix tailTrace_385463
  have hstable : (prefixWord ++ tailWord_385463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385463).length < 2 ^ (prefixWord ++ tailWord_385463).sum := by decide
  have hdescent : baseEnd_385463 < baseStart_385463 := by decide
  rcases family_descends (prefixWord ++ tailWord_385463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385508 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_385508 : Nat := 118140960795 + 385508 * 2 ^ 59
def prefixEnd_385508 : Nat := 4983230072969 + 3 ^ 40 * 385508 * 2
def baseEnd_385508 : Nat := 175956355692073717224077

theorem tailTrace_385508 : CollatzResearch.WordTrace tailWord_385508 prefixEnd_385508 175956355692073717224077 := by
  unfold tailWord_385508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030315943688915184878589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9373754591585220246504785 7030315943688915184878589)
  ·
    refine ⟨2636368478883343194329471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7030315943688915184878589 2636368478883343194329471)
    ·
      refine ⟨3954552718325014791494207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636368478883343194329471 3954552718325014791494207)
      ·
        refine ⟨5931829077487522187241311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3954552718325014791494207 5931829077487522187241311)
        ·
          refine ⟨8897743616231283280861967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5931829077487522187241311 8897743616231283280861967)
          ·
            refine ⟨13346615424346924921292951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8897743616231283280861967 13346615424346924921292951)
            ·
              refine ⟨20019923136520387381939427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13346615424346924921292951 20019923136520387381939427)
              ·
                refine ⟨30029884704780581072909141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20019923136520387381939427 30029884704780581072909141)
                ·
                  refine ⟨175956355692073717224077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30029884704780581072909141 175956355692073717224077)
                  ·
                    rfl

theorem cell20_385508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_385508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385508 prefixEnd_385508 := by exact prefixLift 385508
  have htrace : WordTrace (prefixWord ++ tailWord_385508) baseStart_385508 baseEnd_385508 := by
    simpa [prefixWord, tailWord_385508, baseEnd_385508] using wordTrace_append hprefix tailTrace_385508
  have hstable : (prefixWord ++ tailWord_385508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385508).length < 2 ^ (prefixWord ++ tailWord_385508).sum := by decide
  have hdescent : baseEnd_385508 < baseStart_385508 := by decide
  rcases family_descends (prefixWord ++ tailWord_385508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385538 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_385538 : Nat := 118140960795 + 385538 * 2 ^ 59
def prefixEnd_385538 : Nat := 4983230072969 + 3 ^ 40 * 385538 * 2
def baseEnd_385538 : Nat := 175970048509526946223955

theorem tailTrace_385538 : CollatzResearch.WordTrace tailWord_385538 prefixEnd_385538 175970048509526946223955 := by
  unfold tailWord_385538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515431519317286373337317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9374484051512763662232845 3515431519317286373337317)
  ·
    refine ⟨659143409871991195000747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3515431519317286373337317 659143409871991195000747)
    ·
      refine ⟨988715114807986792501121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659143409871991195000747 988715114807986792501121)
      ·
        refine ⟨741536336105990094375841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 988715114807986792501121 741536336105990094375841)
        ·
          refine ⟨556152252079492570781881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741536336105990094375841 556152252079492570781881)
          ·
            refine ⟨417114189059619428086411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556152252079492570781881 417114189059619428086411)
            ·
              refine ⟨625671283589429142129617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417114189059619428086411 625671283589429142129617)
              ·
                refine ⟨469253462692071856597213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625671283589429142129617 469253462692071856597213)
                ·
                  refine ⟨175970048509526946223955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469253462692071856597213 175970048509526946223955)
                  ·
                    rfl

theorem cell20_385538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_385538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385538 prefixEnd_385538 := by exact prefixLift 385538
  have htrace : WordTrace (prefixWord ++ tailWord_385538) baseStart_385538 baseEnd_385538 := by
    simpa [prefixWord, tailWord_385538, baseEnd_385538] using wordTrace_append hprefix tailTrace_385538
  have hstable : (prefixWord ++ tailWord_385538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385538).length < 2 ^ (prefixWord ++ tailWord_385538).sum := by decide
  have hdescent : baseEnd_385538 < baseStart_385538 := by decide
  rcases family_descends (prefixWord ++ tailWord_385538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385584 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_385584 : Nat := 118140960795 + 385584 * 2 ^ 59
def prefixEnd_385584 : Nat := 4983230072969 + 3 ^ 40 * 385584 * 2
def baseEnd_385584 : Nat := 175991044162955230690433

theorem tailTrace_385584 : CollatzResearch.WordTrace tailWord_385584 prefixEnd_385584 175991044162955230690433 := by
  unfold tailWord_385584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031701917551247674761903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9375602556734996899682537 7031701917551247674761903)
  ·
    refine ⟨10547552876326871512142855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031701917551247674761903 10547552876326871512142855)
    ·
      refine ⟨15821329314490307268214283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10547552876326871512142855 15821329314490307268214283)
      ·
        refine ⟨23731993971735460902321425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15821329314490307268214283 23731993971735460902321425)
        ·
          refine ⟨17798995478801595676741069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23731993971735460902321425 17798995478801595676741069)
          ·
            refine ⟨6674623304550598378777901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17798995478801595676741069 6674623304550598378777901)
            ·
              refine ⟨2502983739206474392041713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6674623304550598378777901 2502983739206474392041713)
              ·
                refine ⟨1877237804404855794031285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502983739206474392041713 1877237804404855794031285)
                ·
                  refine ⟨175991044162955230690433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1877237804404855794031285 175991044162955230690433)
                  ·
                    rfl

theorem cell20_385584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_385584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385584 prefixEnd_385584 := by exact prefixLift 385584
  have htrace : WordTrace (prefixWord ++ tailWord_385584) baseStart_385584 baseEnd_385584 := by
    simpa [prefixWord, tailWord_385584, baseEnd_385584] using wordTrace_append hprefix tailTrace_385584
  have hstable : (prefixWord ++ tailWord_385584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385584).length < 2 ^ (prefixWord ++ tailWord_385584).sum := by decide
  have hdescent : baseEnd_385584 < baseStart_385584 := by decide
  rcases family_descends (prefixWord ++ tailWord_385584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385601 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_385601 : Nat := 118140960795 + 385601 * 2 ^ 59
def prefixEnd_385601 : Nat := 4983230072969 + 3 ^ 40 * 385601 * 2
def baseEnd_385601 : Nat := 175998803426178727123697

theorem tailTrace_385601 : CollatzResearch.WordTrace tailWord_385601 prefixEnd_385601 175998803426178727123697 := by
  unfold tailWord_385601
  simp only [CollatzResearch.WordTrace]
  refine ⟨14064023876040907252892657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9376015917360604835261771 14064023876040907252892657)
  ·
    refine ⟨10548017907030680439669493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14064023876040907252892657 10548017907030680439669493)
    ·
      refine ⟨988876678784126291219015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10548017907030680439669493 988876678784126291219015)
      ·
        refine ⟨1483315018176189436828523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988876678784126291219015 1483315018176189436828523)
        ·
          refine ⟨2224972527264284155242785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483315018176189436828523 2224972527264284155242785)
          ·
            refine ⟨1668729395448213116432089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224972527264284155242785 1668729395448213116432089)
            ·
              refine ⟨1251547046586159837324067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668729395448213116432089 1251547046586159837324067)
              ·
                refine ⟨1877320569879239755986101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251547046586159837324067 1877320569879239755986101)
                ·
                  refine ⟨175998803426178727123697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1877320569879239755986101 175998803426178727123697)
                  ·
                    rfl

theorem cell20_385601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_385601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385601 prefixEnd_385601 := by exact prefixLift 385601
  have htrace : WordTrace (prefixWord ++ tailWord_385601) baseStart_385601 baseEnd_385601 := by
    simpa [prefixWord, tailWord_385601, baseEnd_385601] using wordTrace_append hprefix tailTrace_385601
  have hstable : (prefixWord ++ tailWord_385601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385601).length < 2 ^ (prefixWord ++ tailWord_385601).sum := by decide
  have hdescent : baseEnd_385601 < baseStart_385601 := by decide
  rcases family_descends (prefixWord ++ tailWord_385601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385653 : List Nat := [1, 3, 4, 2, 10]
def baseStart_385653 : Nat := 118140960795 + 385653 * 2 ^ 59
def prefixEnd_385653 : Nat := 4983230072969 + 3 ^ 40 * 385653 * 2
def baseEnd_385653 : Nat := 2173117748680217992471

theorem tailTrace_385653 : CollatzResearch.WordTrace tailWord_385653 prefixEnd_385653 2173117748680217992471 := by
  unfold tailWord_385653
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065920471852520133785613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9377280314568346755857075 14065920471852520133785613)
  ·
    refine ⟨5274720176944695050169605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14065920471852520133785613 5274720176944695050169605)
    ·
      refine ⟨989010033177130321906801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5274720176944695050169605 989010033177130321906801)
      ·
        refine ⟨741757524882847741430101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 989010033177130321906801 741757524882847741430101)
        ·
          refine ⟨2173117748680217992471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 741757524882847741430101 2173117748680217992471)
          ·
            rfl

theorem cell20_385653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 10].length) (baseStart_385653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385653 prefixEnd_385653 := by exact prefixLift 385653
  have htrace : WordTrace (prefixWord ++ tailWord_385653) baseStart_385653 baseEnd_385653 := by
    simpa [prefixWord, tailWord_385653, baseEnd_385653] using wordTrace_append hprefix tailTrace_385653
  have hstable : (prefixWord ++ tailWord_385653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385653).length < 2 ^ (prefixWord ++ tailWord_385653).sum := by decide
  have hdescent : baseEnd_385653 < baseStart_385653 := by decide
  rcases family_descends (prefixWord ++ tailWord_385653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385660 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_385660 : Nat := 118140960795 + 385660 * 2 ^ 59
def prefixEnd_385660 : Nat := 4983230072969 + 3 ^ 40 * 385660 * 2
def baseEnd_385660 : Nat := 176025732633836744156789

theorem tailTrace_385660 : CollatzResearch.WordTrace tailWord_385660 prefixEnd_385660 176025732633836744156789 := by
  unfold tailWord_385660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033087891413580164645217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9377450521884773552860289 7033087891413580164645217)
  ·
    refine ⟨5274815918560185123483913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7033087891413580164645217 5274815918560185123483913)
    ·
      refine ⟨3956111938920138842612935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5274815918560185123483913 3956111938920138842612935)
      ·
        refine ⟨5934167908380208263919403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956111938920138842612935 5934167908380208263919403)
        ·
          refine ⟨8901251862570312395879105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934167908380208263919403 8901251862570312395879105)
          ·
            refine ⟨6675938896927734296909329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8901251862570312395879105 6675938896927734296909329)
            ·
              refine ⟨5006954172695800722681997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6675938896927734296909329 5006954172695800722681997)
              ·
                refine ⟨1877607814760925271005749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5006954172695800722681997 1877607814760925271005749)
                ·
                  refine ⟨176025732633836744156789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1877607814760925271005749 176025732633836744156789)
                  ·
                    rfl

theorem cell20_385660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_385660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385660 prefixEnd_385660 := by exact prefixLift 385660
  have htrace : WordTrace (prefixWord ++ tailWord_385660) baseStart_385660 baseEnd_385660 := by
    simpa [prefixWord, tailWord_385660, baseEnd_385660] using wordTrace_append hprefix tailTrace_385660
  have hstable : (prefixWord ++ tailWord_385660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385660).length < 2 ^ (prefixWord ++ tailWord_385660).sum := by decide
  have hdescent : baseEnd_385660 < baseStart_385660 := by decide
  rcases family_descends (prefixWord ++ tailWord_385660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385715 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_385715 : Nat := 118140960795 + 385715 * 2 ^ 59
def prefixEnd_385715 : Nat := 4983230072969 + 3 ^ 40 * 385715 * 2
def baseEnd_385715 : Nat := 176050836132500997323231

theorem tailTrace_385715 : CollatzResearch.WordTrace tailWord_385715 prefixEnd_385715 176050836132500997323231 := by
  unfold tailWord_385715
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068181797627904722542599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9378787865085269815028399 14068181797627904722542599)
  ·
    refine ⟨21102272696441857083813899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14068181797627904722542599 21102272696441857083813899)
    ·
      refine ⟨31653409044662785625720849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21102272696441857083813899 31653409044662785625720849)
      ·
        refine ⟨23740056783497089219290637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31653409044662785625720849 23740056783497089219290637)
        ·
          refine ⟨8902521293811408457233989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23740056783497089219290637 8902521293811408457233989)
          ·
            refine ⟨1669222742589639085731373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8902521293811408457233989 1669222742589639085731373)
            ·
              refine ⟨625958528471114657149265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669222742589639085731373 625958528471114657149265)
              ·
                refine ⟨469468896353335992861949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625958528471114657149265 469468896353335992861949)
                ·
                  refine ⟨176050836132500997323231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469468896353335992861949 176050836132500997323231)
                  ·
                    rfl

theorem cell20_385715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_385715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385715 prefixEnd_385715 := by exact prefixLift 385715
  have htrace : WordTrace (prefixWord ++ tailWord_385715) baseStart_385715 baseEnd_385715 := by
    simpa [prefixWord, tailWord_385715, baseEnd_385715] using wordTrace_append hprefix tailTrace_385715
  have hstable : (prefixWord ++ tailWord_385715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385715).length < 2 ^ (prefixWord ++ tailWord_385715).sum := by decide
  have hdescent : baseEnd_385715 < baseStart_385715 := by decide
  rcases family_descends (prefixWord ++ tailWord_385715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385722 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_385722 : Nat := 118140960795 + 385722 * 2 ^ 59
def prefixEnd_385722 : Nat := 4983230072969 + 3 ^ 40 * 385722 * 2
def baseEnd_385722 : Nat := 176054031123240084089869

theorem tailTrace_385722 : CollatzResearch.WordTrace tailWord_385722 prefixEnd_385722 176054031123240084089869 := by
  unfold tailWord_385722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517109277150636229511855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9378958072401696612031613 3517109277150636229511855)
  ·
    refine ⟨5275663915725954344267783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517109277150636229511855 5275663915725954344267783)
    ·
      refine ⟨7913495873588931516401675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5275663915725954344267783 7913495873588931516401675)
      ·
        refine ⟨11870243810383397274602513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913495873588931516401675 11870243810383397274602513)
        ·
          refine ⟨8902682857787547955951885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11870243810383397274602513 8902682857787547955951885)
          ·
            refine ⟨3338506071670330483481957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8902682857787547955951885 3338506071670330483481957)
            ·
              refine ⟨625969888438186965652867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3338506071670330483481957 625969888438186965652867)
              ·
                refine ⟨938954832657280448479301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625969888438186965652867 938954832657280448479301)
                ·
                  refine ⟨176054031123240084089869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938954832657280448479301 176054031123240084089869)
                  ·
                    rfl

theorem cell20_385722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_385722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385722 prefixEnd_385722 := by exact prefixLift 385722
  have htrace : WordTrace (prefixWord ++ tailWord_385722) baseStart_385722 baseEnd_385722 := by
    simpa [prefixWord, tailWord_385722, baseEnd_385722] using wordTrace_append hprefix tailTrace_385722
  have hstable : (prefixWord ++ tailWord_385722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385722).length < 2 ^ (prefixWord ++ tailWord_385722).sum := by decide
  have hdescent : baseEnd_385722 < baseStart_385722 := by decide
  rcases family_descends (prefixWord ++ tailWord_385722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385746 : List Nat := [3, 2, 2, 2, 3, 1, 1, 6]
def baseStart_385746 : Nat := 118140960795 + 385746 * 2 ^ 59
def prefixEnd_385746 : Nat := 4983230072969 + 3 ^ 40 * 385746 * 2
def baseEnd_385746 : Nat := 58688328459067555763257

theorem tailTrace_385746 : CollatzResearch.WordTrace tailWord_385746 prefixEnd_385746 58688328459067555763257 := by
  unfold tailWord_385746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517328115128899254230273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9379541640343731344614061 3517328115128899254230273)
  ·
    refine ⟨2637996086346674440672705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3517328115128899254230273 2637996086346674440672705)
    ·
      refine ⟨1978497064760005830504529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2637996086346674440672705 1978497064760005830504529)
      ·
        refine ⟨1483872798570004372878397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978497064760005830504529 1483872798570004372878397)
        ·
          refine ⟨556452299463751639829399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1483872798570004372878397 556452299463751639829399)
          ·
            refine ⟨834678449195627459744099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556452299463751639829399 834678449195627459744099)
            ·
              refine ⟨1252017673793441189616149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834678449195627459744099 1252017673793441189616149)
              ·
                refine ⟨58688328459067555763257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1252017673793441189616149 58688328459067555763257)
                ·
                  rfl

theorem cell20_385746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_385746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385746 prefixEnd_385746 := by exact prefixLift 385746
  have htrace : WordTrace (prefixWord ++ tailWord_385746) baseStart_385746 baseEnd_385746 := by
    simpa [prefixWord, tailWord_385746, baseEnd_385746] using wordTrace_append hprefix tailTrace_385746
  have hstable : (prefixWord ++ tailWord_385746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385746).length < 2 ^ (prefixWord ++ tailWord_385746).sum := by decide
  have hdescent : baseEnd_385746 < baseStart_385746 := by decide
  rcases family_descends (prefixWord ++ tailWord_385746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385780 : List Nat := [2, 6, 1, 1, 2, 1, 2, 5]
def baseStart_385780 : Nat := 118140960795 + 385780 * 2 ^ 59
def prefixEnd_385780 : Nat := 4983230072969 + 3 ^ 40 * 385780 * 2
def baseEnd_385780 : Nat := 58693501301216553385433

theorem tailTrace_385780 : CollatzResearch.WordTrace tailWord_385780 prefixEnd_385780 58693501301216553385433 := by
  unfold tailWord_385780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035276271196210411829397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9380368361594947215772529 7035276271196210411829397)
  ·
    refine ⟨329778575212322363054503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7035276271196210411829397 329778575212322363054503)
    ·
      refine ⟨494667862818483544581755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329778575212322363054503 494667862818483544581755)
      ·
        refine ⟨742001794227725316872633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494667862818483544581755 742001794227725316872633)
        ·
          refine ⟨556501345670793987654475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742001794227725316872633 556501345670793987654475)
          ·
            refine ⟨834752018506190981481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556501345670793987654475 834752018506190981481713)
            ·
              refine ⟨626064013879643236111285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834752018506190981481713 626064013879643236111285)
              ·
                refine ⟨58693501301216553385433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626064013879643236111285 58693501301216553385433)
                ·
                  rfl

theorem cell20_385780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_385780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385780 prefixEnd_385780 := by exact prefixLift 385780
  have htrace : WordTrace (prefixWord ++ tailWord_385780) baseStart_385780 baseEnd_385780 := by
    simpa [prefixWord, tailWord_385780, baseEnd_385780] using wordTrace_append hprefix tailTrace_385780
  have hstable : (prefixWord ++ tailWord_385780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385780).length < 2 ^ (prefixWord ++ tailWord_385780).sum := by decide
  have hdescent : baseEnd_385780 < baseStart_385780 := by decide
  rcases family_descends (prefixWord ++ tailWord_385780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385828 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 2]
def baseStart_385828 : Nat := 118140960795 + 385828 * 2 ^ 59
def prefixEnd_385828 : Nat := 4983230072969 + 3 ^ 40 * 385828 * 2
def baseEnd_385828 : Nat := 176102412411574826556103

theorem tailTrace_385828 : CollatzResearch.WordTrace tailWord_385828 prefixEnd_385828 176102412411574826556103 := by
  unfold tailWord_385828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036151623109262510703069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9381535497479016680937425 7036151623109262510703069)
  ·
    refine ⟨2638556858665973441513651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7036151623109262510703069 2638556858665973441513651)
    ·
      refine ⟨3957835287998960162270477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638556858665973441513651 3957835287998960162270477)
      ·
        refine ⟨1484188232999610060851429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3957835287998960162270477 1484188232999610060851429)
        ·
          refine ⟨278285293687426886409643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1484188232999610060851429 278285293687426886409643)
          ·
            refine ⟨417427940531140329614465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278285293687426886409643 417427940531140329614465)
            ·
              refine ⟨313070955398355247210849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417427940531140329614465 313070955398355247210849)
              ·
                refine ⟨234803216548766435408137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313070955398355247210849 234803216548766435408137)
                ·
                  refine ⟨176102412411574826556103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234803216548766435408137 176102412411574826556103)
                  ·
                    rfl

theorem cell20_385828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_385828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385828 prefixEnd_385828 := by exact prefixLift 385828
  have htrace : WordTrace (prefixWord ++ tailWord_385828) baseStart_385828 baseEnd_385828 := by
    simpa [prefixWord, tailWord_385828, baseEnd_385828] using wordTrace_append hprefix tailTrace_385828
  have hstable : (prefixWord ++ tailWord_385828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385828).length < 2 ^ (prefixWord ++ tailWord_385828).sum := by decide
  have hdescent : baseEnd_385828 < baseStart_385828 := by decide
  rcases family_descends (prefixWord ++ tailWord_385828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385829 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_385829 : Nat := 118140960795 + 385829 * 2 ^ 59
def prefixEnd_385829 : Nat := 4983230072969 + 3 ^ 40 * 385829 * 2
def baseEnd_385829 : Nat := 176102868838823267522765

theorem tailTrace_385829 : CollatzResearch.WordTrace tailWord_385829 prefixEnd_385829 176102868838823267522765 := by
  unfold tailWord_385829
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072339719214902192192541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9381559812809934794795027 14072339719214902192192541)
  ·
    refine ⟨5277127394705588322072203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14072339719214902192192541 5277127394705588322072203)
    ·
      refine ⟨7915691092058382483108305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277127394705588322072203 7915691092058382483108305)
      ·
        refine ⟨5936768319043786862331229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7915691092058382483108305 5936768319043786862331229)
        ·
          refine ⟨2226288119641420073374211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5936768319043786862331229 2226288119641420073374211)
          ·
            refine ⟨3339432179462130110061317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226288119641420073374211 3339432179462130110061317)
            ·
              refine ⟨626143533649149395636497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3339432179462130110061317 626143533649149395636497)
              ·
                refine ⟨469607650236862046727373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626143533649149395636497 469607650236862046727373)
                ·
                  refine ⟨176102868838823267522765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469607650236862046727373 176102868838823267522765)
                  ·
                    rfl

theorem cell20_385829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_385829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385829 prefixEnd_385829 := by exact prefixLift 385829
  have htrace : WordTrace (prefixWord ++ tailWord_385829) baseStart_385829 baseEnd_385829 := by
    simpa [prefixWord, tailWord_385829, baseEnd_385829] using wordTrace_append hprefix tailTrace_385829
  have hstable : (prefixWord ++ tailWord_385829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385829).length < 2 ^ (prefixWord ++ tailWord_385829).sum := by decide
  have hdescent : baseEnd_385829 < baseStart_385829 := by decide
  rcases family_descends (prefixWord ++ tailWord_385829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385843 : List Nat := [1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_385843 : Nat := 118140960795 + 385843 * 2 ^ 59
def prefixEnd_385843 : Nat := 4983230072969 + 3 ^ 40 * 385843 * 2
def baseEnd_385843 : Nat := 58703086273433813685347

theorem tailTrace_385843 : CollatzResearch.WordTrace tailWord_385843 prefixEnd_385843 58703086273433813685347 := by
  unfold tailWord_385843
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072850341164182583202183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9381900227442788388801455 14072850341164182583202183)
  ·
    refine ⟨21109275511746273874803275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14072850341164182583202183 21109275511746273874803275)
    ·
      refine ⟨31663913267619410812204913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21109275511746273874803275 31663913267619410812204913)
      ·
        refine ⟨23747934950714558109153685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31663913267619410812204913 23747934950714558109153685)
        ·
          refine ⟨1113184450814744911366579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23747934950714558109153685 1113184450814744911366579)
          ·
            refine ⟨1669776676222117367049869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113184450814744911366579 1669776676222117367049869)
            ·
              refine ⟨626166253583294012643701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669776676222117367049869 626166253583294012643701)
              ·
                refine ⟨58703086273433813685347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626166253583294012643701 58703086273433813685347)
                ·
                  rfl

theorem cell20_385843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_385843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385843 prefixEnd_385843 := by exact prefixLift 385843
  have htrace : WordTrace (prefixWord ++ tailWord_385843) baseStart_385843 baseEnd_385843 := by
    simpa [prefixWord, tailWord_385843, baseEnd_385843] using wordTrace_append hprefix tailTrace_385843
  have hstable : (prefixWord ++ tailWord_385843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385843).length < 2 ^ (prefixWord ++ tailWord_385843).sum := by decide
  have hdescent : baseEnd_385843 < baseStart_385843 := by decide
  rcases family_descends (prefixWord ++ tailWord_385843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385853 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_385853 : Nat := 118140960795 + 385853 * 2 ^ 59
def prefixEnd_385853 : Nat := 4983230072969 + 3 ^ 40 * 385853 * 2
def baseEnd_385853 : Nat := 176113823092785850722667

theorem tailTrace_385853 : CollatzResearch.WordTrace tailWord_385853 prefixEnd_385853 176113823092785850722667 := by
  unfold tailWord_385853
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073215071127954291066213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9382143380751969527377475 14073215071127954291066213)
  ·
    refine ⟨2638727825836491429574915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14073215071127954291066213 2638727825836491429574915)
    ·
      refine ⟨3958091738754737144362373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638727825836491429574915 3958091738754737144362373)
      ·
        refine ⟨742142201016513214567945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3958091738754737144362373 742142201016513214567945)
        ·
          refine ⟨556606650762384910925959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742142201016513214567945 556606650762384910925959)
          ·
            refine ⟨834909976143577366388939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556606650762384910925959 834909976143577366388939)
            ·
              refine ⟨1252364964215366049583409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834909976143577366388939 1252364964215366049583409)
              ·
                refine ⟨939273723161524537187557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252364964215366049583409 939273723161524537187557)
                ·
                  refine ⟨176113823092785850722667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939273723161524537187557 176113823092785850722667)
                  ·
                    rfl

theorem cell20_385853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_385853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385853 prefixEnd_385853 := by exact prefixLift 385853
  have htrace : WordTrace (prefixWord ++ tailWord_385853) baseStart_385853 baseEnd_385853 := by
    simpa [prefixWord, tailWord_385853, baseEnd_385853] using wordTrace_append hprefix tailTrace_385853
  have hstable : (prefixWord ++ tailWord_385853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385853).length < 2 ^ (prefixWord ++ tailWord_385853).sum := by decide
  have hdescent : baseEnd_385853 < baseStart_385853 := by decide
  rcases family_descends (prefixWord ++ tailWord_385853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385884 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_385884 : Nat := 118140960795 + 385884 * 2 ^ 59
def prefixEnd_385884 : Nat := 4983230072969 + 3 ^ 40 * 385884 * 2
def baseEnd_385884 : Nat := 176127972337487520689207

theorem tailTrace_385884 : CollatzResearch.WordTrace tailWord_385884 prefixEnd_385884 176127972337487520689207 := by
  unfold tailWord_385884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037172867007823292722353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9382897156010431056963137 7037172867007823292722353)
  ·
    refine ⟨5277879650255867469541765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7037172867007823292722353 5277879650255867469541765)
    ·
      refine ⟨989602434422975150539081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5277879650255867469541765 989602434422975150539081)
      ·
        refine ⟨742201825817231362904311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 989602434422975150539081 742201825817231362904311)
        ·
          refine ⟨1113302738725847044356467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742201825817231362904311 1113302738725847044356467)
          ·
            refine ⟨1669954108088770566534701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113302738725847044356467 1669954108088770566534701)
            ·
              refine ⟨626232790533288962450513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669954108088770566534701 626232790533288962450513)
              ·
                refine ⟨469674592899966721837885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626232790533288962450513 469674592899966721837885)
                ·
                  refine ⟨176127972337487520689207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469674592899966721837885 176127972337487520689207)
                  ·
                    rfl

theorem cell20_385884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_385884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385884 prefixEnd_385884 := by exact prefixLift 385884
  have htrace : WordTrace (prefixWord ++ tailWord_385884) baseStart_385884 baseEnd_385884 := by
    simpa [prefixWord, tailWord_385884, baseEnd_385884] using wordTrace_append hprefix tailTrace_385884
  have hstable : (prefixWord ++ tailWord_385884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385884).length < 2 ^ (prefixWord ++ tailWord_385884).sum := by decide
  have hdescent : baseEnd_385884 < baseStart_385884 := by decide
  rcases family_descends (prefixWord ++ tailWord_385884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385888 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_385888 : Nat := 118140960795 + 385888 * 2 ^ 59
def prefixEnd_385888 : Nat := 4983230072969 + 3 ^ 40 * 385888 * 2
def baseEnd_385888 : Nat := 176129798046481284555857

theorem tailTrace_385888 : CollatzResearch.WordTrace tailWord_385888 prefixEnd_385888 176129798046481284555857 := by
  unfold tailWord_385888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037245813000577634295159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9382994417334103512393545 7037245813000577634295159)
  ·
    refine ⟨10555868719500866451442739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7037245813000577634295159 10555868719500866451442739)
    ·
      refine ⟨15833803079251299677164109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10555868719500866451442739 15833803079251299677164109)
      ·
        refine ⟨5937676154719237378936541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15833803079251299677164109 5937676154719237378936541)
        ·
          refine ⟨2226628558019714017101203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5937676154719237378936541 2226628558019714017101203)
          ·
            refine ⟨3339942837029571025651805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226628558019714017101203 3339942837029571025651805)
            ·
              refine ⟨1252478563886089134619427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3339942837029571025651805 1252478563886089134619427)
              ·
                refine ⟨1878717845829133701929141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252478563886089134619427 1878717845829133701929141)
                ·
                  refine ⟨176129798046481284555857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1878717845829133701929141 176129798046481284555857)
                  ·
                    rfl

theorem cell20_385888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_385888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385888 prefixEnd_385888 := by exact prefixLift 385888
  have htrace : WordTrace (prefixWord ++ tailWord_385888) baseStart_385888 baseEnd_385888 := by
    simpa [prefixWord, tailWord_385888, baseEnd_385888] using wordTrace_append hprefix tailTrace_385888
  have hstable : (prefixWord ++ tailWord_385888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385888).length < 2 ^ (prefixWord ++ tailWord_385888).sum := by decide
  have hdescent : baseEnd_385888 < baseStart_385888 := by decide
  rcases family_descends (prefixWord ++ tailWord_385888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385891 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 2]
def baseStart_385891 : Nat := 118140960795 + 385891 * 2 ^ 59
def prefixEnd_385891 : Nat := 4983230072969 + 3 ^ 40 * 385891 * 2
def baseEnd_385891 : Nat := 176131167328226607455845

theorem tailTrace_385891 : CollatzResearch.WordTrace tailWord_385891 prefixEnd_385891 176131167328226607455845 := by
  unfold tailWord_385891
  simp only [CollatzResearch.WordTrace]
  refine ⟨14074601044990286780949527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383067363326857853966351 14074601044990286780949527)
  ·
    refine ⟨21111901567485430171424291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14074601044990286780949527 21111901567485430171424291)
    ·
      refine ⟨31667852351228145257136437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21111901567485430171424291 31667852351228145257136437)
      ·
        refine ⟨2968861157927638617856541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31667852351228145257136437 2968861157927638617856541)
        ·
          refine ⟨1113322934222864481696203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2968861157927638617856541 1113322934222864481696203)
          ·
            refine ⟨1669984401334296722544305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113322934222864481696203 1669984401334296722544305)
            ·
              refine ⟨1252488301000722541908229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669984401334296722544305 1252488301000722541908229)
              ·
                refine ⟨234841556437635476607793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1252488301000722541908229 234841556437635476607793)
                ·
                  refine ⟨176131167328226607455845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234841556437635476607793 176131167328226607455845)
                  ·
                    rfl

theorem cell20_385891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 2].length) (baseStart_385891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385891 prefixEnd_385891 := by exact prefixLift 385891
  have htrace : WordTrace (prefixWord ++ tailWord_385891) baseStart_385891 baseEnd_385891 := by
    simpa [prefixWord, tailWord_385891, baseEnd_385891] using wordTrace_append hprefix tailTrace_385891
  have hstable : (prefixWord ++ tailWord_385891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385891).length < 2 ^ (prefixWord ++ tailWord_385891).sum := by decide
  have hdescent : baseEnd_385891 < baseStart_385891 := by decide
  rcases family_descends (prefixWord ++ tailWord_385891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385919 : List Nat := [1, 1, 2, 2, 1, 1, 8, 4]
def baseStart_385919 : Nat := 118140960795 + 385919 * 2 ^ 59
def prefixEnd_385919 : Nat := 4983230072969 + 3 ^ 40 * 385919 * 2
def baseEnd_385919 : Nat := 58714649097060984840799

theorem tailTrace_385919 : CollatzResearch.WordTrace tailWord_385919 prefixEnd_385919 58714649097060984840799 := by
  unfold tailWord_385919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075622288888847562968811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383748192592565041979207 14075622288888847562968811)
  ·
    refine ⟨21113433433333271344453217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14075622288888847562968811 21113433433333271344453217)
    ·
      refine ⟨15835075074999953508339913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21113433433333271344453217 15835075074999953508339913)
      ·
        refine ⟨11876306306249965131254935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15835075074999953508339913 11876306306249965131254935)
        ·
          refine ⟨17814459459374947696882403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11876306306249965131254935 17814459459374947696882403)
          ·
            refine ⟨26721689189062421545323605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17814459459374947696882403 26721689189062421545323605)
            ·
              refine ⟨313144795184325252484261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 26721689189062421545323605 313144795184325252484261)
              ·
                refine ⟨58714649097060984840799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313144795184325252484261 58714649097060984840799)
                ·
                  rfl

theorem cell20_385919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_385919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385919 prefixEnd_385919 := by exact prefixLift 385919
  have htrace : WordTrace (prefixWord ++ tailWord_385919) baseStart_385919 baseEnd_385919 := by
    simpa [prefixWord, tailWord_385919, baseEnd_385919] using wordTrace_append hprefix tailTrace_385919
  have hstable : (prefixWord ++ tailWord_385919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385919).length < 2 ^ (prefixWord ++ tailWord_385919).sum := by decide
  have hdescent : baseEnd_385919 < baseStart_385919 := by decide
  rcases family_descends (prefixWord ++ tailWord_385919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385929 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 2]
def baseStart_385929 : Nat := 118140960795 + 385929 * 2 ^ 59
def prefixEnd_385929 : Nat := 4983230072969 + 3 ^ 40 * 385929 * 2
def baseEnd_385929 : Nat := 176148511563667364189023

theorem tailTrace_385929 : CollatzResearch.WordTrace tailWord_385929 prefixEnd_385929 176148511563667364189023 := by
  unfold tailWord_385929
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075987018852619270832841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383991345901746180555227 14075987018852619270832841)
  ·
    refine ⟨10556990264139464453124631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14075987018852619270832841 10556990264139464453124631)
    ·
      refine ⟨15835485396209196679686947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10556990264139464453124631 15835485396209196679686947)
      ·
        refine ⟨23753228094313795019530421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15835485396209196679686947 23753228094313795019530421)
        ·
          refine ⟨2226865133841918283080977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23753228094313795019530421 2226865133841918283080977)
          ·
            refine ⟨1670148850381438712310733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226865133841918283080977 1670148850381438712310733)
            ·
              refine ⟨626305818893039517116525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670148850381438712310733 626305818893039517116525)
              ·
                refine ⟨234864682084889818918697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 626305818893039517116525 234864682084889818918697)
                ·
                  refine ⟨176148511563667364189023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234864682084889818918697 176148511563667364189023)
                  ·
                    rfl

theorem cell20_385929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_385929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385929 prefixEnd_385929 := by exact prefixLift 385929
  have htrace : WordTrace (prefixWord ++ tailWord_385929) baseStart_385929 baseEnd_385929 := by
    simpa [prefixWord, tailWord_385929, baseEnd_385929] using wordTrace_append hprefix tailTrace_385929
  have hstable : (prefixWord ++ tailWord_385929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385929).length < 2 ^ (prefixWord ++ tailWord_385929).sum := by decide
  have hdescent : baseEnd_385929 < baseStart_385929 := by decide
  rcases family_descends (prefixWord ++ tailWord_385929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385946 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_385946 : Nat := 118140960795 + 385946 * 2 ^ 59
def prefixEnd_385946 : Nat := 4983230072969 + 3 ^ 40 * 385946 * 2
def baseEnd_385946 : Nat := 176156270826890860622287

theorem tailTrace_385946 : CollatzResearch.WordTrace tailWord_385946 prefixEnd_385946 176156270826890860622287 := by
  unfold tailWord_385946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519151764947757793550423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9384404706527354116134461 3519151764947757793550423)
  ·
    refine ⟨5278727647421636690325635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519151764947757793550423 5278727647421636690325635)
    ·
      refine ⟨7918091471132455035488453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5278727647421636690325635 7918091471132455035488453)
      ·
        refine ⟨1484642150837335319154085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7918091471132455035488453 1484642150837335319154085)
        ·
          refine ⟨278370403282000372341391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1484642150837335319154085 278370403282000372341391)
          ·
            refine ⟨417555604923000558512087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278370403282000372341391 417555604923000558512087)
            ·
              refine ⟨626333407384500837768131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417555604923000558512087 626333407384500837768131)
              ·
                refine ⟨939500111076751256652197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626333407384500837768131 939500111076751256652197)
                ·
                  refine ⟨176156270826890860622287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939500111076751256652197 176156270826890860622287)
                  ·
                    rfl

theorem cell20_385946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_385946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385946 prefixEnd_385946 := by exact prefixLift 385946
  have htrace : WordTrace (prefixWord ++ tailWord_385946) baseStart_385946 baseEnd_385946 := by
    simpa [prefixWord, tailWord_385946, baseEnd_385946] using wordTrace_append hprefix tailTrace_385946
  have hstable : (prefixWord ++ tailWord_385946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385946).length < 2 ^ (prefixWord ++ tailWord_385946).sum := by decide
  have hdescent : baseEnd_385946 < baseStart_385946 := by decide
  rcases family_descends (prefixWord ++ tailWord_385946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385964 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_385964 : Nat := 118140960795 + 385964 * 2 ^ 59
def prefixEnd_385964 : Nat := 4983230072969 + 3 ^ 40 * 385964 * 2
def baseEnd_385964 : Nat := 176164486517362798022213

theorem tailTrace_385964 : CollatzResearch.WordTrace tailWord_385964 prefixEnd_385964 176164486517362798022213 := by
  unfold tailWord_385964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7038631786862910124178473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9384842382483880165571297 7038631786862910124178473)
  ·
    refine ⟨5278973840147182593133855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7038631786862910124178473 5278973840147182593133855)
    ·
      refine ⟨7918460760220773889700783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5278973840147182593133855 7918460760220773889700783)
      ·
        refine ⟨11877691140331160834551175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7918460760220773889700783 11877691140331160834551175)
        ·
          refine ⟨17816536710496741251826763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11877691140331160834551175 17816536710496741251826763)
          ·
            refine ⟨26724805065745111877740145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17816536710496741251826763 26724805065745111877740145)
            ·
              refine ⟨20043603799308833908305109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26724805065745111877740145 20043603799308833908305109)
              ·
                refine ⟨469771964046300794725901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20043603799308833908305109 469771964046300794725901)
                ·
                  refine ⟨176164486517362798022213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469771964046300794725901 176164486517362798022213)
                  ·
                    rfl

theorem cell20_385964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_385964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385964 prefixEnd_385964 := by exact prefixLift 385964
  have htrace : WordTrace (prefixWord ++ tailWord_385964) baseStart_385964 baseEnd_385964 := by
    simpa [prefixWord, tailWord_385964, baseEnd_385964] using wordTrace_append hprefix tailTrace_385964
  have hstable : (prefixWord ++ tailWord_385964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385964).length < 2 ^ (prefixWord ++ tailWord_385964).sum := by decide
  have hdescent : baseEnd_385964 < baseStart_385964 := by decide
  rcases family_descends (prefixWord ++ tailWord_385964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385978 : List Nat := [3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_385978 : Nat := 118140960795 + 385978 * 2 ^ 59
def prefixEnd_385978 : Nat := 4983230072969 + 3 ^ 40 * 385978 * 2
def baseEnd_385978 : Nat := 58723625499613657185163

theorem tailTrace_385978 : CollatzResearch.WordTrace tailWord_385978 prefixEnd_385978 58723625499613657185163 := by
  unfold tailWord_385978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519443548918775159841647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9385182797116733759577725 3519443548918775159841647)
  ·
    refine ⟨5279165323378162739762471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519443548918775159841647 5279165323378162739762471)
    ·
      refine ⟨7918747985067244109643707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279165323378162739762471 7918747985067244109643707)
      ·
        refine ⟨11878121977600866164465561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7918747985067244109643707 11878121977600866164465561)
        ·
          refine ⟨8908591483200649623349171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11878121977600866164465561 8908591483200649623349171)
          ·
            refine ⟨13362887224800974435023757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908591483200649623349171 13362887224800974435023757)
            ·
              refine ⟨5011082709300365413133909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13362887224800974435023757 5011082709300365413133909)
              ·
                refine ⟨58723625499613657185163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5011082709300365413133909 58723625499613657185163)
                ·
                  rfl

theorem cell20_385978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_385978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_385978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_385978 prefixEnd_385978 := by exact prefixLift 385978
  have htrace : WordTrace (prefixWord ++ tailWord_385978) baseStart_385978 baseEnd_385978 := by
    simpa [prefixWord, tailWord_385978, baseEnd_385978] using wordTrace_append hprefix tailTrace_385978
  have hstable : (prefixWord ++ tailWord_385978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385978).length < 2 ^ (prefixWord ++ tailWord_385978).sum := by decide
  have hdescent : baseEnd_385978 < baseStart_385978 := by decide
  rcases family_descends (prefixWord ++ tailWord_385978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386026 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_386026 : Nat := 118140960795 + 386026 * 2 ^ 59
def prefixEnd_386026 : Nat := 4983230072969 + 3 ^ 40 * 386026 * 2
def baseEnd_386026 : Nat := 176192785006766137955293

theorem tailTrace_386026 : CollatzResearch.WordTrace tailWord_386026 prefixEnd_386026 176192785006766137955293 := by
  unfold tailWord_386026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519881224875301209278483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9386349933000803224742621 3519881224875301209278483)
  ·
    refine ⟨5279821837312951813917725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519881224875301209278483 5279821837312951813917725)
    ·
      refine ⟨1979933188992356930219147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5279821837312951813917725 1979933188992356930219147)
      ·
        refine ⟨2969899783488535395328721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979933188992356930219147 2969899783488535395328721)
        ·
          refine ⟨2227424837616401546496541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2969899783488535395328721 2227424837616401546496541)
          ·
            refine ⟨835284314106150579936203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2227424837616401546496541 835284314106150579936203)
            ·
              refine ⟨1252926471159225869904305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835284314106150579936203 1252926471159225869904305)
              ·
                refine ⟨939694853369419402428229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252926471159225869904305 939694853369419402428229)
                ·
                  refine ⟨176192785006766137955293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939694853369419402428229 176192785006766137955293)
                  ·
                    rfl

theorem cell20_386026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_386026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386026 prefixEnd_386026 := by exact prefixLift 386026
  have htrace : WordTrace (prefixWord ++ tailWord_386026) baseStart_386026 baseEnd_386026 := by
    simpa [prefixWord, tailWord_386026, baseEnd_386026] using wordTrace_append hprefix tailTrace_386026
  have hstable : (prefixWord ++ tailWord_386026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386026).length < 2 ^ (prefixWord ++ tailWord_386026).sum := by decide
  have hdescent : baseEnd_386026 < baseStart_386026 := by decide
  rcases family_descends (prefixWord ++ tailWord_386026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386085 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_386085 : Nat := 118140960795 + 386085 * 2 ^ 59
def prefixEnd_386085 : Nat := 4983230072969 + 3 ^ 40 * 386085 * 2
def baseEnd_386085 : Nat := 176219714214424154988385

theorem tailTrace_386085 : CollatzResearch.WordTrace tailWord_386085 prefixEnd_386085 176219714214424154988385 := by
  unfold tailWord_386085
  simp only [CollatzResearch.WordTrace]
  refine ⟨14081676806287457913511709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9387784537524971942341139 14081676806287457913511709)
  ·
    refine ⟨5280628802357796717566891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14081676806287457913511709 5280628802357796717566891)
    ·
      refine ⟨7920943203536695076350337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280628802357796717566891 7920943203536695076350337)
      ·
        refine ⟨5940707402652521307262753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7920943203536695076350337 5940707402652521307262753)
        ·
          refine ⟨4455530551989390980447065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940707402652521307262753 4455530551989390980447065)
          ·
            refine ⟨3341647913992043235335299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4455530551989390980447065 3341647913992043235335299)
            ·
              refine ⟨5012471870988064853002949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341647913992043235335299 5012471870988064853002949)
              ·
                refine ⟨939838475810262159938053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5012471870988064853002949 939838475810262159938053)
                ·
                  refine ⟨176219714214424154988385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939838475810262159938053 176219714214424154988385)
                  ·
                    rfl

theorem cell20_386085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_386085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386085 prefixEnd_386085 := by exact prefixLift 386085
  have htrace : WordTrace (prefixWord ++ tailWord_386085) baseStart_386085 baseEnd_386085 := by
    simpa [prefixWord, tailWord_386085, baseEnd_386085] using wordTrace_append hprefix tailTrace_386085
  have hstable : (prefixWord ++ tailWord_386085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386085).length < 2 ^ (prefixWord ++ tailWord_386085).sum := by decide
  have hdescent : baseEnd_386085 < baseStart_386085 := by decide
  rcases family_descends (prefixWord ++ tailWord_386085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386092 : List Nat := [2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_386092 : Nat := 118140960795 + 386092 * 2 ^ 59
def prefixEnd_386092 : Nat := 4983230072969 + 3 ^ 40 * 386092 * 2
def baseEnd_386092 : Nat := 58740969735054413918341

theorem tailTrace_386092 : CollatzResearch.WordTrace tailWord_386092 prefixEnd_386092 58740969735054413918341 := by
  unfold tailWord_386092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7040966058631049054508265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9387954744841398739344353 7040966058631049054508265)
  ·
    refine ⟨5280724543973286790881199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7040966058631049054508265 5280724543973286790881199)
    ·
      refine ⟨7921086815959930186321799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280724543973286790881199 7921086815959930186321799)
      ·
        refine ⟨11881630223939895279482699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921086815959930186321799 11881630223939895279482699)
        ·
          refine ⟨17822445335909842919224049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11881630223939895279482699 17822445335909842919224049)
          ·
            refine ⟨13366834001932382189418037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17822445335909842919224049 13366834001932382189418037)
            ·
              refine ⟨1253140687681160830257941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13366834001932382189418037 1253140687681160830257941)
              ·
                refine ⟨58740969735054413918341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1253140687681160830257941 58740969735054413918341)
                ·
                  rfl

theorem cell20_386092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_386092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386092 prefixEnd_386092 := by exact prefixLift 386092
  have htrace : WordTrace (prefixWord ++ tailWord_386092) baseStart_386092 baseEnd_386092 := by
    simpa [prefixWord, tailWord_386092, baseEnd_386092] using wordTrace_append hprefix tailTrace_386092
  have hstable : (prefixWord ++ tailWord_386092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386092).length < 2 ^ (prefixWord ++ tailWord_386092).sum := by decide
  have hdescent : baseEnd_386092 < baseStart_386092 := by decide
  rcases family_descends (prefixWord ++ tailWord_386092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386109 : List Nat := [1, 4, 1, 3, 1, 4, 6]
def baseStart_386109 : Nat := 118140960795 + 386109 * 2 ^ 59
def prefixEnd_386109 : Nat := 4983230072969 + 3 ^ 40 * 386109 * 2
def baseEnd_386109 : Nat := 19581185385376304243143

theorem tailTrace_386109 : CollatzResearch.WordTrace tailWord_386109 prefixEnd_386109 19581185385376304243143 := by
  unfold tailWord_386109
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082552158200510012385381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9388368105467006674923587 14082552158200510012385381)
  ·
    refine ⟨2640478529662595627322259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14082552158200510012385381 2640478529662595627322259)
    ·
      refine ⟨3960717794493893440983389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640478529662595627322259 3960717794493893440983389)
      ·
        refine ⟨1485269172935210040368771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3960717794493893440983389 1485269172935210040368771)
        ·
          refine ⟨2227903759402815060553157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1485269172935210040368771 2227903759402815060553157)
          ·
            refine ⟨417731954888027823853717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2227903759402815060553157 417731954888027823853717)
            ·
              refine ⟨19581185385376304243143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 417731954888027823853717 19581185385376304243143)
              ·
                rfl

theorem cell20_386109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_386109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386109 prefixEnd_386109 := by exact prefixLift 386109
  have htrace : WordTrace (prefixWord ++ tailWord_386109) baseStart_386109 baseEnd_386109 := by
    simpa [prefixWord, tailWord_386109, baseEnd_386109] using wordTrace_append hprefix tailTrace_386109
  have hstable : (prefixWord ++ tailWord_386109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386109).length < 2 ^ (prefixWord ++ tailWord_386109).sum := by decide
  have hdescent : baseEnd_386109 < baseStart_386109 := by decide
  rcases family_descends (prefixWord ++ tailWord_386109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386137 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_386137 : Nat := 118140960795 + 386137 * 2 ^ 59
def prefixEnd_386137 : Nat := 4983230072969 + 3 ^ 40 * 386137 * 2
def baseEnd_386137 : Nat := 176243448431343085254839

theorem tailTrace_386137 : CollatzResearch.WordTrace tailWord_386137 prefixEnd_386137 176243448431343085254839 := by
  unfold tailWord_386137
  simp only [CollatzResearch.WordTrace]
  refine ⟨14083573402099070794404665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9389048934732713862936443 14083573402099070794404665)
  ·
    refine ⟨10562680051574303095803499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14083573402099070794404665 10562680051574303095803499)
    ·
      refine ⟨15844020077361454643705249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10562680051574303095803499 15844020077361454643705249)
      ·
        refine ⟨11883015058021090982778937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15844020077361454643705249 11883015058021090982778937)
        ·
          refine ⟨8912261293515818237084203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11883015058021090982778937 8912261293515818237084203)
          ·
            refine ⟨13368391940273727355626305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912261293515818237084203 13368391940273727355626305)
            ·
              refine ⟨10026293955205295516719729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13368391940273727355626305 10026293955205295516719729)
              ·
                refine ⟨7519720466403971637539797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10026293955205295516719729 7519720466403971637539797)
                ·
                  refine ⟨176243448431343085254839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7519720466403971637539797 176243448431343085254839)
                  ·
                    rfl

theorem cell20_386137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_386137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386137 prefixEnd_386137 := by exact prefixLift 386137
  have htrace : WordTrace (prefixWord ++ tailWord_386137) baseStart_386137 baseEnd_386137 := by
    simpa [prefixWord, tailWord_386137, baseEnd_386137] using wordTrace_append hprefix tailTrace_386137
  have hstable : (prefixWord ++ tailWord_386137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386137).length < 2 ^ (prefixWord ++ tailWord_386137).sum := by decide
  have hdescent : baseEnd_386137 < baseStart_386137 := by decide
  rcases family_descends (prefixWord ++ tailWord_386137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386185 : List Nat := [1, 2, 1, 1, 4, 5, 1, 5]
def baseStart_386185 : Nat := 118140960795 + 386185 * 2 ^ 59
def prefixEnd_386185 : Nat := 4983230072969 + 3 ^ 40 * 386185 * 2
def baseEnd_386185 : Nat := 58755118979756083884881

theorem tailTrace_386185 : CollatzResearch.WordTrace tailWord_386185 prefixEnd_386185 58755118979756083884881 := by
  unfold tailWord_386185
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085324105925174992152009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9390216070616783328101339 14085324105925174992152009)
  ·
    refine ⟨10563993079443881244114007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14085324105925174992152009 10563993079443881244114007)
    ·
      refine ⟨15845989619165821866171011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10563993079443881244114007 15845989619165821866171011)
      ·
        refine ⟨23768984428748732799256517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15845989619165821866171011 23768984428748732799256517)
        ·
          refine ⟨4456684580390387399860597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23768984428748732799256517 4456684580390387399860597)
          ·
            refine ⟨417814179411598818736931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4456684580390387399860597 417814179411598818736931)
            ·
              refine ⟨626721269117398228105397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417814179411598818736931 626721269117398228105397)
              ·
                refine ⟨58755118979756083884881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626721269117398228105397 58755118979756083884881)
                ·
                  rfl

theorem cell20_386185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_386185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386185 prefixEnd_386185 := by exact prefixLift 386185
  have htrace : WordTrace (prefixWord ++ tailWord_386185) baseStart_386185 baseEnd_386185 := by
    simpa [prefixWord, tailWord_386185, baseEnd_386185] using wordTrace_append hprefix tailTrace_386185
  have hstable : (prefixWord ++ tailWord_386185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386185).length < 2 ^ (prefixWord ++ tailWord_386185).sum := by decide
  have hdescent : baseEnd_386185 < baseStart_386185 := by decide
  rcases family_descends (prefixWord ++ tailWord_386185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386199 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_386199 : Nat := 118140960795 + 386199 * 2 ^ 59
def prefixEnd_386199 : Nat := 4983230072969 + 3 ^ 40 * 386199 * 2
def baseEnd_386199 : Nat := 176271746920746425187919

theorem tailTrace_386199 : CollatzResearch.WordTrace tailWord_386199 prefixEnd_386199 176271746920746425187919 := by
  unfold tailWord_386199
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085834727874455383161651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9390556485249636922107767 14085834727874455383161651)
  ·
    refine ⟨21128752091811683074742477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14085834727874455383161651 21128752091811683074742477)
    ·
      refine ⟨7923282034429381153028429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21128752091811683074742477 7923282034429381153028429)
      ·
        refine ⟨2971230762911017932385661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7923282034429381153028429 2971230762911017932385661)
        ·
          refine ⟨1114211536091631724644623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2971230762911017932385661 1114211536091631724644623)
          ·
            refine ⟨1671317304137447586966935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114211536091631724644623 1671317304137447586966935)
            ·
              refine ⟨2506975956206171380450403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671317304137447586966935 2506975956206171380450403)
              ·
                refine ⟨3760463934309257070675605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506975956206171380450403 3760463934309257070675605)
                ·
                  refine ⟨176271746920746425187919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3760463934309257070675605 176271746920746425187919)
                  ·
                    rfl

theorem cell20_386199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_386199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386199 prefixEnd_386199 := by exact prefixLift 386199
  have htrace : WordTrace (prefixWord ++ tailWord_386199) baseStart_386199 baseEnd_386199 := by
    simpa [prefixWord, tailWord_386199, baseEnd_386199] using wordTrace_append hprefix tailTrace_386199
  have hstable : (prefixWord ++ tailWord_386199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386199).length < 2 ^ (prefixWord ++ tailWord_386199).sum := by decide
  have hdescent : baseEnd_386199 < baseStart_386199 := by decide
  rcases family_descends (prefixWord ++ tailWord_386199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386202 : List Nat := [3, 1, 1, 5, 1, 2, 3, 4]
def baseStart_386202 : Nat := 118140960795 + 386202 * 2 ^ 59
def prefixEnd_386202 : Nat := 4983230072969 + 3 ^ 40 * 386202 * 2
def baseEnd_386202 : Nat := 58757705400830582695969

theorem tailTrace_386202 : CollatzResearch.WordTrace tailWord_386202 prefixEnd_386202 58757705400830582695969 := by
  unfold tailWord_386202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521486036715896723880215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9390629431242391263680573 3521486036715896723880215)
  ·
    refine ⟨5282229055073845085820323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521486036715896723880215 5282229055073845085820323)
    ·
      refine ⟨7923343582610767628730485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5282229055073845085820323 7923343582610767628730485)
      ·
        refine ⟨742813460869759465193483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7923343582610767628730485 742813460869759465193483)
        ·
          refine ⟨1114220191304639197790225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742813460869759465193483 1114220191304639197790225)
          ·
            refine ⟨835665143478479398342669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114220191304639197790225 835665143478479398342669)
            ·
              refine ⟨313374428804429774378501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 835665143478479398342669 313374428804429774378501)
              ·
                refine ⟨58757705400830582695969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313374428804429774378501 58757705400830582695969)
                ·
                  rfl

theorem cell20_386202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_386202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386202 prefixEnd_386202 := by exact prefixLift 386202
  have htrace : WordTrace (prefixWord ++ tailWord_386202) baseStart_386202 baseEnd_386202 := by
    simpa [prefixWord, tailWord_386202, baseEnd_386202] using wordTrace_append hprefix tailTrace_386202
  have hstable : (prefixWord ++ tailWord_386202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386202).length < 2 ^ (prefixWord ++ tailWord_386202).sum := by decide
  have hdescent : baseEnd_386202 < baseStart_386202 := by decide
  rcases family_descends (prefixWord ++ tailWord_386202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386237 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_386237 : Nat := 118140960795 + 386237 * 2 ^ 59
def prefixEnd_386237 : Nat := 4983230072969 + 3 ^ 40 * 386237 * 2
def baseEnd_386237 : Nat := 176289091156187181921097

theorem tailTrace_386237 : CollatzResearch.WordTrace tailWord_386237 prefixEnd_386237 176289091156187181921097 := by
  unfold tailWord_386237
  simp only [CollatzResearch.WordTrace]
  refine ⟨14087220701736787873044965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9391480467824525248696643 14087220701736787873044965)
  ·
    refine ⟨2641353881575647726195931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14087220701736787873044965 2641353881575647726195931)
    ·
      refine ⟨3962030822363471589293897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641353881575647726195931 3962030822363471589293897)
      ·
        refine ⟨2971523116772603691970423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3962030822363471589293897 2971523116772603691970423)
        ·
          refine ⟨4457284675158905537955635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971523116772603691970423 4457284675158905537955635)
          ·
            refine ⟨6685927012738358306933453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457284675158905537955635 6685927012738358306933453)
            ·
              refine ⟨2507222629776884365100045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6685927012738358306933453 2507222629776884365100045)
              ·
                refine ⟨940208486166331636912517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2507222629776884365100045 940208486166331636912517)
                ·
                  refine ⟨176289091156187181921097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940208486166331636912517 176289091156187181921097)
                  ·
                    rfl

theorem cell20_386237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_386237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386237 prefixEnd_386237 := by exact prefixLift 386237
  have htrace : WordTrace (prefixWord ++ tailWord_386237) baseStart_386237 baseEnd_386237 := by
    simpa [prefixWord, tailWord_386237, baseEnd_386237] using wordTrace_append hprefix tailTrace_386237
  have hstable : (prefixWord ++ tailWord_386237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386237).length < 2 ^ (prefixWord ++ tailWord_386237).sum := by decide
  have hdescent : baseEnd_386237 < baseStart_386237 := by decide
  rcases family_descends (prefixWord ++ tailWord_386237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386253 : List Nat := [1, 6, 2, 2, 2, 1, 2, 4]
def baseStart_386253 : Nat := 118140960795 + 386253 * 2 ^ 59
def prefixEnd_386253 : Nat := 4983230072969 + 3 ^ 40 * 386253 * 2
def baseEnd_386253 : Nat := 58765464664054079129233

theorem tailTrace_386253 : CollatzResearch.WordTrace tailWord_386253 prefixEnd_386253 58765464664054079129233 := by
  unfold tailWord_386253
  simp only [CollatzResearch.WordTrace]
  refine ⟨14087804269678822605627413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9391869513119215070418275 14087804269678822605627413)
  ·
    refine ⟨660365825141194809638785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14087804269678822605627413 660365825141194809638785)
    ·
      refine ⟨495274368855896107229089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660365825141194809638785 495274368855896107229089)
      ·
        refine ⟨371455776641922080421817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495274368855896107229089 371455776641922080421817)
        ·
          refine ⟨278591832481441560316363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371455776641922080421817 278591832481441560316363)
          ·
            refine ⟨417887748722162340474545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278591832481441560316363 417887748722162340474545)
            ·
              refine ⟨313415811541621755355909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417887748722162340474545 313415811541621755355909)
              ·
                refine ⟨58765464664054079129233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313415811541621755355909 58765464664054079129233)
                ·
                  rfl

theorem cell20_386253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].length) (baseStart_386253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386253 prefixEnd_386253 := by exact prefixLift 386253
  have htrace : WordTrace (prefixWord ++ tailWord_386253) baseStart_386253 baseEnd_386253 := by
    simpa [prefixWord, tailWord_386253, baseEnd_386253] using wordTrace_append hprefix tailTrace_386253
  have hstable : (prefixWord ++ tailWord_386253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386253).length < 2 ^ (prefixWord ++ tailWord_386253).sum := by decide
  have hdescent : baseEnd_386253 < baseStart_386253 := by decide
  rcases family_descends (prefixWord ++ tailWord_386253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386261 : List Nat := [1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_386261 : Nat := 118140960795 + 386261 * 2 ^ 59
def prefixEnd_386261 : Nat := 4983230072969 + 3 ^ 40 * 386261 * 2
def baseEnd_386261 : Nat := 58766681803383255040333

theorem tailTrace_386261 : CollatzResearch.WordTrace tailWord_386261 prefixEnd_386261 58766681803383255040333 := by
  unfold tailWord_386261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14088096053649839971918637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9392064035766559981279091 14088096053649839971918637)
  ·
    refine ⟨5283036020118689989469489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14088096053649839971918637 5283036020118689989469489)
    ·
      refine ⟨3962277015089017492102117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5283036020118689989469489 3962277015089017492102117)
      ·
        refine ⟨742926940329190779769147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3962277015089017492102117 742926940329190779769147)
        ·
          refine ⟨1114390410493786169653721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742926940329190779769147 1114390410493786169653721)
          ·
            refine ⟨835792807870339627240291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114390410493786169653721 835792807870339627240291)
            ·
              refine ⟨1253689211805509440860437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835792807870339627240291 1253689211805509440860437)
              ·
                refine ⟨58766681803383255040333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1253689211805509440860437 58766681803383255040333)
                ·
                  rfl

theorem cell20_386261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_386261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386261 prefixEnd_386261 := by exact prefixLift 386261
  have htrace : WordTrace (prefixWord ++ tailWord_386261) baseStart_386261 baseEnd_386261 := by
    simpa [prefixWord, tailWord_386261, baseEnd_386261] using wordTrace_append hprefix tailTrace_386261
  have hstable : (prefixWord ++ tailWord_386261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386261).length < 2 ^ (prefixWord ++ tailWord_386261).sum := by decide
  have hdescent : baseEnd_386261 < baseStart_386261 := by decide
  rcases family_descends (prefixWord ++ tailWord_386261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386282 : List Nat := [3, 1, 3, 1, 1, 3, 8]
def baseStart_386282 : Nat := 118140960795 + 386282 * 2 ^ 59
def prefixEnd_386282 : Nat := 4983230072969 + 3 ^ 40 * 386282 * 2
def baseEnd_386282 : Nat := 19589958931374113935657

theorem tailTrace_386282 : CollatzResearch.WordTrace tailWord_386282 prefixEnd_386282 19589958931374113935657 := by
  unfold tailWord_386282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522215496643440139608275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9392574657715840372288733 3522215496643440139608275)
  ·
    refine ⟨5283323244965160209412413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3522215496643440139608275 5283323244965160209412413)
    ·
      refine ⟨1981246216861935078529655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5283323244965160209412413 1981246216861935078529655)
      ·
        refine ⟨2971869325292902617794483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981246216861935078529655 2971869325292902617794483)
        ·
          refine ⟨4457803987939353926691725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971869325292902617794483 4457803987939353926691725)
          ·
            refine ⟨1671676495477257722509397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4457803987939353926691725 1671676495477257722509397)
            ·
              refine ⟨19589958931374113935657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1671676495477257722509397 19589958931374113935657)
              ·
                rfl

theorem cell20_386282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_386282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386282 prefixEnd_386282 := by exact prefixLift 386282
  have htrace : WordTrace (prefixWord ++ tailWord_386282) baseStart_386282 baseEnd_386282 := by
    simpa [prefixWord, tailWord_386282, baseEnd_386282] using wordTrace_append hprefix tailTrace_386282
  have hstable : (prefixWord ++ tailWord_386282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386282).length < 2 ^ (prefixWord ++ tailWord_386282).sum := by decide
  have hdescent : baseEnd_386282 < baseStart_386282 := by decide
  rcases family_descends (prefixWord ++ tailWord_386282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386302 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_386302 : Nat := 118140960795 + 386302 * 2 ^ 59
def prefixEnd_386302 : Nat := 4983230072969 + 3 ^ 40 * 386302 * 2
def baseEnd_386302 : Nat := 176318758927335844754165

theorem tailTrace_386302 : CollatzResearch.WordTrace tailWord_386302 prefixEnd_386302 176318758927335844754165 := by
  unfold tailWord_386302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761198930812662996770145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9393060964334202649440773 1761198930812662996770145)
  ·
    refine ⟨1320899198109497247577609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1761198930812662996770145 1320899198109497247577609)
    ·
      refine ⟨990674398582122935683207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1320899198109497247577609 990674398582122935683207)
      ·
        refine ⟨1486011597873184403524811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990674398582122935683207 1486011597873184403524811)
        ·
          refine ⟨2229017396809776605287217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486011597873184403524811 2229017396809776605287217)
          ·
            refine ⟨1671763047607332453965413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229017396809776605287217 1671763047607332453965413)
            ·
              refine ⟨313455571426374835118515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1671763047607332453965413 313455571426374835118515)
              ·
                refine ⟨470183357139562252677773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313455571426374835118515 470183357139562252677773)
                ·
                  refine ⟨176318758927335844754165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470183357139562252677773 176318758927335844754165)
                  ·
                    rfl

theorem cell20_386302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_386302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386302 prefixEnd_386302 := by exact prefixLift 386302
  have htrace : WordTrace (prefixWord ++ tailWord_386302) baseStart_386302 baseEnd_386302 := by
    simpa [prefixWord, tailWord_386302, baseEnd_386302] using wordTrace_append hprefix tailTrace_386302
  have hstable : (prefixWord ++ tailWord_386302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386302).length < 2 ^ (prefixWord ++ tailWord_386302).sum := by decide
  have hdescent : baseEnd_386302 < baseStart_386302 := by decide
  rcases family_descends (prefixWord ++ tailWord_386302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386375 : List Nat := [1, 1, 4, 1, 2, 4, 3, 4]
def baseStart_386375 : Nat := 118140960795 + 386375 * 2 ^ 59
def prefixEnd_386375 : Nat := 4983230072969 + 3 ^ 40 * 386375 * 2
def baseEnd_386375 : Nat := 58784026038824011773511

theorem tailTrace_386375 : CollatzResearch.WordTrace tailWord_386375 prefixEnd_386375 58784026038824011773511 := by
  unfold tailWord_386375
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092253975236837441568579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9394835983491224961045719 14092253975236837441568579)
  ·
    refine ⟨21138380962855256162352869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14092253975236837441568579 21138380962855256162352869)
    ·
      refine ⟨3963446430535360530441163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21138380962855256162352869 3963446430535360530441163)
      ·
        refine ⟨5945169645803040795661745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963446430535360530441163 5945169645803040795661745)
        ·
          refine ⟨4458877234352280596746309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5945169645803040795661745 4458877234352280596746309)
          ·
            refine ⟨836039481441052611889933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4458877234352280596746309 836039481441052611889933)
            ·
              refine ⟨313514805540394729458725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836039481441052611889933 313514805540394729458725)
              ·
                refine ⟨58784026038824011773511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313514805540394729458725 58784026038824011773511)
                ·
                  rfl

theorem cell20_386375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_386375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386375 prefixEnd_386375 := by exact prefixLift 386375
  have htrace : WordTrace (prefixWord ++ tailWord_386375) baseStart_386375 baseEnd_386375 := by
    simpa [prefixWord, tailWord_386375, baseEnd_386375] using wordTrace_append hprefix tailTrace_386375
  have hstable : (prefixWord ++ tailWord_386375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386375).length < 2 ^ (prefixWord ++ tailWord_386375).sum := by decide
  have hdescent : baseEnd_386375 < baseStart_386375 := by decide
  rcases family_descends (prefixWord ++ tailWord_386375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386381 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 2]
def baseStart_386381 : Nat := 118140960795 + 386381 * 2 ^ 59
def prefixEnd_386381 : Nat := 4983230072969 + 3 ^ 40 * 386381 * 2
def baseEnd_386381 : Nat := 176354816679962681120509

theorem tailTrace_386381 : CollatzResearch.WordTrace tailWord_386381 prefixEnd_386381 176354816679962681120509 := by
  unfold tailWord_386381
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092472813215100466286997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9394981875476733644191331 14092472813215100466286997)
  ·
    refine ⟨660584663119457834357203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14092472813215100466286997 660584663119457834357203)
    ·
      refine ⟨990876994679186751535805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660584663119457834357203 990876994679186751535805)
      ·
        refine ⟨371578873004695031825927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 990876994679186751535805 371578873004695031825927)
        ·
          refine ⟨557368309507042547738891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371578873004695031825927 557368309507042547738891)
          ·
            refine ⟨836052464260563821608337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557368309507042547738891 836052464260563821608337)
            ·
              refine ⟨627039348195422866206253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836052464260563821608337 627039348195422866206253)
              ·
                refine ⟨235139755573283574827345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 627039348195422866206253 235139755573283574827345)
                ·
                  refine ⟨176354816679962681120509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235139755573283574827345 176354816679962681120509)
                  ·
                    rfl

theorem cell20_386381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_386381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386381 prefixEnd_386381 := by exact prefixLift 386381
  have htrace : WordTrace (prefixWord ++ tailWord_386381) baseStart_386381 baseEnd_386381 := by
    simpa [prefixWord, tailWord_386381, baseEnd_386381] using wordTrace_append hprefix tailTrace_386381
  have hstable : (prefixWord ++ tailWord_386381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386381).length < 2 ^ (prefixWord ++ tailWord_386381).sum := by decide
  have hdescent : baseEnd_386381 < baseStart_386381 := by decide
  rcases family_descends (prefixWord ++ tailWord_386381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386458 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_386458 : Nat := 118140960795 + 386458 * 2 ^ 59
def prefixEnd_386458 : Nat := 4983230072969 + 3 ^ 40 * 386458 * 2
def baseEnd_386458 : Nat := 176389961578092635553527

theorem tailTrace_386458 : CollatzResearch.WordTrace tailWord_386458 prefixEnd_386458 176389961578092635553527 := by
  unfold tailWord_386458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523820308484035654210007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9396854155957428411226685 3523820308484035654210007)
  ·
    refine ⟨5285730462726053481315011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3523820308484035654210007 5285730462726053481315011)
    ·
      refine ⟨7928595694089080221972517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5285730462726053481315011 7928595694089080221972517)
      ·
        refine ⟨1486611692641702541619847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7928595694089080221972517 1486611692641702541619847)
        ·
          refine ⟨2229917538962553812429771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486611692641702541619847 2229917538962553812429771)
          ·
            refine ⟨3344876308443830718644657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229917538962553812429771 3344876308443830718644657)
            ·
              refine ⟨2508657231332873038983493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344876308443830718644657 2508657231332873038983493)
              ·
                refine ⟨470373230874913694809405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2508657231332873038983493 470373230874913694809405)
                ·
                  refine ⟨176389961578092635553527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470373230874913694809405 176389961578092635553527)
                  ·
                    rfl

theorem cell20_386458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_386458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386458 prefixEnd_386458 := by exact prefixLift 386458
  have htrace : WordTrace (prefixWord ++ tailWord_386458) baseStart_386458 baseEnd_386458 := by
    simpa [prefixWord, tailWord_386458, baseEnd_386458] using wordTrace_append hprefix tailTrace_386458
  have hstable : (prefixWord ++ tailWord_386458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386458).length < 2 ^ (prefixWord ++ tailWord_386458).sum := by decide
  have hdescent : baseEnd_386458 < baseStart_386458 := by decide
  rcases family_descends (prefixWord ++ tailWord_386458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386569 : List Nat := [1, 2, 1, 1, 3, 1, 11]
def baseStart_386569 : Nat := 118140960795 + 386569 * 2 ^ 59
def prefixEnd_386569 : Nat := 4983230072969 + 3 ^ 40 * 386569 * 2
def baseEnd_386569 : Nat := 19604513889185509205897

theorem tailTrace_386569 : CollatzResearch.WordTrace tailWord_386569 prefixEnd_386569 19604513889185509205897 := by
  unfold tailWord_386569
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099329736534008574130761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9399553157689339049420507 14099329736534008574130761)
  ·
    refine ⟨10574497302400506430598071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14099329736534008574130761 10574497302400506430598071)
    ·
      refine ⟨15861745953600759645897107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10574497302400506430598071 15861745953600759645897107)
      ·
        refine ⟨23792618930401139468845661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15861745953600759645897107 23792618930401139468845661)
        ·
          refine ⟨8922232098900427300817123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23792618930401139468845661 8922232098900427300817123)
          ·
            refine ⟨13383348148350640951225685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8922232098900427300817123 13383348148350640951225685)
            ·
              refine ⟨19604513889185509205897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13383348148350640951225685 19604513889185509205897)
              ·
                rfl

theorem cell20_386569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_386569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386569 prefixEnd_386569 := by exact prefixLift 386569
  have htrace : WordTrace (prefixWord ++ tailWord_386569) baseStart_386569 baseEnd_386569 := by
    simpa [prefixWord, tailWord_386569, baseEnd_386569] using wordTrace_append hprefix tailTrace_386569
  have hstable : (prefixWord ++ tailWord_386569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386569).length < 2 ^ (prefixWord ++ tailWord_386569).sum := by decide
  have hdescent : baseEnd_386569 < baseStart_386569 := by decide
  rcases family_descends (prefixWord ++ tailWord_386569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386572 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_386572 : Nat := 118140960795 + 386572 * 2 ^ 59
def prefixEnd_386572 : Nat := 4983230072969 + 3 ^ 40 * 386572 * 2
def baseEnd_386572 : Nat := 176441994284414905753061

theorem tailTrace_386572 : CollatzResearch.WordTrace tailWord_386572 prefixEnd_386572 176441994284414905753061 := by
  unfold tailWord_386572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049719577761570043244985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9399626103682093390993313 7049719577761570043244985)
  ·
    refine ⟨5287289683321177532433739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7049719577761570043244985 5287289683321177532433739)
    ·
      refine ⟨7930934524981766298650609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287289683321177532433739 7930934524981766298650609)
      ·
        refine ⟨5948200893736324723987957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7930934524981766298650609 5948200893736324723987957)
        ·
          refine ⟨557643833787780442873871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5948200893736324723987957 557643833787780442873871)
          ·
            refine ⟨836465750681670664310807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557643833787780442873871 836465750681670664310807)
            ·
              refine ⟨1254698626022505996466211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836465750681670664310807 1254698626022505996466211)
              ·
                refine ⟨1882047939033758994699317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254698626022505996466211 1882047939033758994699317)
                ·
                  refine ⟨176441994284414905753061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1882047939033758994699317 176441994284414905753061)
                  ·
                    rfl

theorem cell20_386572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_386572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386572 prefixEnd_386572 := by exact prefixLift 386572
  have htrace : WordTrace (prefixWord ++ tailWord_386572) baseStart_386572 baseEnd_386572 := by
    simpa [prefixWord, tailWord_386572, baseEnd_386572] using wordTrace_append hprefix tailTrace_386572
  have hstable : (prefixWord ++ tailWord_386572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386572).length < 2 ^ (prefixWord ++ tailWord_386572).sum := by decide
  have hdescent : baseEnd_386572 < baseStart_386572 := by decide
  rcases family_descends (prefixWord ++ tailWord_386572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386579 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_386579 : Nat := 118140960795 + 386579 * 2 ^ 59
def prefixEnd_386579 : Nat := 4983230072969 + 3 ^ 40 * 386579 * 2
def baseEnd_386579 : Nat := 176445189275153992519699

theorem tailTrace_386579 : CollatzResearch.WordTrace tailWord_386579 prefixEnd_386579 176445189275153992519699 := by
  unfold tailWord_386579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099694466497780281994791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9399796310998520187996527 14099694466497780281994791)
  ·
    refine ⟨21149541699746670422992187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14099694466497780281994791 21149541699746670422992187)
    ·
      refine ⟨31724312549620005634488281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21149541699746670422992187 31724312549620005634488281)
      ·
        refine ⟨23793234412215004225866211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31724312549620005634488281 23793234412215004225866211)
        ·
          refine ⟨35689851618322506338799317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23793234412215004225866211 35689851618322506338799317)
          ·
            refine ⟨836480897304433742315609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35689851618322506338799317 836480897304433742315609)
            ·
              refine ⟨627360672978325306736707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836480897304433742315609 627360672978325306736707)
              ·
                refine ⟨941041009467487960105061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627360672978325306736707 941041009467487960105061)
                ·
                  refine ⟨176445189275153992519699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941041009467487960105061 176445189275153992519699)
                  ·
                    rfl

theorem cell20_386579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_386579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386579 prefixEnd_386579 := by exact prefixLift 386579
  have htrace : WordTrace (prefixWord ++ tailWord_386579) baseStart_386579 baseEnd_386579 := by
    simpa [prefixWord, tailWord_386579, baseEnd_386579] using wordTrace_append hprefix tailTrace_386579
  have hstable : (prefixWord ++ tailWord_386579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386579).length < 2 ^ (prefixWord ++ tailWord_386579).sum := by decide
  have hdescent : baseEnd_386579 < baseStart_386579 := by decide
  rcases family_descends (prefixWord ++ tailWord_386579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386589 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 3]
def baseStart_386589 : Nat := 118140960795 + 386589 * 2 ^ 59
def prefixEnd_386589 : Nat := 4983230072969 + 3 ^ 40 * 386589 * 2
def baseEnd_386589 : Nat := 176449753547638402186325

theorem tailTrace_386589 : CollatzResearch.WordTrace tailWord_386589 prefixEnd_386589 176449753547638402186325 := by
  unfold tailWord_386589
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100059196461551989858821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9400039464307701326572547 14100059196461551989858821)
  ·
    refine ⟨2643761099336540998098529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14100059196461551989858821 2643761099336540998098529)
    ·
      refine ⟨1982820824502405748573897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2643761099336540998098529 1982820824502405748573897)
      ·
        refine ⟨1487115618376804311430423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1982820824502405748573897 1487115618376804311430423)
        ·
          refine ⟨2230673427565206467145635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487115618376804311430423 2230673427565206467145635)
          ·
            refine ⟨3346010141347809700718453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230673427565206467145635 3346010141347809700718453)
            ·
              refine ⟨313688450751357159442355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3346010141347809700718453 313688450751357159442355)
              ·
                refine ⟨470532676127035739163533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313688450751357159442355 470532676127035739163533)
                ·
                  refine ⟨176449753547638402186325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470532676127035739163533 176449753547638402186325)
                  ·
                    rfl

theorem cell20_386589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_386589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386589 prefixEnd_386589 := by exact prefixLift 386589
  have htrace : WordTrace (prefixWord ++ tailWord_386589) baseStart_386589 baseEnd_386589 := by
    simpa [prefixWord, tailWord_386589, baseEnd_386589] using wordTrace_append hprefix tailTrace_386589
  have hstable : (prefixWord ++ tailWord_386589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386589).length < 2 ^ (prefixWord ++ tailWord_386589).sum := by decide
  have hdescent : baseEnd_386589 < baseStart_386589 := by decide
  rcases family_descends (prefixWord ++ tailWord_386589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386613 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 2]
def baseStart_386613 : Nat := 118140960795 + 386613 * 2 ^ 59
def prefixEnd_386613 : Nat := 4983230072969 + 3 ^ 40 * 386613 * 2
def baseEnd_386613 : Nat := 176460707801600985386227

theorem tailTrace_386613 : CollatzResearch.WordTrace tailWord_386613 prefixEnd_386613 176460707801600985386227 := by
  unfold tailWord_386613
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100934548374604088732493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9400623032249736059154995 14100934548374604088732493)
  ·
    refine ⟨5287850455640476533274685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14100934548374604088732493 5287850455640476533274685)
    ·
      refine ⟨1982943920865178699978007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5287850455640476533274685 1982943920865178699978007)
      ·
        refine ⟨2974415881297768049967011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982943920865178699978007 2974415881297768049967011)
        ·
          refine ⟨4461623821946652074950517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974415881297768049967011 4461623821946652074950517)
          ·
            refine ⟨418277233307498632026611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4461623821946652074950517 418277233307498632026611)
            ·
              refine ⟨627415849961247948039917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418277233307498632026611 627415849961247948039917)
              ·
                refine ⟨235280943735467980514969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 627415849961247948039917 235280943735467980514969)
                ·
                  refine ⟨176460707801600985386227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235280943735467980514969 176460707801600985386227)
                  ·
                    rfl

theorem cell20_386613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_386613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386613 prefixEnd_386613 := by exact prefixLift 386613
  have htrace : WordTrace (prefixWord ++ tailWord_386613) baseStart_386613 baseEnd_386613 := by
    simpa [prefixWord, tailWord_386613, baseEnd_386613] using wordTrace_append hprefix tailTrace_386613
  have hstable : (prefixWord ++ tailWord_386613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386613).length < 2 ^ (prefixWord ++ tailWord_386613).sum := by decide
  have hdescent : baseEnd_386613 < baseStart_386613 := by decide
  rcases family_descends (prefixWord ++ tailWord_386613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386630 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_386630 : Nat := 118140960795 + 386630 * 2 ^ 59
def prefixEnd_386630 : Nat := 4983230072969 + 3 ^ 40 * 386630 * 2
def baseEnd_386630 : Nat := 176468467064824481819491

theorem tailTrace_386630 : CollatzResearch.WordTrace tailWord_386630 prefixEnd_386630 176468467064824481819491 := by
  unfold tailWord_386630
  simp only [CollatzResearch.WordTrace]
  refine ⟨440673580916031749753167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9401036392875343994734229 440673580916031749753167)
  ·
    refine ⟨661010371374047624629751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 440673580916031749753167 661010371374047624629751)
    ·
      refine ⟨991515557061071436944627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661010371374047624629751 991515557061071436944627)
      ·
        refine ⟨1487273335591607155416941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991515557061071436944627 1487273335591607155416941)
        ·
          refine ⟨557727500846852683281353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1487273335591607155416941 557727500846852683281353)
          ·
            refine ⟨418295625635139512461015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557727500846852683281353 418295625635139512461015)
            ·
              refine ⟨627443438452709268691523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418295625635139512461015 627443438452709268691523)
              ·
                refine ⟨941165157679063903037285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627443438452709268691523 941165157679063903037285)
                ·
                  refine ⟨176468467064824481819491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941165157679063903037285 176468467064824481819491)
                  ·
                    rfl

theorem cell20_386630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_386630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386630 prefixEnd_386630 := by exact prefixLift 386630
  have htrace : WordTrace (prefixWord ++ tailWord_386630) baseStart_386630 baseEnd_386630 := by
    simpa [prefixWord, tailWord_386630, baseEnd_386630] using wordTrace_append hprefix tailTrace_386630
  have hstable : (prefixWord ++ tailWord_386630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386630).length < 2 ^ (prefixWord ++ tailWord_386630).sum := by decide
  have hdescent : baseEnd_386630 < baseStart_386630 := by decide
  rcases family_descends (prefixWord ++ tailWord_386630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386689 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 2]
def baseStart_386689 : Nat := 118140960795 + 386689 * 2 ^ 59
def prefixEnd_386689 : Nat := 4983230072969 + 3 ^ 40 * 386689 * 2
def baseEnd_386689 : Nat := 176495396272482498852583

theorem tailTrace_386689 : CollatzResearch.WordTrace tailWord_386689 prefixEnd_386689 176495396272482498852583 := by
  unfold tailWord_386689
  simp only [CollatzResearch.WordTrace]
  refine ⟨14103706496099269068499121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9402470997399512712332747 14103706496099269068499121)
  ·
    refine ⟨10577779872074451801374341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14103706496099269068499121 10577779872074451801374341)
    ·
      refine ⟨1983333726013959712757689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10577779872074451801374341 1983333726013959712757689)
      ·
        refine ⟨1487500294510469784568267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1983333726013959712757689 1487500294510469784568267)
        ·
          refine ⟨2231250441765704676852401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487500294510469784568267 2231250441765704676852401)
          ·
            refine ⟨1673437831324278507639301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231250441765704676852401 1673437831324278507639301)
            ·
              refine ⟨313769593373302220182369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1673437831324278507639301 313769593373302220182369)
              ·
                refine ⟨235327195029976665136777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313769593373302220182369 235327195029976665136777)
                ·
                  refine ⟨176495396272482498852583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235327195029976665136777 176495396272482498852583)
                  ·
                    rfl

theorem cell20_386689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_386689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386689 prefixEnd_386689 := by exact prefixLift 386689
  have htrace : WordTrace (prefixWord ++ tailWord_386689) baseStart_386689 baseEnd_386689 := by
    simpa [prefixWord, tailWord_386689, baseEnd_386689] using wordTrace_append hprefix tailTrace_386689
  have hstable : (prefixWord ++ tailWord_386689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386689).length < 2 ^ (prefixWord ++ tailWord_386689).sum := by decide
  have hdescent : baseEnd_386689 < baseStart_386689 := by decide
  rcases family_descends (prefixWord ++ tailWord_386689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386696 : List Nat := [2, 1, 3, 5, 1, 2, 1, 5]
def baseStart_386696 : Nat := 118140960795 + 386696 * 2 ^ 59
def prefixEnd_386696 : Nat := 4983230072969 + 3 ^ 40 * 386696 * 2
def baseEnd_386696 : Nat := 58832863754407195206407

theorem tailTrace_386696 : CollatzResearch.WordTrace tailWord_386696 prefixEnd_386696 58832863754407195206407 := by
  unfold tailWord_386696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051980903536954632001971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9402641204715939509335961 7051980903536954632001971)
  ·
    refine ⟨10577971355305431948002957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7051980903536954632001971 10577971355305431948002957)
    ·
      refine ⟨3966739258239536980501109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10577971355305431948002957 3966739258239536980501109)
      ·
        refine ⟨371881805459956591921979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3966739258239536980501109 371881805459956591921979)
        ·
          refine ⟨557822708189934887882969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371881805459956591921979 557822708189934887882969)
          ·
            refine ⟨418367031142451165912227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557822708189934887882969 418367031142451165912227)
            ·
              refine ⟨627550546713676748868341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418367031142451165912227 627550546713676748868341)
              ·
                refine ⟨58832863754407195206407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 627550546713676748868341 58832863754407195206407)
                ·
                  rfl

theorem cell20_386696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_386696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386696 prefixEnd_386696 := by exact prefixLift 386696
  have htrace : WordTrace (prefixWord ++ tailWord_386696) baseStart_386696 baseEnd_386696 := by
    simpa [prefixWord, tailWord_386696, baseEnd_386696] using wordTrace_append hprefix tailTrace_386696
  have hstable : (prefixWord ++ tailWord_386696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386696).length < 2 ^ (prefixWord ++ tailWord_386696).sum := by decide
  have hdescent : baseEnd_386696 < baseStart_386696 := by decide
  rcases family_descends (prefixWord ++ tailWord_386696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386748 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 2]
def baseStart_386748 : Nat := 118140960795 + 386748 * 2 ^ 59
def prefixEnd_386748 : Nat := 4983230072969 + 3 ^ 40 * 386748 * 2
def baseEnd_386748 : Nat := 176522325480140515885675

theorem tailTrace_386748 : CollatzResearch.WordTrace tailWord_386748 prefixEnd_386748 176522325480140515885675 := by
  unfold tailWord_386748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052929201442761072448449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9403905601923681429931265 7052929201442761072448449)
  ·
    refine ⟨5289696901082070804336337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7052929201442761072448449 5289696901082070804336337)
    ·
      refine ⟨3967272675811553103252253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5289696901082070804336337 3967272675811553103252253)
      ·
        refine ⟨1487727253429332413719595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3967272675811553103252253 1487727253429332413719595)
        ·
          refine ⟨2231590880143998620579393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487727253429332413719595 2231590880143998620579393)
          ·
            refine ⟨1673693160107998965434545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231590880143998620579393 1673693160107998965434545)
            ·
              refine ⟨1255269870080999224075909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673693160107998965434545 1255269870080999224075909)
              ·
                refine ⟨235363100640187354514233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1255269870080999224075909 235363100640187354514233)
                ·
                  refine ⟨176522325480140515885675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235363100640187354514233 176522325480140515885675)
                  ·
                    rfl

theorem cell20_386748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_386748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386748 prefixEnd_386748 := by exact prefixLift 386748
  have htrace : WordTrace (prefixWord ++ tailWord_386748) baseStart_386748 baseEnd_386748 := by
    simpa [prefixWord, tailWord_386748, baseEnd_386748] using wordTrace_append hprefix tailTrace_386748
  have hstable : (prefixWord ++ tailWord_386748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386748).length < 2 ^ (prefixWord ++ tailWord_386748).sum := by decide
  have hdescent : baseEnd_386748 < baseStart_386748 := by decide
  rcases family_descends (prefixWord ++ tailWord_386748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386754 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_386754 : Nat := 118140960795 + 386754 * 2 ^ 59
def prefixEnd_386754 : Nat := 4983230072969 + 3 ^ 40 * 386754 * 2
def baseEnd_386754 : Nat := 176525064043631161685651

theorem tailTrace_386754 : CollatzResearch.WordTrace tailWord_386754 prefixEnd_386754 176525064043631161685651 := by
  unfold tailWord_386754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526519310215946292403829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9404051493909190113076877 3526519310215946292403829)
  ·
    refine ⟨330611185332744964912859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3526519310215946292403829 330611185332744964912859)
    ·
      refine ⟨495916777999117447369289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330611185332744964912859 495916777999117447369289)
      ·
        refine ⟨371937583499338085526967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495916777999117447369289 371937583499338085526967)
        ·
          refine ⟨557906375249007128290451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371937583499338085526967 557906375249007128290451)
          ·
            refine ⟨836859562873510692435677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557906375249007128290451 836859562873510692435677)
            ·
              refine ⟨313822336077566509663379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836859562873510692435677 313822336077566509663379)
              ·
                refine ⟨470733504116349764495069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313822336077566509663379 470733504116349764495069)
                ·
                  refine ⟨176525064043631161685651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470733504116349764495069 176525064043631161685651)
                  ·
                    rfl

theorem cell20_386754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_386754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386754 prefixEnd_386754 := by exact prefixLift 386754
  have htrace : WordTrace (prefixWord ++ tailWord_386754) baseStart_386754 baseEnd_386754 := by
    simpa [prefixWord, tailWord_386754, baseEnd_386754] using wordTrace_append hprefix tailTrace_386754
  have hstable : (prefixWord ++ tailWord_386754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386754).length < 2 ^ (prefixWord ++ tailWord_386754).sum := by decide
  have hdescent : baseEnd_386754 < baseStart_386754 := by decide
  rcases family_descends (prefixWord ++ tailWord_386754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386759 : List Nat := [1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_386759 : Nat := 118140960795 + 386759 * 2 ^ 59
def prefixEnd_386759 : Nat := 4983230072969 + 3 ^ 40 * 386759 * 2
def baseEnd_386759 : Nat := 58842448726624455506321

theorem tailTrace_386759 : CollatzResearch.WordTrace tailWord_386759 prefixEnd_386759 58842448726624455506321 := by
  unfold tailWord_386759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106259605845671023547331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9404173070563780682364887 14106259605845671023547331)
  ·
    refine ⟨21159389408768506535320997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14106259605845671023547331 21159389408768506535320997)
    ·
      refine ⟨3967385514144094975372687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21159389408768506535320997 3967385514144094975372687)
      ·
        refine ⟨5951078271216142463059031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3967385514144094975372687 5951078271216142463059031)
        ·
          refine ⟨8926617406824213694588547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951078271216142463059031 8926617406824213694588547)
          ·
            refine ⟨13389926110236320541882821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8926617406824213694588547 13389926110236320541882821)
            ·
              refine ⟨2510611145669310101603029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13389926110236320541882821 2510611145669310101603029)
              ·
                refine ⟨58842448726624455506321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2510611145669310101603029 58842448726624455506321)
                ·
                  rfl

theorem cell20_386759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_386759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386759 prefixEnd_386759 := by exact prefixLift 386759
  have htrace : WordTrace (prefixWord ++ tailWord_386759) baseStart_386759 baseEnd_386759 := by
    simpa [prefixWord, tailWord_386759, baseEnd_386759] using wordTrace_append hprefix tailTrace_386759
  have hstable : (prefixWord ++ tailWord_386759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386759).length < 2 ^ (prefixWord ++ tailWord_386759).sum := by decide
  have hdescent : baseEnd_386759 < baseStart_386759 := by decide
  rcases family_descends (prefixWord ++ tailWord_386759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386772 : List Nat := [2, 4, 1, 3, 1, 3, 2, 4]
def baseStart_386772 : Nat := 118140960795 + 386772 * 2 ^ 59
def prefixEnd_386772 : Nat := 4983230072969 + 3 ^ 40 * 386772 * 2
def baseEnd_386772 : Nat := 58844426578034366361859

theorem tailTrace_386772 : CollatzResearch.WordTrace tailWord_386772 prefixEnd_386772 58844426578034366361859 := by
  unfold tailWord_386772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053366877399287121885285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9404489169865716162513713 7053366877399287121885285)
  ·
    refine ⟨1322506289512366335353491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7053366877399287121885285 1322506289512366335353491)
    ·
      refine ⟨1983759434268549503030237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322506289512366335353491 1983759434268549503030237)
      ·
        refine ⟨743909787850706063636339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1983759434268549503030237 743909787850706063636339)
        ·
          refine ⟨1115864681776059095454509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743909787850706063636339 1115864681776059095454509)
          ·
            refine ⟨418449255666022160795441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1115864681776059095454509 418449255666022160795441)
            ·
              refine ⟨313836941749516620596581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418449255666022160795441 313836941749516620596581)
              ·
                refine ⟨58844426578034366361859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313836941749516620596581 58844426578034366361859)
                ·
                  rfl

theorem cell20_386772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_386772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386772 prefixEnd_386772 := by exact prefixLift 386772
  have htrace : WordTrace (prefixWord ++ tailWord_386772) baseStart_386772 baseEnd_386772 := by
    simpa [prefixWord, tailWord_386772, baseEnd_386772] using wordTrace_append hprefix tailTrace_386772
  have hstable : (prefixWord ++ tailWord_386772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386772).length < 2 ^ (prefixWord ++ tailWord_386772).sum := by decide
  have hdescent : baseEnd_386772 < baseStart_386772 := by decide
  rcases family_descends (prefixWord ++ tailWord_386772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386807 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 2]
def baseStart_386807 : Nat := 118140960795 + 386807 * 2 ^ 59
def prefixEnd_386807 : Nat := 4983230072969 + 3 ^ 40 * 386807 * 2
def baseEnd_386807 : Nat := 176549254687798532918767

theorem tailTrace_386807 : CollatzResearch.WordTrace tailWord_386807 prefixEnd_386807 176549254687798532918767 := by
  unfold tailWord_386807
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108010309671775221294675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9405340206447850147529783 14108010309671775221294675)
  ·
    refine ⟨21162015464507662831942013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14108010309671775221294675 21162015464507662831942013)
    ·
      refine ⟨7935755799190373561978255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21162015464507662831942013 7935755799190373561978255)
      ·
        refine ⟨11903633698785560342967383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935755799190373561978255 11903633698785560342967383)
        ·
          refine ⟨17855450548178340514451075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11903633698785560342967383 17855450548178340514451075)
          ·
            refine ⟨26783175822267510771676613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17855450548178340514451075 26783175822267510771676613)
            ·
              refine ⟨5021845466675158269689365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26783175822267510771676613 5021845466675158269689365)
              ·
                refine ⟨235399006250398043891689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5021845466675158269689365 235399006250398043891689)
                ·
                  refine ⟨176549254687798532918767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235399006250398043891689 176549254687798532918767)
                  ·
                    rfl

theorem cell20_386807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 2].length) (baseStart_386807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386807 prefixEnd_386807 := by exact prefixLift 386807
  have htrace : WordTrace (prefixWord ++ tailWord_386807) baseStart_386807 baseEnd_386807 := by
    simpa [prefixWord, tailWord_386807, baseEnd_386807] using wordTrace_append hprefix tailTrace_386807
  have hstable : (prefixWord ++ tailWord_386807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386807).length < 2 ^ (prefixWord ++ tailWord_386807).sum := by decide
  have hdescent : baseEnd_386807 < baseStart_386807 := by decide
  rcases family_descends (prefixWord ++ tailWord_386807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386828 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_386828 : Nat := 118140960795 + 386828 * 2 ^ 59
def prefixEnd_386828 : Nat := 4983230072969 + 3 ^ 40 * 386828 * 2
def baseEnd_386828 : Nat := 176558839660015793218681

theorem tailTrace_386828 : CollatzResearch.WordTrace tailWord_386828 prefixEnd_386828 176558839660015793218681 := by
  unfold tailWord_386828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7054388121297847903904569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9405850828397130538539425 7054388121297847903904569)
  ·
    refine ⟨5290791090973385927928427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7054388121297847903904569 5290791090973385927928427)
    ·
      refine ⟨7936186636460078891892641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5290791090973385927928427 7936186636460078891892641)
      ·
        refine ⟨5952139977345059168919481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7936186636460078891892641 5952139977345059168919481)
        ·
          refine ⟨4464104983008794376689611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5952139977345059168919481 4464104983008794376689611)
          ·
            refine ⟨6696157474513191565034417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464104983008794376689611 6696157474513191565034417)
            ·
              refine ⟨5022118105884893673775813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696157474513191565034417 5022118105884893673775813)
              ·
                refine ⟨941647144853417563832965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5022118105884893673775813 941647144853417563832965)
                ·
                  refine ⟨176558839660015793218681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941647144853417563832965 176558839660015793218681)
                  ·
                    rfl

theorem cell20_386828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_386828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386828 prefixEnd_386828 := by exact prefixLift 386828
  have htrace : WordTrace (prefixWord ++ tailWord_386828) baseStart_386828 baseEnd_386828 := by
    simpa [prefixWord, tailWord_386828, baseEnd_386828] using wordTrace_append hprefix tailTrace_386828
  have hstable : (prefixWord ++ tailWord_386828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386828).length < 2 ^ (prefixWord ++ tailWord_386828).sum := by decide
  have hdescent : baseEnd_386828 < baseStart_386828 := by decide
  rcases family_descends (prefixWord ++ tailWord_386828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386869 : List Nat := [1, 3, 3, 1, 4, 2, 1, 5]
def baseStart_386869 : Nat := 118140960795 + 386869 * 2 ^ 59
def prefixEnd_386869 : Nat := 4983230072969 + 3 ^ 40 * 386869 * 2
def baseEnd_386869 : Nat := 58859184392400624283949

theorem tailTrace_386869 : CollatzResearch.WordTrace tailWord_386869 prefixEnd_386869 58859184392400624283949 := by
  unfold tailWord_386869
  simp only [CollatzResearch.WordTrace]
  refine ⟨14110271635447159810051661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9406847756964773206701107 14110271635447159810051661)
  ·
    refine ⟨5291351863292684928769373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14110271635447159810051661 5291351863292684928769373)
    ·
      refine ⟨1984256948734756848288515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5291351863292684928769373 1984256948734756848288515)
      ·
        refine ⟨2976385423102135272432773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984256948734756848288515 2976385423102135272432773)
        ·
          refine ⟨558072266831650363581145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2976385423102135272432773 558072266831650363581145)
          ·
            refine ⟨418554200123737772685859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558072266831650363581145 418554200123737772685859)
            ·
              refine ⟨627831300185606659028789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418554200123737772685859 627831300185606659028789)
              ·
                refine ⟨58859184392400624283949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 627831300185606659028789 58859184392400624283949)
                ·
                  rfl

theorem cell20_386869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_386869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386869 prefixEnd_386869 := by exact prefixLift 386869
  have htrace : WordTrace (prefixWord ++ tailWord_386869) baseStart_386869 baseEnd_386869 := by
    simpa [prefixWord, tailWord_386869, baseEnd_386869] using wordTrace_append hprefix tailTrace_386869
  have hstable : (prefixWord ++ tailWord_386869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386869).length < 2 ^ (prefixWord ++ tailWord_386869).sum := by decide
  have hdescent : baseEnd_386869 < baseStart_386869 := by decide
  rcases family_descends (prefixWord ++ tailWord_386869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386880 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_386880 : Nat := 118140960795 + 386880 * 2 ^ 59
def prefixEnd_386880 : Nat := 4983230072969 + 3 ^ 40 * 386880 * 2
def baseEnd_386880 : Nat := 176582573876934723485135

theorem tailTrace_386880 : CollatzResearch.WordTrace tailWord_386880 prefixEnd_386880 176582573876934723485135 := by
  unfold tailWord_386880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7055336419203654344351047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9407115225604872459134729 7055336419203654344351047)
  ·
    refine ⟨10583004628805481516526571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7055336419203654344351047 10583004628805481516526571)
    ·
      refine ⟨15874506943208222274789857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10583004628805481516526571 15874506943208222274789857)
      ·
        refine ⟨11905880207406166706092393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15874506943208222274789857 11905880207406166706092393)
        ·
          refine ⟨8929410155554625029569295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11905880207406166706092393 8929410155554625029569295)
          ·
            refine ⟨13394115233331937544353943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929410155554625029569295 13394115233331937544353943)
            ·
              refine ⟨20091172849997906316530915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13394115233331937544353943 20091172849997906316530915)
              ·
                refine ⟨30136759274996859474796373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20091172849997906316530915 30136759274996859474796373)
                ·
                  refine ⟨176582573876934723485135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30136759274996859474796373 176582573876934723485135)
                  ·
                    rfl

theorem cell20_386880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_386880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386880 prefixEnd_386880 := by exact prefixLift 386880
  have htrace : WordTrace (prefixWord ++ tailWord_386880) baseStart_386880 baseEnd_386880 := by
    simpa [prefixWord, tailWord_386880, baseEnd_386880] using wordTrace_append hprefix tailTrace_386880
  have hstable : (prefixWord ++ tailWord_386880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386880).length < 2 ^ (prefixWord ++ tailWord_386880).sum := by decide
  have hdescent : baseEnd_386880 < baseStart_386880 := by decide
  rcases family_descends (prefixWord ++ tailWord_386880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386890 : List Nat := [3, 1, 2, 1, 1, 1, 7, 4]
def baseStart_386890 : Nat := 118140960795 + 386890 * 2 ^ 59
def prefixEnd_386890 : Nat := 4983230072969 + 3 ^ 40 * 386890 * 2
def baseEnd_386890 : Nat := 58862379383139711050587

theorem tailTrace_386890 : CollatzResearch.WordTrace tailWord_386890 prefixEnd_386890 58862379383139711050587 := by
  unfold tailWord_386890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527759392092770099141531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9407358378914053597710749 3527759392092770099141531)
  ·
    refine ⟨5291639088139155148712297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3527759392092770099141531 5291639088139155148712297)
    ·
      refine ⟨3968729316104366361534223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5291639088139155148712297 3968729316104366361534223)
      ·
        refine ⟨5953093974156549542301335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968729316104366361534223 5953093974156549542301335)
        ·
          refine ⟨8929640961234824313452003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953093974156549542301335 8929640961234824313452003)
          ·
            refine ⟨13394461441852236470178005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929640961234824313452003 13394461441852236470178005)
            ·
              refine ⟨313932690043411792269797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13394461441852236470178005 313932690043411792269797)
              ·
                refine ⟨58862379383139711050587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313932690043411792269797 58862379383139711050587)
                ·
                  rfl

theorem cell20_386890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_386890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386890 prefixEnd_386890 := by exact prefixLift 386890
  have htrace : WordTrace (prefixWord ++ tailWord_386890) baseStart_386890 baseEnd_386890 := by
    simpa [prefixWord, tailWord_386890, baseEnd_386890] using wordTrace_append hprefix tailTrace_386890
  have hstable : (prefixWord ++ tailWord_386890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386890).length < 2 ^ (prefixWord ++ tailWord_386890).sum := by decide
  have hdescent : baseEnd_386890 < baseStart_386890 := by decide
  rcases family_descends (prefixWord ++ tailWord_386890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386900 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 2]
def baseStart_386900 : Nat := 118140960795 + 386900 * 2 ^ 59
def prefixEnd_386900 : Nat := 4983230072969 + 3 ^ 40 * 386900 * 2
def baseEnd_386900 : Nat := 176591702421903542818387

theorem tailTrace_386900 : CollatzResearch.WordTrace tailWord_386900 prefixEnd_386900 176591702421903542818387 := by
  unfold tailWord_386900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7055701149167426052215077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9407601532223234736286769 7055701149167426052215077)
  ·
    refine ⟨1322943965468892384790327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7055701149167426052215077 1322943965468892384790327)
    ·
      refine ⟨1984415948203338577185491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322943965468892384790327 1984415948203338577185491)
      ·
        refine ⟨2976623922305007865778237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984415948203338577185491 2976623922305007865778237)
        ·
          refine ⟨1116233970864377949666839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2976623922305007865778237 1116233970864377949666839)
          ·
            refine ⟨1674350956296566924500259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116233970864377949666839 1674350956296566924500259)
            ·
              refine ⟨2511526434444850386750389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674350956296566924500259 2511526434444850386750389)
              ·
                refine ⟨235455603229204723757849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2511526434444850386750389 235455603229204723757849)
                ·
                  refine ⟨176591702421903542818387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235455603229204723757849 176591702421903542818387)
                  ·
                    rfl

theorem cell20_386900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_386900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386900 prefixEnd_386900 := by exact prefixLift 386900
  have htrace : WordTrace (prefixWord ++ tailWord_386900) baseStart_386900 baseEnd_386900 := by
    simpa [prefixWord, tailWord_386900, baseEnd_386900] using wordTrace_append hprefix tailTrace_386900
  have hstable : (prefixWord ++ tailWord_386900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386900).length < 2 ^ (prefixWord ++ tailWord_386900).sum := by decide
  have hdescent : baseEnd_386900 < baseStart_386900 := by decide
  rcases family_descends (prefixWord ++ tailWord_386900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386911 : List Nat := [1, 1, 2, 3, 1, 5, 7]
def baseStart_386911 : Nat := 118140960795 + 386911 * 2 ^ 59
def prefixEnd_386911 : Nat := 4983230072969 + 3 ^ 40 * 386911 * 2
def baseEnd_386911 : Nat := 19621858124626265939075

theorem tailTrace_386911 : CollatzResearch.WordTrace tailWord_386911 prefixEnd_386911 19621858124626265939075 := by
  unfold tailWord_386911
  simp only [CollatzResearch.WordTrace]
  refine ⟨14111803501295000983080587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9407869000863333988720391 14111803501295000983080587)
  ·
    refine ⟨21167705251942501474620881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14111803501295000983080587 21167705251942501474620881)
    ·
      refine ⟨15875778938956876105965661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21167705251942501474620881 15875778938956876105965661)
      ·
        refine ⟨5953417102108828539737123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15875778938956876105965661 5953417102108828539737123)
        ·
          refine ⟨8930125653163242809605685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953417102108828539737123 8930125653163242809605685)
          ·
            refine ⟨837199279984054013400533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8930125653163242809605685 837199279984054013400533)
            ·
              refine ⟨19621858124626265939075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 837199279984054013400533 19621858124626265939075)
              ·
                rfl

theorem cell20_386911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_386911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386911 prefixEnd_386911 := by exact prefixLift 386911
  have htrace : WordTrace (prefixWord ++ tailWord_386911) baseStart_386911 baseEnd_386911 := by
    simpa [prefixWord, tailWord_386911, baseEnd_386911] using wordTrace_append hprefix tailTrace_386911
  have hstable : (prefixWord ++ tailWord_386911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386911).length < 2 ^ (prefixWord ++ tailWord_386911).sum := by decide
  have hdescent : baseEnd_386911 < baseStart_386911 := by decide
  rcases family_descends (prefixWord ++ tailWord_386911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386914 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_386914 : Nat := 118140960795 + 386914 * 2 ^ 59
def prefixEnd_386914 : Nat := 4983230072969 + 3 ^ 40 * 386914 * 2
def baseEnd_386914 : Nat := 176598092403381716351663

theorem tailTrace_386914 : CollatzResearch.WordTrace tailWord_386914 prefixEnd_386914 176598092403381716351663 := by
  unfold tailWord_386914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527978230071033123859949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9407941946856088330293197 3527978230071033123859949)
  ·
    refine ⟨1322991836276637421447481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3527978230071033123859949 1322991836276637421447481)
    ·
      refine ⟨992243877207478066085611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1322991836276637421447481 992243877207478066085611)
      ·
        refine ⟨1488365815811217099128417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992243877207478066085611 1488365815811217099128417)
        ·
          refine ⟨1116274361858412824346313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488365815811217099128417 1116274361858412824346313)
          ·
            refine ⟨837205771393809618259735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116274361858412824346313 837205771393809618259735)
            ·
              refine ⟨1255808657090714427389603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837205771393809618259735 1255808657090714427389603)
              ·
                refine ⟨1883712985636071641084405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255808657090714427389603 1883712985636071641084405)
                ·
                  refine ⟨176598092403381716351663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883712985636071641084405 176598092403381716351663)
                  ·
                    rfl

theorem cell20_386914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_386914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386914 prefixEnd_386914 := by exact prefixLift 386914
  have htrace : WordTrace (prefixWord ++ tailWord_386914) baseStart_386914 baseEnd_386914 := by
    simpa [prefixWord, tailWord_386914, baseEnd_386914] using wordTrace_append hprefix tailTrace_386914
  have hstable : (prefixWord ++ tailWord_386914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386914).length < 2 ^ (prefixWord ++ tailWord_386914).sum := by decide
  have hdescent : baseEnd_386914 < baseStart_386914 := by decide
  rcases family_descends (prefixWord ++ tailWord_386914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386945 : List Nat := [1, 2, 4, 4, 1, 1, 1, 6]
def baseStart_386945 : Nat := 118140960795 + 386945 * 2 ^ 59
def prefixEnd_386945 : Nat := 4983230072969 + 3 ^ 40 * 386945 * 2
def baseEnd_386945 : Nat := 58870747216027795439401

theorem tailTrace_386945 : CollatzResearch.WordTrace tailWord_386945 prefixEnd_386945 58870747216027795439401 := by
  unfold tailWord_386945
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113043583171824789818289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9408695722114549859878859 14113043583171824789818289)
  ·
    refine ⟨10584782687378868592363717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14113043583171824789818289 10584782687378868592363717)
    ·
      refine ⟨1984646753883537861068197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10584782687378868592363717 1984646753883537861068197)
      ·
        refine ⟨372121266353163348950287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1984646753883537861068197 372121266353163348950287)
        ·
          refine ⟨558181899529745023425431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372121266353163348950287 558181899529745023425431)
          ·
            refine ⟨837272849294617535138147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558181899529745023425431 837272849294617535138147)
            ·
              refine ⟨1255909273941926302707221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837272849294617535138147 1255909273941926302707221)
              ·
                refine ⟨58870747216027795439401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1255909273941926302707221 58870747216027795439401)
                ·
                  rfl

theorem cell20_386945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_386945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386945 prefixEnd_386945 := by exact prefixLift 386945
  have htrace : WordTrace (prefixWord ++ tailWord_386945) baseStart_386945 baseEnd_386945 := by
    simpa [prefixWord, tailWord_386945, baseEnd_386945] using wordTrace_append hprefix tailTrace_386945
  have hstable : (prefixWord ++ tailWord_386945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386945).length < 2 ^ (prefixWord ++ tailWord_386945).sum := by decide
  have hdescent : baseEnd_386945 < baseStart_386945 := by decide
  rcases family_descends (prefixWord ++ tailWord_386945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386949 : List Nat := [1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_386949 : Nat := 118140960795 + 386949 * 2 ^ 59
def prefixEnd_386949 : Nat := 4983230072969 + 3 ^ 40 * 386949 * 2
def baseEnd_386949 : Nat := 58871355785692383394951

theorem tailTrace_386949 : CollatzResearch.WordTrace tailWord_386949 prefixEnd_386949 58871355785692383394951 := by
  unfold tailWord_386949
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113189475157333472963901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9408792983438222315309267 14113189475157333472963901)
  ·
    refine ⟨5292446053184000052361463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14113189475157333472963901 5292446053184000052361463)
    ·
      refine ⟨7938669079776000078542195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292446053184000052361463 7938669079776000078542195)
      ·
        refine ⟨11908003619664000117813293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938669079776000078542195 11908003619664000117813293)
        ·
          refine ⟨4465501357374000044179985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11908003619664000117813293 4465501357374000044179985)
          ·
            refine ⟨3349126018030500033134989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465501357374000044179985 3349126018030500033134989)
            ·
              refine ⟨1255922256761437512425621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3349126018030500033134989 1255922256761437512425621)
              ·
                refine ⟨58871355785692383394951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1255922256761437512425621 58871355785692383394951)
                ·
                  rfl

theorem cell20_386949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_386949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386949 prefixEnd_386949 := by exact prefixLift 386949
  have htrace : WordTrace (prefixWord ++ tailWord_386949) baseStart_386949 baseEnd_386949 := by
    simpa [prefixWord, tailWord_386949, baseEnd_386949] using wordTrace_append hprefix tailTrace_386949
  have hstable : (prefixWord ++ tailWord_386949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386949).length < 2 ^ (prefixWord ++ tailWord_386949).sum := by decide
  have hdescent : baseEnd_386949 < baseStart_386949 := by decide
  rcases family_descends (prefixWord ++ tailWord_386949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386973 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_386973 : Nat := 118140960795 + 386973 * 2 ^ 59
def prefixEnd_386973 : Nat := 4983230072969 + 3 ^ 40 * 386973 * 2
def baseEnd_386973 : Nat := 176625021611039733384755

theorem tailTrace_386973 : CollatzResearch.WordTrace tailWord_386973 prefixEnd_386973 176625021611039733384755 := by
  unfold tailWord_386973
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114064827070385571837573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9409376551380257047891715 14114064827070385571837573)
  ·
    refine ⟨2646387155075697294719545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14114064827070385571837573 2646387155075697294719545)
    ·
      refine ⟨1984790366306772971039659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2646387155075697294719545 1984790366306772971039659)
      ·
        refine ⟨2977185549460159456559489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984790366306772971039659 2977185549460159456559489)
        ·
          refine ⟨2232889162095119592419617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2977185549460159456559489 2232889162095119592419617)
          ·
            refine ⟨1674666871571339694314713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2232889162095119592419617 1674666871571339694314713)
            ·
              refine ⟨1256000153678504770736035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674666871571339694314713 1256000153678504770736035)
              ·
                refine ⟨1884000230517757156104053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256000153678504770736035 1884000230517757156104053)
                ·
                  refine ⟨176625021611039733384755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1884000230517757156104053 176625021611039733384755)
                  ·
                    rfl

theorem cell20_386973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_386973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_386973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_386973 prefixEnd_386973 := by exact prefixLift 386973
  have htrace : WordTrace (prefixWord ++ tailWord_386973) baseStart_386973 baseEnd_386973 := by
    simpa [prefixWord, tailWord_386973, baseEnd_386973] using wordTrace_append hprefix tailTrace_386973
  have hstable : (prefixWord ++ tailWord_386973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386973).length < 2 ^ (prefixWord ++ tailWord_386973).sum := by decide
  have hdescent : baseEnd_386973 < baseStart_386973 := by decide
  rcases family_descends (prefixWord ++ tailWord_386973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387028 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_387028 : Nat := 118140960795 + 387028 * 2 ^ 59
def prefixEnd_387028 : Nat := 4983230072969 + 3 ^ 40 * 387028 * 2
def baseEnd_387028 : Nat := 176650125109703986551197

theorem tailTrace_387028 : CollatzResearch.WordTrace tailWord_387028 prefixEnd_387028 176650125109703986551197 := by
  unfold tailWord_387028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7058035420935564982544869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9410713894580753310059825 7058035420935564982544869)
  ·
    refine ⟨1323381641425418434227163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7058035420935564982544869 1323381641425418434227163)
    ·
      refine ⟨1985072462138127651340745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323381641425418434227163 1985072462138127651340745)
      ·
        refine ⟨1488804346603595738505559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1985072462138127651340745 1488804346603595738505559)
        ·
          refine ⟨2233206519905393607758339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488804346603595738505559 2233206519905393607758339)
          ·
            refine ⟨3349809779858090411637509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233206519905393607758339 3349809779858090411637509)
            ·
              refine ⟨628089333723391952182033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3349809779858090411637509 628089333723391952182033)
              ·
                refine ⟨471067000292543964136525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628089333723391952182033 471067000292543964136525)
                ·
                  refine ⟨176650125109703986551197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471067000292543964136525 176650125109703986551197)
                  ·
                    rfl

theorem cell20_387028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_387028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387028 prefixEnd_387028 := by exact prefixLift 387028
  have htrace : WordTrace (prefixWord ++ tailWord_387028) baseStart_387028 baseEnd_387028 := by
    simpa [prefixWord, tailWord_387028, baseEnd_387028] using wordTrace_append hprefix tailTrace_387028
  have hstable : (prefixWord ++ tailWord_387028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387028).length < 2 ^ (prefixWord ++ tailWord_387028).sum := by decide
  have hdescent : baseEnd_387028 < baseStart_387028 := by decide
  rcases family_descends (prefixWord ++ tailWord_387028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387115 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_387115 : Nat := 118140960795 + 387115 * 2 ^ 59
def prefixEnd_387115 : Nat := 4983230072969 + 3 ^ 40 * 387115 * 2
def baseEnd_387115 : Nat := 176689834280318350650841

theorem tailTrace_387115 : CollatzResearch.WordTrace tailWord_387115 prefixEnd_387115 176689834280318350650841 := by
  unfold tailWord_387115
  simp only [CollatzResearch.WordTrace]
  refine ⟨14119243992555943823506799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9412829328370629215671199 14119243992555943823506799)
  ·
    refine ⟨21178865988833915735260199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14119243992555943823506799 21178865988833915735260199)
    ·
      refine ⟨31768298983250873602890299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21178865988833915735260199 31768298983250873602890299)
      ·
        refine ⟨47652448474876310404335449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31768298983250873602890299 47652448474876310404335449)
        ·
          refine ⟨35739336356157232803251587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47652448474876310404335449 35739336356157232803251587)
          ·
            refine ⟨53609004534235849204877381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35739336356157232803251587 53609004534235849204877381)
            ·
              refine ⟨10051688350169221725914509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53609004534235849204877381 10051688350169221725914509)
              ·
                refine ⟨3769383131313458147217941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10051688350169221725914509 3769383131313458147217941)
                ·
                  refine ⟨176689834280318350650841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3769383131313458147217941 176689834280318350650841)
                  ·
                    rfl

theorem cell20_387115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_387115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387115 prefixEnd_387115 := by exact prefixLift 387115
  have htrace : WordTrace (prefixWord ++ tailWord_387115) baseStart_387115 baseEnd_387115 := by
    simpa [prefixWord, tailWord_387115, baseEnd_387115] using wordTrace_append hprefix tailTrace_387115
  have hstable : (prefixWord ++ tailWord_387115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387115).length < 2 ^ (prefixWord ++ tailWord_387115).sum := by decide
  have hdescent : baseEnd_387115 < baseStart_387115 := by decide
  rcases family_descends (prefixWord ++ tailWord_387115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387118 : List Nat := [4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_387118 : Nat := 118140960795 + 387118 * 2 ^ 59
def prefixEnd_387118 : Nat := 4983230072969 + 3 ^ 40 * 387118 * 2
def baseEnd_387118 : Nat := 58897067854021224516943

theorem tailTrace_387118 : CollatzResearch.WordTrace tailWord_387118 prefixEnd_387118 58897067854021224516943 := by
  unfold tailWord_387118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764919176443134416983251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9412902274363383557244005 1764919176443134416983251)
  ·
    refine ⟨2647378764664701625474877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764919176443134416983251 2647378764664701625474877)
    ·
      refine ⟨992767036749263109553079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2647378764664701625474877 992767036749263109553079)
      ·
        refine ⟨1489150555123894664329619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992767036749263109553079 1489150555123894664329619)
        ·
          refine ⟨2233725832685841996494429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489150555123894664329619 2233725832685841996494429)
          ·
            refine ⟨837647187257190748685411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2233725832685841996494429 837647187257190748685411)
            ·
              refine ⟨1256470780885786123028117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837647187257190748685411 1256470780885786123028117)
              ·
                refine ⟨58897067854021224516943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1256470780885786123028117 58897067854021224516943)
                ·
                  rfl

theorem cell20_387118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_387118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387118 prefixEnd_387118 := by exact prefixLift 387118
  have htrace : WordTrace (prefixWord ++ tailWord_387118) baseStart_387118 baseEnd_387118 := by
    simpa [prefixWord, tailWord_387118, baseEnd_387118] using wordTrace_append hprefix tailTrace_387118
  have hstable : (prefixWord ++ tailWord_387118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387118).length < 2 ^ (prefixWord ++ tailWord_387118).sum := by decide
  have hdescent : baseEnd_387118 < baseStart_387118 := by decide
  rcases family_descends (prefixWord ++ tailWord_387118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387124 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 2]
def baseStart_387124 : Nat := 118140960795 + 387124 * 2 ^ 59
def prefixEnd_387124 : Nat := 4983230072969 + 3 ^ 40 * 387124 * 2
def baseEnd_387124 : Nat := 176693942125554319350805

theorem tailTrace_387124 : CollatzResearch.WordTrace tailWord_387124 prefixEnd_387124 176693942125554319350805 := by
  unfold tailWord_387124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059786124761669180292213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9413048166348892240389617 7059786124761669180292213)
  ·
    refine ⟨661854949196406485652395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7059786124761669180292213 661854949196406485652395)
    ·
      refine ⟨992782423794609728478593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661854949196406485652395 992782423794609728478593)
      ·
        refine ⟨744586817845957296358945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992782423794609728478593 744586817845957296358945)
        ·
          refine ⟨558440113384467972269209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744586817845957296358945 558440113384467972269209)
          ·
            refine ⟨418830085038350979201907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558440113384467972269209 418830085038350979201907)
            ·
              refine ⟨628245127557526468802861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418830085038350979201907 628245127557526468802861)
              ·
                refine ⟨235591922834072425801073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 628245127557526468802861 235591922834072425801073)
                ·
                  refine ⟨176693942125554319350805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235591922834072425801073 176693942125554319350805)
                  ·
                    rfl

theorem cell20_387124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_387124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387124 prefixEnd_387124 := by exact prefixLift 387124
  have htrace : WordTrace (prefixWord ++ tailWord_387124) baseStart_387124 baseEnd_387124 := by
    simpa [prefixWord, tailWord_387124, baseEnd_387124] using wordTrace_append hprefix tailTrace_387124
  have hstable : (prefixWord ++ tailWord_387124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387124).length < 2 ^ (prefixWord ++ tailWord_387124).sum := by decide
  have hdescent : baseEnd_387124 < baseStart_387124 := by decide
  rcases family_descends (prefixWord ++ tailWord_387124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387142 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_387142 : Nat := 118140960795 + 387142 * 2 ^ 59
def prefixEnd_387142 : Nat := 4983230072969 + 3 ^ 40 * 387142 * 2
def baseEnd_387142 : Nat := 176702157816026256750731

theorem tailTrace_387142 : CollatzResearch.WordTrace tailWord_387142 prefixEnd_387142 176702157816026256750731 := by
  unfold tailWord_387142
  simp only [CollatzResearch.WordTrace]
  refine ⟨441257148858066482335615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9413485842305418289826453 441257148858066482335615)
  ·
    refine ⟨661885723287099723503423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441257148858066482335615 661885723287099723503423)
    ·
      refine ⟨992828584930649585255135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661885723287099723503423 992828584930649585255135)
      ·
        refine ⟨1489242877395974377882703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992828584930649585255135 1489242877395974377882703)
        ·
          refine ⟨2233864316093961566824055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489242877395974377882703 2233864316093961566824055)
          ·
            refine ⟨3350796474140942350236083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233864316093961566824055 3350796474140942350236083)
            ·
              refine ⟨5026194711211413525354125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350796474140942350236083 5026194711211413525354125)
              ·
                refine ⟨1884823016704280072007797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5026194711211413525354125 1884823016704280072007797)
                ·
                  refine ⟨176702157816026256750731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1884823016704280072007797 176702157816026256750731)
                  ·
                    rfl

theorem cell20_387142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_387142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387142 prefixEnd_387142 := by exact prefixLift 387142
  have htrace : WordTrace (prefixWord ++ tailWord_387142) baseStart_387142 baseEnd_387142 := by
    simpa [prefixWord, tailWord_387142, baseEnd_387142] using wordTrace_append hprefix tailTrace_387142
  have hstable : (prefixWord ++ tailWord_387142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387142).length < 2 ^ (prefixWord ++ tailWord_387142).sum := by decide
  have hdescent : baseEnd_387142 < baseStart_387142 := by decide
  rcases family_descends (prefixWord ++ tailWord_387142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387232 : List Nat := [2, 1, 1, 4, 2, 3, 3, 4]
def baseStart_387232 : Nat := 118140960795 + 387232 * 2 ^ 59
def prefixEnd_387232 : Nat := 4983230072969 + 3 ^ 40 * 387232 * 2
def baseEnd_387232 : Nat := 58914412089461981250121

theorem tailTrace_387232 : CollatzResearch.WordTrace tailWord_387232 prefixEnd_387232 58914412089461981250121 := by
  unfold tailWord_387232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061755666566036402757975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9415674222088048537010633 7061755666566036402757975)
  ·
    refine ⟨10592633499849054604136963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7061755666566036402757975 10592633499849054604136963)
    ·
      refine ⟨15888950249773581906205445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10592633499849054604136963 15888950249773581906205445)
      ·
        refine ⟨2979178171832546607413521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15888950249773581906205445 2979178171832546607413521)
        ·
          refine ⟨2234383628874409955560141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2979178171832546607413521 2234383628874409955560141)
          ·
            refine ⟨837893860827903733335053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2234383628874409955560141 837893860827903733335053)
            ·
              refine ⟨314210197810463900000645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 837893860827903733335053 314210197810463900000645)
              ·
                refine ⟨58914412089461981250121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314210197810463900000645 58914412089461981250121)
                ·
                  rfl

theorem cell20_387232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_387232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387232 prefixEnd_387232 := by exact prefixLift 387232
  have htrace : WordTrace (prefixWord ++ tailWord_387232) baseStart_387232 baseEnd_387232 := by
    simpa [prefixWord, tailWord_387232, baseEnd_387232] using wordTrace_append hprefix tailTrace_387232
  have hstable : (prefixWord ++ tailWord_387232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387232).length < 2 ^ (prefixWord ++ tailWord_387232).sum := by decide
  have hdescent : baseEnd_387232 < baseStart_387232 := by decide
  rcases family_descends (prefixWord ++ tailWord_387232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387252 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 5]
def baseStart_387252 : Nat := 118140960795 + 387252 * 2 ^ 59
def prefixEnd_387252 : Nat := 4983230072969 + 3 ^ 40 * 387252 * 2
def baseEnd_387252 : Nat := 176752364813354763083615

theorem tailTrace_387252 : CollatzResearch.WordTrace tailWord_387252 prefixEnd_387252 176752364813354763083615 := by
  unfold tailWord_387252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062120396529808110622005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9416160528706410814162673 7062120396529808110622005)
  ·
    refine ⟨662073787174669510370813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7062120396529808110622005 662073787174669510370813)
    ·
      refine ⟨248277670190501066389055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 662073787174669510370813 248277670190501066389055)
      ·
        refine ⟨372416505285751599583583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248277670190501066389055 372416505285751599583583)
        ·
          refine ⟨558624757928627399375375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372416505285751599583583 558624757928627399375375)
          ·
            refine ⟨837937136892941099063063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558624757928627399375375 837937136892941099063063)
            ·
              refine ⟨1256905705339411648594595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837937136892941099063063 1256905705339411648594595)
              ·
                refine ⟨1885358558009117472891893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256905705339411648594595 1885358558009117472891893)
                ·
                  refine ⟨176752364813354763083615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1885358558009117472891893 176752364813354763083615)
                  ·
                    rfl

theorem cell20_387252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_387252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387252 prefixEnd_387252 := by exact prefixLift 387252
  have htrace : WordTrace (prefixWord ++ tailWord_387252) baseStart_387252 baseEnd_387252 := by
    simpa [prefixWord, tailWord_387252, baseEnd_387252] using wordTrace_append hprefix tailTrace_387252
  have hstable : (prefixWord ++ tailWord_387252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387252).length < 2 ^ (prefixWord ++ tailWord_387252).sum := by decide
  have hdescent : baseEnd_387252 < baseStart_387252 := by decide
  rcases family_descends (prefixWord ++ tailWord_387252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387322 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_387322 : Nat := 118140960795 + 387322 * 2 ^ 59
def prefixEnd_387322 : Nat := 4983230072969 + 3 ^ 40 * 387322 * 2
def baseEnd_387322 : Nat := 176784314720745630749995

theorem tailTrace_387322 : CollatzResearch.WordTrace tailWord_387322 prefixEnd_387322 176784314720745630749995 := by
  unfold tailWord_387322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531698475701504544073055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9417862601870678784194813 3531698475701504544073055)
  ·
    refine ⟨5297547713552256816109583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531698475701504544073055 5297547713552256816109583)
    ·
      refine ⟨7946321570328385224164375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5297547713552256816109583 7946321570328385224164375)
      ·
        refine ⟨11919482355492577836246563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7946321570328385224164375 11919482355492577836246563)
        ·
          refine ⟨17879223533238866754369845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11919482355492577836246563 17879223533238866754369845)
          ·
            refine ⟨1676177206241143758222173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17879223533238866754369845 1676177206241143758222173)
            ·
              refine ⟨628566452340428909333315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676177206241143758222173 628566452340428909333315)
              ·
                refine ⟨942849678510643363999973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628566452340428909333315 942849678510643363999973)
                ·
                  refine ⟨176784314720745630749995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942849678510643363999973 176784314720745630749995)
                  ·
                    rfl

theorem cell20_387322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_387322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387322 prefixEnd_387322 := by exact prefixLift 387322
  have htrace : WordTrace (prefixWord ++ tailWord_387322) baseStart_387322 baseEnd_387322 := by
    simpa [prefixWord, tailWord_387322, baseEnd_387322] using wordTrace_append hprefix tailTrace_387322
  have hstable : (prefixWord ++ tailWord_387322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387322).length < 2 ^ (prefixWord ++ tailWord_387322).sum := by decide
  have hdescent : baseEnd_387322 < baseStart_387322 := by decide
  rcases family_descends (prefixWord ++ tailWord_387322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387329 : List Nat := [1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_387329 : Nat := 118140960795 + 387329 * 2 ^ 59
def prefixEnd_387329 : Nat := 4983230072969 + 3 ^ 40 * 387329 * 2
def baseEnd_387329 : Nat := 58929169903828239172211

theorem tailTrace_387329 : CollatzResearch.WordTrace tailWord_387329 prefixEnd_387329 58929169903828239172211 := by
  unfold tailWord_387329
  simp only [CollatzResearch.WordTrace]
  refine ⟨14127049213780658371797041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9418032809187105581198027 14127049213780658371797041)
  ·
    refine ⟨10595286910335493778847781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14127049213780658371797041 10595286910335493778847781)
    ·
      refine ⟨1986616295687905083533959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10595286910335493778847781 1986616295687905083533959)
      ·
        refine ⟨2979924443531857625300939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986616295687905083533959 2979924443531857625300939)
        ·
          refine ⟨4469886665297786437951409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979924443531857625300939 4469886665297786437951409)
          ·
            refine ⟨3352414998973339828463557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469886665297786437951409 3352414998973339828463557)
            ·
              refine ⟨628577812307501217836917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3352414998973339828463557 628577812307501217836917)
              ·
                refine ⟨58929169903828239172211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 628577812307501217836917 58929169903828239172211)
                ·
                  rfl

theorem cell20_387329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_387329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387329 prefixEnd_387329 := by exact prefixLift 387329
  have htrace : WordTrace (prefixWord ++ tailWord_387329) baseStart_387329 baseEnd_387329 := by
    simpa [prefixWord, tailWord_387329, baseEnd_387329] using wordTrace_append hprefix tailTrace_387329
  have hstable : (prefixWord ++ tailWord_387329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387329).length < 2 ^ (prefixWord ++ tailWord_387329).sum := by decide
  have hdescent : baseEnd_387329 < baseStart_387329 := by decide
  rcases family_descends (prefixWord ++ tailWord_387329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387332 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_387332 : Nat := 118140960795 + 387332 * 2 ^ 59
def prefixEnd_387332 : Nat := 4983230072969 + 3 ^ 40 * 387332 * 2
def baseEnd_387332 : Nat := 176788878993230040416621

theorem tailTrace_387332 : CollatzResearch.WordTrace tailWord_387332 prefixEnd_387332 176788878993230040416621 := by
  unfold tailWord_387332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7063579316384894942078125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9418105755179859922770833 7063579316384894942078125)
  ·
    refine ⟨2648842243644335603279297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7063579316384894942078125 2648842243644335603279297)
    ·
      refine ⟨1986631682733251702459473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2648842243644335603279297 1986631682733251702459473)
      ·
        refine ⟨1489973762049938776844605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986631682733251702459473 1489973762049938776844605)
        ·
          refine ⟨558740160768727041316727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1489973762049938776844605 558740160768727041316727)
          ·
            refine ⟨838110241153090561975091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558740160768727041316727 838110241153090561975091)
            ·
              refine ⟨1257165361729635842962637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838110241153090561975091 1257165361729635842962637)
              ·
                refine ⟨471437010648613441110989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257165361729635842962637 471437010648613441110989)
                ·
                  refine ⟨176788878993230040416621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471437010648613441110989 176788878993230040416621)
                  ·
                    rfl

theorem cell20_387332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_387332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387332 prefixEnd_387332 := by exact prefixLift 387332
  have htrace : WordTrace (prefixWord ++ tailWord_387332) baseStart_387332 baseEnd_387332 := by
    simpa [prefixWord, tailWord_387332, baseEnd_387332] using wordTrace_append hprefix tailTrace_387332
  have hstable : (prefixWord ++ tailWord_387332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387332).length < 2 ^ (prefixWord ++ tailWord_387332).sum := by decide
  have hdescent : baseEnd_387332 < baseStart_387332 := by decide
  rcases family_descends (prefixWord ++ tailWord_387332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387343 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_387343 : Nat := 118140960795 + 387343 * 2 ^ 59
def prefixEnd_387343 : Nat := 4983230072969 + 3 ^ 40 * 387343 * 2
def baseEnd_387343 : Nat := 176793899692962891049909

theorem tailTrace_387343 : CollatzResearch.WordTrace tailWord_387343 prefixEnd_387343 176793899692962891049909 := by
  unfold tailWord_387343
  simp only [CollatzResearch.WordTrace]
  refine ⟨14127559835729938762806683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9418373223819959175204455 14127559835729938762806683)
  ·
    refine ⟨21191339753594908144210025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14127559835729938762806683 21191339753594908144210025)
    ·
      refine ⟨15893504815196181108157519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21191339753594908144210025 15893504815196181108157519)
      ·
        refine ⟨23840257222794271662236279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15893504815196181108157519 23840257222794271662236279)
        ·
          refine ⟨35760385834191407493354419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23840257222794271662236279 35760385834191407493354419)
          ·
            refine ⟨53640578751287111240031629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35760385834191407493354419 53640578751287111240031629)
            ·
              refine ⟨20115217031732666715011861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53640578751287111240031629 20115217031732666715011861)
              ·
                refine ⟨942900798362468752266181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20115217031732666715011861 942900798362468752266181)
                ·
                  refine ⟨176793899692962891049909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942900798362468752266181 176793899692962891049909)
                  ·
                    rfl

theorem cell20_387343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_387343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387343 prefixEnd_387343 := by exact prefixLift 387343
  have htrace : WordTrace (prefixWord ++ tailWord_387343) baseStart_387343 baseEnd_387343 := by
    simpa [prefixWord, tailWord_387343, baseEnd_387343] using wordTrace_append hprefix tailTrace_387343
  have hstable : (prefixWord ++ tailWord_387343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387343).length < 2 ^ (prefixWord ++ tailWord_387343).sum := by decide
  have hdescent : baseEnd_387343 < baseStart_387343 := by decide
  rcases family_descends (prefixWord ++ tailWord_387343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387373 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 2]
def baseStart_387373 : Nat := 118140960795 + 387373 * 2 ^ 59
def prefixEnd_387373 : Nat := 4983230072969 + 3 ^ 40 * 387373 * 2
def baseEnd_387373 : Nat := 176807592510416120049787

theorem tailTrace_387373 : CollatzResearch.WordTrace tailWord_387373 prefixEnd_387373 176807592510416120049787 := by
  unfold tailWord_387373
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128654025621253886398773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9419102683747502590932515 14128654025621253886398773)
  ·
    refine ⟨1324561314901992551849885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14128654025621253886398773 1324561314901992551849885)
    ·
      refine ⟨496710493088247206943707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1324561314901992551849885 496710493088247206943707)
      ·
        refine ⟨745065739632370810415561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496710493088247206943707 745065739632370810415561)
        ·
          refine ⟨558799304724278107811671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745065739632370810415561 558799304724278107811671)
          ·
            refine ⟨838198957086417161717507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558799304724278107811671 838198957086417161717507)
            ·
              refine ⟨1257298435629625742576261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838198957086417161717507 1257298435629625742576261)
              ·
                refine ⟨235743456680554826733049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1257298435629625742576261 235743456680554826733049)
                ·
                  refine ⟨176807592510416120049787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235743456680554826733049 176807592510416120049787)
                  ·
                    rfl

theorem cell20_387373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_387373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387373 prefixEnd_387373 := by exact prefixLift 387373
  have htrace : WordTrace (prefixWord ++ tailWord_387373) baseStart_387373 baseEnd_387373 := by
    simpa [prefixWord, tailWord_387373, baseEnd_387373] using wordTrace_append hprefix tailTrace_387373
  have hstable : (prefixWord ++ tailWord_387373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387373).length < 2 ^ (prefixWord ++ tailWord_387373).sum := by decide
  have hdescent : baseEnd_387373 < baseStart_387373 := by decide
  rcases family_descends (prefixWord ++ tailWord_387373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387415 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 2]
def baseStart_387415 : Nat := 118140960795 + 387415 * 2 ^ 59
def prefixEnd_387415 : Nat := 4983230072969 + 3 ^ 40 * 387415 * 2
def baseEnd_387415 : Nat := 176826762454850640649615

theorem tailTrace_387415 : CollatzResearch.WordTrace tailWord_387415 prefixEnd_387415 176826762454850640649615 := by
  unfold tailWord_387415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130185891469095059427699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9420123927646063372951799 14130185891469095059427699)
  ·
    refine ⟨21195278837203642589141549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14130185891469095059427699 21195278837203642589141549)
    ·
      refine ⟨7948229563951365970928081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21195278837203642589141549 7948229563951365970928081)
      ·
        refine ⟨5961172172963524478196061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7948229563951365970928081 5961172172963524478196061)
        ·
          refine ⟨2235439564861321679323523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5961172172963524478196061 2235439564861321679323523)
          ·
            refine ⟨3353159347291982518985285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235439564861321679323523 3353159347291982518985285)
            ·
              refine ⟨628717377617246722309741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3353159347291982518985285 628717377617246722309741)
              ·
                refine ⟨235769016606467520866153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 628717377617246722309741 235769016606467520866153)
                ·
                  refine ⟨176826762454850640649615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235769016606467520866153 176826762454850640649615)
                  ·
                    rfl

theorem cell20_387415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 2].length) (baseStart_387415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387415 prefixEnd_387415 := by exact prefixLift 387415
  have htrace : WordTrace (prefixWord ++ tailWord_387415) baseStart_387415 baseEnd_387415 := by
    simpa [prefixWord, tailWord_387415, baseEnd_387415] using wordTrace_append hprefix tailTrace_387415
  have hstable : (prefixWord ++ tailWord_387415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387415).length < 2 ^ (prefixWord ++ tailWord_387415).sum := by decide
  have hdescent : baseEnd_387415 < baseStart_387415 := by decide
  rcases family_descends (prefixWord ++ tailWord_387415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387429 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_387429 : Nat := 118140960795 + 387429 * 2 ^ 59
def prefixEnd_387429 : Nat := 4983230072969 + 3 ^ 40 * 387429 * 2
def baseEnd_387429 : Nat := 176833152436328814182891

theorem tailTrace_387429 : CollatzResearch.WordTrace tailWord_387429 prefixEnd_387429 176833152436328814182891 := by
  unfold tailWord_387429
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130696513418375450437341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9420464342278916966958227 14130696513418375450437341)
  ·
    refine ⟨5299011192531890793914003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14130696513418375450437341 5299011192531890793914003)
    ·
      refine ⟨7948516788797836190871005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5299011192531890793914003 7948516788797836190871005)
      ·
        refine ⟨2980693795799188571576627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7948516788797836190871005 2980693795799188571576627)
        ·
          refine ⟨4471040693698782857364941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980693795799188571576627 4471040693698782857364941)
          ·
            refine ⟨1676640260137043571511853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4471040693698782857364941 1676640260137043571511853)
            ·
              refine ⟨628740097551391339316945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676640260137043571511853 628740097551391339316945)
              ·
                refine ⟨471555073163543504487709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628740097551391339316945 471555073163543504487709)
                ·
                  refine ⟨176833152436328814182891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471555073163543504487709 176833152436328814182891)
                  ·
                    rfl

theorem cell20_387429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_387429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387429 prefixEnd_387429 := by exact prefixLift 387429
  have htrace : WordTrace (prefixWord ++ tailWord_387429) baseStart_387429 baseEnd_387429 := by
    simpa [prefixWord, tailWord_387429, baseEnd_387429] using wordTrace_append hprefix tailTrace_387429
  have hstable : (prefixWord ++ tailWord_387429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387429).length < 2 ^ (prefixWord ++ tailWord_387429).sum := by decide
  have hdescent : baseEnd_387429 < baseStart_387429 := by decide
  rcases family_descends (prefixWord ++ tailWord_387429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387466 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_387466 : Nat := 118140960795 + 387466 * 2 ^ 59
def prefixEnd_387466 : Nat := 4983230072969 + 3 ^ 40 * 387466 * 2
def baseEnd_387466 : Nat := 176850040244521129949407

theorem tailTrace_387466 : CollatzResearch.WordTrace tailWord_387466 prefixEnd_387466 176850040244521129949407 := by
  unfold tailWord_387466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533011503571082692383563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9421364009522887179689501 3533011503571082692383563)
  ·
    refine ⟨5299517255356624038575345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533011503571082692383563 5299517255356624038575345)
    ·
      refine ⟨3974637941517468028931509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5299517255356624038575345 3974637941517468028931509)
      ·
        refine ⟨372622307017262627712329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3974637941517468028931509 372622307017262627712329)
        ·
          refine ⟨279466730262946970784247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372622307017262627712329 279466730262946970784247)
          ·
            refine ⟨419200095394420456176371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279466730262946970784247 419200095394420456176371)
            ·
              refine ⟨628800143091630684264557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419200095394420456176371 628800143091630684264557)
              ·
                refine ⟨235800053659361506599209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 628800143091630684264557 235800053659361506599209)
                ·
                  refine ⟨176850040244521129949407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235800053659361506599209 176850040244521129949407)
                  ·
                    rfl

theorem cell20_387466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_387466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387466 prefixEnd_387466 := by exact prefixLift 387466
  have htrace : WordTrace (prefixWord ++ tailWord_387466) baseStart_387466 baseEnd_387466 := by
    simpa [prefixWord, tailWord_387466, baseEnd_387466] using wordTrace_append hprefix tailTrace_387466
  have hstable : (prefixWord ++ tailWord_387466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387466).length < 2 ^ (prefixWord ++ tailWord_387466).sum := by decide
  have hdescent : baseEnd_387466 < baseStart_387466 := by decide
  rcases family_descends (prefixWord ++ tailWord_387466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387470 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_387470 : Nat := 118140960795 + 387470 * 2 ^ 59
def prefixEnd_387470 : Nat := 4983230072969 + 3 ^ 40 * 387470 * 2
def baseEnd_387470 : Nat := 176851865953514893816057

theorem tailTrace_387470 : CollatzResearch.WordTrace tailWord_387470 prefixEnd_387470 176851865953514893816057 := by
  unfold tailWord_387470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1766523988283729931584983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9421461270846559635119909 1766523988283729931584983)
  ·
    refine ⟨2649785982425594897377475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1766523988283729931584983 2649785982425594897377475)
    ·
      refine ⟨3974678973638392346066213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2649785982425594897377475 3974678973638392346066213)
      ·
        refine ⟨745252307557198564887415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3974678973638392346066213 745252307557198564887415)
        ·
          refine ⟨1117878461335797847331123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745252307557198564887415 1117878461335797847331123)
          ·
            refine ⟨1676817692003696770996685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117878461335797847331123 1676817692003696770996685)
            ·
              refine ⟨628806634501386289123757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676817692003696770996685 628806634501386289123757)
              ·
                refine ⟨235802487938019858421409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 628806634501386289123757 235802487938019858421409)
                ·
                  refine ⟨176851865953514893816057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235802487938019858421409 176851865953514893816057)
                  ·
                    rfl

theorem cell20_387470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_387470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387470 prefixEnd_387470 := by exact prefixLift 387470
  have htrace : WordTrace (prefixWord ++ tailWord_387470) baseStart_387470 baseEnd_387470 := by
    simpa [prefixWord, tailWord_387470, baseEnd_387470] using wordTrace_append hprefix tailTrace_387470
  have hstable : (prefixWord ++ tailWord_387470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387470).length < 2 ^ (prefixWord ++ tailWord_387470).sum := by decide
  have hdescent : baseEnd_387470 < baseStart_387470 := by decide
  rcases family_descends (prefixWord ++ tailWord_387470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387488 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_387488 : Nat := 118140960795 + 387488 * 2 ^ 59
def prefixEnd_387488 : Nat := 4983230072969 + 3 ^ 40 * 387488 * 2
def baseEnd_387488 : Nat := 176860081643986831215983

theorem tailTrace_387488 : CollatzResearch.WordTrace tailWord_387488 prefixEnd_387488 176860081643986831215983 := by
  unfold tailWord_387488
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066424210102314263417559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9421898946803085684556745 7066424210102314263417559)
  ·
    refine ⟨10599636315153471395126339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7066424210102314263417559 10599636315153471395126339)
    ·
      refine ⟨15899454472730207092689509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599636315153471395126339 15899454472730207092689509)
      ·
        refine ⟨2981147713636913829879283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15899454472730207092689509 2981147713636913829879283)
        ·
          refine ⟨4471721570455370744818925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981147713636913829879283 4471721570455370744818925)
          ·
            refine ⟨1676895588920764029307097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4471721570455370744818925 1676895588920764029307097)
            ·
              refine ⟨1257671691690573021980323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676895588920764029307097 1257671691690573021980323)
              ·
                refine ⟨1886507537535859532970485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257671691690573021980323 1886507537535859532970485)
                ·
                  refine ⟨176860081643986831215983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1886507537535859532970485 176860081643986831215983)
                  ·
                    rfl

theorem cell20_387488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_387488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387488 prefixEnd_387488 := by exact prefixLift 387488
  have htrace : WordTrace (prefixWord ++ tailWord_387488) baseStart_387488 baseEnd_387488 := by
    simpa [prefixWord, tailWord_387488, baseEnd_387488] using wordTrace_append hprefix tailTrace_387488
  have hstable : (prefixWord ++ tailWord_387488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387488).length < 2 ^ (prefixWord ++ tailWord_387488).sum := by decide
  have hdescent : baseEnd_387488 < baseStart_387488 := by decide
  rcases family_descends (prefixWord ++ tailWord_387488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387505 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_387505 : Nat := 118140960795 + 387505 * 2 ^ 59
def prefixEnd_387505 : Nat := 4983230072969 + 3 ^ 40 * 387505 * 2
def baseEnd_387505 : Nat := 176867840907210327649247

theorem tailTrace_387505 : CollatzResearch.WordTrace tailWord_387505 prefixEnd_387505 176867840907210327649247 := by
  unfold tailWord_387505
  simp only [CollatzResearch.WordTrace]
  refine ⟨14133468461143040430203969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9422312307428693620135979 14133468461143040430203969)
  ·
    refine ⟨10600101345857280322652977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14133468461143040430203969 10600101345857280322652977)
    ·
      refine ⟨7950076009392960241989733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10600101345857280322652977 7950076009392960241989733)
      ·
        refine ⟨1490639251761180045373075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7950076009392960241989733 1490639251761180045373075)
        ·
          refine ⟨2235958877641770068059613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490639251761180045373075 2235958877641770068059613)
          ·
            refine ⟨838484579115663775522355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2235958877641770068059613 838484579115663775522355)
            ·
              refine ⟨1257726868673495663283533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838484579115663775522355 1257726868673495663283533)
              ·
                refine ⟨471647575752560873731325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257726868673495663283533 471647575752560873731325)
                ·
                  refine ⟨176867840907210327649247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471647575752560873731325 176867840907210327649247)
                  ·
                    rfl

theorem cell20_387505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_387505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387505 prefixEnd_387505 := by exact prefixLift 387505
  have htrace : WordTrace (prefixWord ++ tailWord_387505) baseStart_387505 baseEnd_387505 := by
    simpa [prefixWord, tailWord_387505, baseEnd_387505] using wordTrace_append hprefix tailTrace_387505
  have hstable : (prefixWord ++ tailWord_387505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387505).length < 2 ^ (prefixWord ++ tailWord_387505).sum := by decide
  have hdescent : baseEnd_387505 < baseStart_387505 := by decide
  rcases family_descends (prefixWord ++ tailWord_387505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387564 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_387564 : Nat := 118140960795 + 387564 * 2 ^ 59
def prefixEnd_387564 : Nat := 4983230072969 + 3 ^ 40 * 387564 * 2
def baseEnd_387564 : Nat := 176894770114868344682339

theorem tailTrace_387564 : CollatzResearch.WordTrace tailWord_387564 prefixEnd_387564 176894770114868344682339 := by
  unfold tailWord_387564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067810183964646753300873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9423746911952862337734497 7067810183964646753300873)
  ·
    refine ⟨5300857637973485064975655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7067810183964646753300873 5300857637973485064975655)
    ·
      refine ⟨7951286456960227597463483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300857637973485064975655 7951286456960227597463483)
      ·
        refine ⟨11926929685440341396195225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951286456960227597463483 11926929685440341396195225)
        ·
          refine ⟨8945197264080256047146419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11926929685440341396195225 8945197264080256047146419)
          ·
            refine ⟨13417795896120384070719629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8945197264080256047146419 13417795896120384070719629)
            ·
              refine ⟨5031673461045144026519861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13417795896120384070719629 5031673461045144026519861)
              ·
                refine ⟨471719386972982252486237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5031673461045144026519861 471719386972982252486237)
                ·
                  refine ⟨176894770114868344682339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471719386972982252486237 176894770114868344682339)
                  ·
                    rfl

theorem cell20_387564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_387564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387564 prefixEnd_387564 := by exact prefixLift 387564
  have htrace : WordTrace (prefixWord ++ tailWord_387564) baseStart_387564 baseEnd_387564 := by
    simpa [prefixWord, tailWord_387564, baseEnd_387564] using wordTrace_append hprefix tailTrace_387564
  have hstable : (prefixWord ++ tailWord_387564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387564).length < 2 ^ (prefixWord ++ tailWord_387564).sum := by decide
  have hdescent : baseEnd_387564 < baseStart_387564 := by decide
  rcases family_descends (prefixWord ++ tailWord_387564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387571 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_387571 : Nat := 118140960795 + 387571 * 2 ^ 59
def prefixEnd_387571 : Nat := 4983230072969 + 3 ^ 40 * 387571 * 2
def baseEnd_387571 : Nat := 176897965105607431448977

theorem tailTrace_387571 : CollatzResearch.WordTrace tailWord_387571 prefixEnd_387571 176897965105607431448977 := by
  unfold tailWord_387571
  simp only [CollatzResearch.WordTrace]
  refine ⟨14135875678903933702106567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9423917119269289134737711 14135875678903933702106567)
  ·
    refine ⟨21203813518355900553159851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14135875678903933702106567 21203813518355900553159851)
    ·
      refine ⟨31805720277533850829739777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21203813518355900553159851 31805720277533850829739777)
      ·
        refine ⟨23854290208150388122304833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31805720277533850829739777 23854290208150388122304833)
        ·
          refine ⟨17890717656112791091728625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23854290208150388122304833 17890717656112791091728625)
          ·
            refine ⟨13418038242084593318796469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17890717656112791091728625 13418038242084593318796469)
            ·
              refine ⟨1257941085195430623637169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13418038242084593318796469 1257941085195430623637169)
              ·
                refine ⟨943455813896572967727877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257941085195430623637169 943455813896572967727877)
                ·
                  refine ⟨176897965105607431448977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943455813896572967727877 176897965105607431448977)
                  ·
                    rfl

theorem cell20_387571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_387571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387571 prefixEnd_387571 := by exact prefixLift 387571
  have htrace : WordTrace (prefixWord ++ tailWord_387571) baseStart_387571 baseEnd_387571 := by
    simpa [prefixWord, tailWord_387571, baseEnd_387571] using wordTrace_append hprefix tailTrace_387571
  have hstable : (prefixWord ++ tailWord_387571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387571).length < 2 ^ (prefixWord ++ tailWord_387571).sum := by decide
  have hdescent : baseEnd_387571 < baseStart_387571 := by decide
  rcases family_descends (prefixWord ++ tailWord_387571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387574 : List Nat := [5, 1, 1, 1, 2, 1, 5, 4]
def baseStart_387574 : Nat := 118140960795 + 387574 * 2 ^ 59
def prefixEnd_387574 : Nat := 4983230072969 + 3 ^ 40 * 387574 * 2
def baseEnd_387574 : Nat := 58966444795784251449655

theorem tailTrace_387574 : CollatzResearch.WordTrace tailWord_387574 prefixEnd_387574 58966444795784251449655 := by
  unfold tailWord_387574
  simp only [CollatzResearch.WordTrace]
  refine ⟨883499068618316575904111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9423990065262043476310517 883499068618316575904111)
  ·
    refine ⟨1325248602927474863856167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 883499068618316575904111 1325248602927474863856167)
    ·
      refine ⟨1987872904391212295784251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325248602927474863856167 1987872904391212295784251)
      ·
        refine ⟨2981809356586818443676377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987872904391212295784251 2981809356586818443676377)
        ·
          refine ⟨2236357017440113832757283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981809356586818443676377 2236357017440113832757283)
          ·
            refine ⟨3354535526160170749135925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236357017440113832757283 3354535526160170749135925)
            ·
              refine ⟨314487705577516007731493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3354535526160170749135925 314487705577516007731493)
              ·
                refine ⟨58966444795784251449655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314487705577516007731493 58966444795784251449655)
                ·
                  rfl

theorem cell20_387574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_387574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387574 prefixEnd_387574 := by exact prefixLift 387574
  have htrace : WordTrace (prefixWord ++ tailWord_387574) baseStart_387574 baseEnd_387574 := by
    simpa [prefixWord, tailWord_387574, baseEnd_387574] using wordTrace_append hprefix tailTrace_387574
  have hstable : (prefixWord ++ tailWord_387574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387574).length < 2 ^ (prefixWord ++ tailWord_387574).sum := by decide
  have hdescent : baseEnd_387574 < baseStart_387574 := by decide
  rcases family_descends (prefixWord ++ tailWord_387574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387598 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_387598 : Nat := 118140960795 + 387598 * 2 ^ 59
def prefixEnd_387598 : Nat := 4983230072969 + 3 ^ 40 * 387598 * 2
def baseEnd_387598 : Nat := 176910288641315337548867

theorem tailTrace_387598 : CollatzResearch.WordTrace tailWord_387598 prefixEnd_387598 176910288641315337548867 := by
  unfold tailWord_387598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767107556225764664167431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9424573633204078208892965 1767107556225764664167431)
  ·
    refine ⟨2650661334338646996251147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1767107556225764664167431 2650661334338646996251147)
    ·
      refine ⟨3975992001507970494376721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2650661334338646996251147 3975992001507970494376721)
      ·
        refine ⟨2981994001130977870782541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3975992001507970494376721 2981994001130977870782541)
        ·
          refine ⟨1118247750424116701543453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2981994001130977870782541 1118247750424116701543453)
          ·
            refine ⟨419342906409043763078795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1118247750424116701543453 419342906409043763078795)
            ·
              refine ⟨629014359613565644618193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419342906409043763078795 629014359613565644618193)
              ·
                refine ⟨471760769710174233463645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629014359613565644618193 471760769710174233463645)
                ·
                  refine ⟨176910288641315337548867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471760769710174233463645 176910288641315337548867)
                  ·
                    rfl

theorem cell20_387598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_387598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387598 prefixEnd_387598 := by exact prefixLift 387598
  have htrace : WordTrace (prefixWord ++ tailWord_387598) baseStart_387598 baseEnd_387598 := by
    simpa [prefixWord, tailWord_387598, baseEnd_387598] using wordTrace_append hprefix tailTrace_387598
  have hstable : (prefixWord ++ tailWord_387598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387598).length < 2 ^ (prefixWord ++ tailWord_387598).sum := by decide
  have hdescent : baseEnd_387598 < baseStart_387598 := by decide
  rcases family_descends (prefixWord ++ tailWord_387598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387626 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_387626 : Nat := 118140960795 + 387626 * 2 ^ 59
def prefixEnd_387626 : Nat := 4983230072969 + 3 ^ 40 * 387626 * 2
def baseEnd_387626 : Nat := 176923068604271684615419

theorem tailTrace_387626 : CollatzResearch.WordTrace tailWord_387626 prefixEnd_387626 176923068604271684615419 := by
  unfold tailWord_387626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534470423426169523839683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9425254462469785396905821 3534470423426169523839683)
  ·
    refine ⟨5301705635139254285759525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3534470423426169523839683 5301705635139254285759525)
    ·
      refine ⟨994069806588610178579911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5301705635139254285759525 994069806588610178579911)
      ·
        refine ⟨1491104709882915267869867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994069806588610178579911 1491104709882915267869867)
        ·
          refine ⟨2236657064824372901804801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491104709882915267869867 2236657064824372901804801)
          ·
            refine ⟨1677492798618279676353601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236657064824372901804801 1677492798618279676353601)
            ·
              refine ⟨1258119598963709757265201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677492798618279676353601 1258119598963709757265201)
              ·
                refine ⟨943589699222782317948901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258119598963709757265201 943589699222782317948901)
                ·
                  refine ⟨176923068604271684615419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943589699222782317948901 176923068604271684615419)
                  ·
                    rfl

theorem cell20_387626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_387626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387626 prefixEnd_387626 := by exact prefixLift 387626
  have htrace : WordTrace (prefixWord ++ tailWord_387626) baseStart_387626 baseEnd_387626 := by
    simpa [prefixWord, tailWord_387626, baseEnd_387626] using wordTrace_append hprefix tailTrace_387626
  have hstable : (prefixWord ++ tailWord_387626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387626).length < 2 ^ (prefixWord ++ tailWord_387626).sum := by decide
  have hdescent : baseEnd_387626 < baseStart_387626 := by decide
  rcases family_descends (prefixWord ++ tailWord_387626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387633 : List Nat := [1, 2, 2, 3, 1, 1, 6, 4]
def baseStart_387633 : Nat := 118140960795 + 387633 * 2 ^ 59
def prefixEnd_387633 : Nat := 4983230072969 + 3 ^ 40 * 387633 * 2
def baseEnd_387633 : Nat := 58975421198336923794019

theorem tailTrace_387633 : CollatzResearch.WordTrace tailWord_387633 prefixEnd_387633 58975421198336923794019 := by
  unfold tailWord_387633
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138137004679318290863553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9425424669786212193909035 14138137004679318290863553)
  ·
    refine ⟨10603602753509488718147665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14138137004679318290863553 10603602753509488718147665)
    ·
      refine ⟨7952702065132116538610749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10603602753509488718147665 7952702065132116538610749)
      ·
        refine ⟨2982263274424543701979031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7952702065132116538610749 2982263274424543701979031)
        ·
          refine ⟨4473394911636815552968547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982263274424543701979031 4473394911636815552968547)
          ·
            refine ⟨6710092367455223329452821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473394911636815552968547 6710092367455223329452821)
            ·
              refine ⟨314535579724463593568101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6710092367455223329452821 314535579724463593568101)
              ·
                refine ⟨58975421198336923794019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314535579724463593568101 58975421198336923794019)
                ·
                  rfl

theorem cell20_387633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_387633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387633 prefixEnd_387633 := by exact prefixLift 387633
  have htrace : WordTrace (prefixWord ++ tailWord_387633) baseStart_387633 baseEnd_387633 := by
    simpa [prefixWord, tailWord_387633, baseEnd_387633] using wordTrace_append hprefix tailTrace_387633
  have hstable : (prefixWord ++ tailWord_387633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387633).length < 2 ^ (prefixWord ++ tailWord_387633).sum := by decide
  have hdescent : baseEnd_387633 < baseStart_387633 := by decide
  rcases family_descends (prefixWord ++ tailWord_387633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387692 : List Nat := [2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_387692 : Nat := 118140960795 + 387692 * 2 ^ 59
def prefixEnd_387692 : Nat := 4983230072969 + 3 ^ 40 * 387692 * 2
def baseEnd_387692 : Nat := 58984397600889596138383

theorem tailTrace_387692 : CollatzResearch.WordTrace tailWord_387692 prefixEnd_387692 58984397600889596138383 := by
  unfold tailWord_387692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070144455732785683630665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9426859274310380911507553 7070144455732785683630665)
  ·
    refine ⟨5302608341799589262722999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7070144455732785683630665 5302608341799589262722999)
    ·
      refine ⟨7953912512699383894084499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5302608341799589262722999 7953912512699383894084499)
      ·
        refine ⟨11930868769049075841126749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953912512699383894084499 11930868769049075841126749)
        ·
          refine ⟨4474075788393403440422531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11930868769049075841126749 4474075788393403440422531)
          ·
            refine ⟨6711113682590105160633797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474075788393403440422531 6711113682590105160633797)
            ·
              refine ⟨1258333815485644717618837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6711113682590105160633797 1258333815485644717618837)
              ·
                refine ⟨58984397600889596138383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1258333815485644717618837 58984397600889596138383)
                ·
                  rfl

theorem cell20_387692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_387692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387692 prefixEnd_387692 := by exact prefixLift 387692
  have htrace : WordTrace (prefixWord ++ tailWord_387692) baseStart_387692 baseEnd_387692 := by
    simpa [prefixWord, tailWord_387692, baseEnd_387692] using wordTrace_append hprefix tailTrace_387692
  have hstable : (prefixWord ++ tailWord_387692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387692).length < 2 ^ (prefixWord ++ tailWord_387692).sum := by decide
  have hdescent : baseEnd_387692 < baseStart_387692 := by decide
  rcases family_descends (prefixWord ++ tailWord_387692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387699 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_387699 : Nat := 118140960795 + 387699 * 2 ^ 59
def prefixEnd_387699 : Nat := 4983230072969 + 3 ^ 40 * 387699 * 2
def baseEnd_387699 : Nat := 176956387793407875181787

theorem tailTrace_387699 : CollatzResearch.WordTrace tailWord_387699 prefixEnd_387699 176956387793407875181787 := by
  unfold tailWord_387699
  simp only [CollatzResearch.WordTrace]
  refine ⟨14140544222440211562766151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9427029481626807708510767 14140544222440211562766151)
  ·
    refine ⟨21210816333660317344149227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14140544222440211562766151 21210816333660317344149227)
    ·
      refine ⟨31816224500490476016223841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21210816333660317344149227 31816224500490476016223841)
      ·
        refine ⟨23862168375367857012167881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31816224500490476016223841 23862168375367857012167881)
        ·
          refine ⟨17896626281525892759125911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23862168375367857012167881 17896626281525892759125911)
          ·
            refine ⟨26844939422288839138688867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17896626281525892759125911 26844939422288839138688867)
            ·
              refine ⟨40267409133433258708033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26844939422288839138688867 40267409133433258708033301)
              ·
                refine ⟨1887534803129684001939061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40267409133433258708033301 1887534803129684001939061)
                ·
                  refine ⟨176956387793407875181787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1887534803129684001939061 176956387793407875181787)
                  ·
                    rfl

theorem cell20_387699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_387699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387699 prefixEnd_387699 := by exact prefixLift 387699
  have htrace : WordTrace (prefixWord ++ tailWord_387699) baseStart_387699 baseEnd_387699 := by
    simpa [prefixWord, tailWord_387699, baseEnd_387699] using wordTrace_append hprefix tailTrace_387699
  have hstable : (prefixWord ++ tailWord_387699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387699).length < 2 ^ (prefixWord ++ tailWord_387699).sum := by decide
  have hdescent : baseEnd_387699 < baseStart_387699 := by decide
  rcases family_descends (prefixWord ++ tailWord_387699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387709 : List Nat := [1, 4, 1, 1, 6, 7]
def baseStart_387709 : Nat := 118140960795 + 387709 * 2 ^ 59
def prefixEnd_387709 : Nat := 4983230072969 + 3 ^ 40 * 387709 * 2
def baseEnd_387709 : Nat := 6554109335773788327719

theorem tailTrace_387709 : CollatzResearch.WordTrace tailWord_387709 prefixEnd_387709 6554109335773788327719 := by
  unfold tailWord_387709
  simp only [CollatzResearch.WordTrace]
  refine ⟨14140908952403983270630181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9427272634935988847086787 14140908952403983270630181)
  ·
    refine ⟨2651420428575746863243159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14140908952403983270630181 2651420428575746863243159)
    ·
      refine ⟨3977130642863620294864739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651420428575746863243159 3977130642863620294864739)
      ·
        refine ⟨5965695964295430442297109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977130642863620294864739 5965695964295430442297109)
        ·
          refine ⟨279641998326348301982677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5965695964295430442297109 279641998326348301982677)
          ·
            refine ⟨6554109335773788327719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 279641998326348301982677 6554109335773788327719)
            ·
              rfl

theorem cell20_387709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 7].length) (baseStart_387709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387709 prefixEnd_387709 := by exact prefixLift 387709
  have htrace : WordTrace (prefixWord ++ tailWord_387709) baseStart_387709 baseEnd_387709 := by
    simpa [prefixWord, tailWord_387709, baseEnd_387709] using wordTrace_append hprefix tailTrace_387709
  have hstable : (prefixWord ++ tailWord_387709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387709).length < 2 ^ (prefixWord ++ tailWord_387709).sum := by decide
  have hdescent : baseEnd_387709 < baseStart_387709 := by decide
  rcases family_descends (prefixWord ++ tailWord_387709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387740 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_387740 : Nat := 118140960795 + 387740 * 2 ^ 59
def prefixEnd_387740 : Nat := 4983230072969 + 3 ^ 40 * 387740 * 2
def baseEnd_387740 : Nat := 176975101310593954814953

theorem tailTrace_387740 : CollatzResearch.WordTrace tailWord_387740 prefixEnd_387740 176975101310593954814953 := by
  unfold tailWord_387740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7071019807645837782504337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9428026410194450376672449 7071019807645837782504337)
  ·
    refine ⟨5303264855734378336878253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7071019807645837782504337 5303264855734378336878253)
    ·
      refine ⟨1988724320900391876329345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5303264855734378336878253 1988724320900391876329345)
      ·
        refine ⟨1491543240675293907247009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1988724320900391876329345 1491543240675293907247009)
        ·
          refine ⟨1118657430506470430435257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1491543240675293907247009 1118657430506470430435257)
          ·
            refine ⟨838993072879852822826443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118657430506470430435257 838993072879852822826443)
            ·
              refine ⟨1258489609319779234239665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838993072879852822826443 1258489609319779234239665)
              ·
                refine ⟨943867206989834425679749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258489609319779234239665 943867206989834425679749)
                ·
                  refine ⟨176975101310593954814953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943867206989834425679749 176975101310593954814953)
                  ·
                    rfl

theorem cell20_387740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_387740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387740 prefixEnd_387740 := by exact prefixLift 387740
  have htrace : WordTrace (prefixWord ++ tailWord_387740) baseStart_387740 baseEnd_387740 := by
    simpa [prefixWord, tailWord_387740, baseEnd_387740] using wordTrace_append hprefix tailTrace_387740
  have hstable : (prefixWord ++ tailWord_387740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387740).length < 2 ^ (prefixWord ++ tailWord_387740).sum := by decide
  have hdescent : baseEnd_387740 < baseStart_387740 := by decide
  rcases family_descends (prefixWord ++ tailWord_387740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387757 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 2]
def baseStart_387757 : Nat := 118140960795 + 387757 * 2 ^ 59
def prefixEnd_387757 : Nat := 4983230072969 + 3 ^ 40 * 387757 * 2
def baseEnd_387757 : Nat := 176982860573817451248217

theorem tailTrace_387757 : CollatzResearch.WordTrace tailWord_387757 prefixEnd_387757 176982860573817451248217 := by
  unfold tailWord_387757
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142659656230087468377525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9428439770820058312251683 14142659656230087468377525)
  ·
    refine ⟨1325874342771570700160393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14142659656230087468377525 1325874342771570700160393)
    ·
      refine ⟨994405757078678025120295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1325874342771570700160393 994405757078678025120295)
      ·
        refine ⟨1491608635618017037680443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994405757078678025120295 1491608635618017037680443)
        ·
          refine ⟨2237412953427025556520665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491608635618017037680443 2237412953427025556520665)
          ·
            refine ⟨1678059715070269167390499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237412953427025556520665 1678059715070269167390499)
            ·
              refine ⟨2517089572605403751085749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678059715070269167390499 2517089572605403751085749)
              ·
                refine ⟨235977147431756601664289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2517089572605403751085749 235977147431756601664289)
                ·
                  refine ⟨176982860573817451248217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235977147431756601664289 176982860573817451248217)
                  ·
                    rfl

theorem cell20_387757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_387757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387757 prefixEnd_387757 := by exact prefixLift 387757
  have htrace : WordTrace (prefixWord ++ tailWord_387757) baseStart_387757 baseEnd_387757 := by
    simpa [prefixWord, tailWord_387757, baseEnd_387757] using wordTrace_append hprefix tailTrace_387757
  have hstable : (prefixWord ++ tailWord_387757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387757).length < 2 ^ (prefixWord ++ tailWord_387757).sum := by decide
  have hdescent : baseEnd_387757 < baseStart_387757 := by decide
  rcases family_descends (prefixWord ++ tailWord_387757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387788 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_387788 : Nat := 118140960795 + 387788 * 2 ^ 59
def prefixEnd_387788 : Nat := 4983230072969 + 3 ^ 40 * 387788 * 2
def baseEnd_387788 : Nat := 176997009818519121214757

theorem tailTrace_387788 : CollatzResearch.WordTrace tailWord_387788 prefixEnd_387788 176997009818519121214757 := by
  unfold tailWord_387788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7071895159558889881378009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9429193546078519841837345 7071895159558889881378009)
  ·
    refine ⟨5303921369669167411033507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7071895159558889881378009 5303921369669167411033507)
    ·
      refine ⟨7955882054503751116550261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5303921369669167411033507 7955882054503751116550261)
      ·
        refine ⟨745863942609726667176587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7955882054503751116550261 745863942609726667176587)
        ·
          refine ⟨1118795913914590000764881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745863942609726667176587 1118795913914590000764881)
          ·
            refine ⟨839096935435942500573661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118795913914590000764881 839096935435942500573661)
            ·
              refine ⟨314661350788478437715123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839096935435942500573661 314661350788478437715123)
              ·
                refine ⟨471992026182717656572685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314661350788478437715123 471992026182717656572685)
                ·
                  refine ⟨176997009818519121214757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471992026182717656572685 176997009818519121214757)
                  ·
                    rfl

theorem cell20_387788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_387788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387788 prefixEnd_387788 := by exact prefixLift 387788
  have htrace : WordTrace (prefixWord ++ tailWord_387788) baseStart_387788 baseEnd_387788 := by
    simpa [prefixWord, tailWord_387788, baseEnd_387788] using wordTrace_append hprefix tailTrace_387788
  have hstable : (prefixWord ++ tailWord_387788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387788).length < 2 ^ (prefixWord ++ tailWord_387788).sum := by decide
  have hdescent : baseEnd_387788 < baseStart_387788 := by decide
  rcases family_descends (prefixWord ++ tailWord_387788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387799 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_387799 : Nat := 118140960795 + 387799 * 2 ^ 59
def prefixEnd_387799 : Nat := 4983230072969 + 3 ^ 40 * 387799 * 2
def baseEnd_387799 : Nat := 177002030518251971848045

theorem tailTrace_387799 : CollatzResearch.WordTrace tailWord_387799 prefixEnd_387799 177002030518251971848045 := by
  unfold tailWord_387799
  simp only [CollatzResearch.WordTrace]
  refine ⟨14144191522077928641406451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9429461014718619094270967 14144191522077928641406451)
  ·
    refine ⟨21216287283116892962109677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14144191522077928641406451 21216287283116892962109677)
    ·
      refine ⟨7956107731168834860791129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21216287283116892962109677 7956107731168834860791129)
      ·
        refine ⟨5967080798376626145593347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7956107731168834860791129 5967080798376626145593347)
        ·
          refine ⟨8950621197564939218390021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5967080798376626145593347 8950621197564939218390021)
          ·
            refine ⟨1678241474543426103448129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8950621197564939218390021 1678241474543426103448129)
            ·
              refine ⟨1258681105907569577586097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1678241474543426103448129 1258681105907569577586097)
              ·
                refine ⟨944010829430677183189573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258681105907569577586097 944010829430677183189573)
                ·
                  refine ⟨177002030518251971848045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944010829430677183189573 177002030518251971848045)
                  ·
                    rfl

theorem cell20_387799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_387799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387799 prefixEnd_387799 := by exact prefixLift 387799
  have htrace : WordTrace (prefixWord ++ tailWord_387799) baseStart_387799 baseEnd_387799 := by
    simpa [prefixWord, tailWord_387799, baseEnd_387799] using wordTrace_append hprefix tailTrace_387799
  have hstable : (prefixWord ++ tailWord_387799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387799).length < 2 ^ (prefixWord ++ tailWord_387799).sum := by decide
  have hdescent : baseEnd_387799 < baseStart_387799 := by decide
  rcases family_descends (prefixWord ++ tailWord_387799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387829 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 4]
def baseStart_387829 : Nat := 118140960795 + 387829 * 2 ^ 59
def prefixEnd_387829 : Nat := 4983230072969 + 3 ^ 40 * 387829 * 2
def baseEnd_387829 : Nat := 177015723335705200847923

theorem tailTrace_387829 : CollatzResearch.WordTrace tailWord_387829 prefixEnd_387829 177015723335705200847923 := by
  unfold tailWord_387829
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145285711969243764998541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9430190474646162509999027 14145285711969243764998541)
  ·
    refine ⟨5304482141988466411874453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14145285711969243764998541 5304482141988466411874453)
    ·
      refine ⟨248647600405709363056615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5304482141988466411874453 248647600405709363056615)
      ·
        refine ⟨372971400608564044584923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248647600405709363056615 372971400608564044584923)
        ·
          refine ⟨559457100912846066877385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372971400608564044584923 559457100912846066877385)
          ·
            refine ⟨419592825684634550158039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559457100912846066877385 419592825684634550158039)
            ·
              refine ⟨629389238526951825237059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419592825684634550158039 629389238526951825237059)
              ·
                refine ⟨944083857790427737855589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629389238526951825237059 944083857790427737855589)
                ·
                  refine ⟨177015723335705200847923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944083857790427737855589 177015723335705200847923)
                  ·
                    rfl

theorem cell20_387829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_387829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387829 prefixEnd_387829 := by exact prefixLift 387829
  have htrace : WordTrace (prefixWord ++ tailWord_387829) baseStart_387829 baseEnd_387829 := by
    simpa [prefixWord, tailWord_387829, baseEnd_387829] using wordTrace_append hprefix tailTrace_387829
  have hstable : (prefixWord ++ tailWord_387829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387829).length < 2 ^ (prefixWord ++ tailWord_387829).sum := by decide
  have hdescent : baseEnd_387829 < baseStart_387829 := by decide
  rcases family_descends (prefixWord ++ tailWord_387829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387830 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_387830 : Nat := 118140960795 + 387830 * 2 ^ 59
def prefixEnd_387830 : Nat := 4983230072969 + 3 ^ 40 * 387830 * 2
def baseEnd_387830 : Nat := 177016179762953641814585

theorem tailTrace_387830 : CollatzResearch.WordTrace tailWord_387830 prefixEnd_387830 177016179762953641814585 := by
  unfold tailWord_387830
  simp only [CollatzResearch.WordTrace]
  refine ⟨884082636560351308486559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9430214789977080623856629 884082636560351308486559)
  ·
    refine ⟨1326123954840526962729839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884082636560351308486559 1326123954840526962729839)
    ·
      refine ⟨1989185932260790444094759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326123954840526962729839 1989185932260790444094759)
      ·
        refine ⟨2983778898391185666142139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989185932260790444094759 2983778898391185666142139)
        ·
          refine ⟨4475668347586778499213209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983778898391185666142139 4475668347586778499213209)
          ·
            refine ⟨3356751260690083874409907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475668347586778499213209 3356751260690083874409907)
            ·
              refine ⟨5035126891035125811614861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356751260690083874409907 5035126891035125811614861)
              ·
                refine ⟨1888172584138172179355573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5035126891035125811614861 1888172584138172179355573)
                ·
                  refine ⟨177016179762953641814585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888172584138172179355573 177016179762953641814585)
                  ·
                    rfl

theorem cell20_387830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_387830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387830 prefixEnd_387830 := by exact prefixLift 387830
  have htrace : WordTrace (prefixWord ++ tailWord_387830) baseStart_387830 baseEnd_387830 := by
    simpa [prefixWord, tailWord_387830, baseEnd_387830] using wordTrace_append hprefix tailTrace_387830
  have hstable : (prefixWord ++ tailWord_387830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387830).length < 2 ^ (prefixWord ++ tailWord_387830).sum := by decide
  have hdescent : baseEnd_387830 < baseStart_387830 := by decide
  rcases family_descends (prefixWord ++ tailWord_387830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387847 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_387847 : Nat := 118140960795 + 387847 * 2 ^ 59
def prefixEnd_387847 : Nat := 4983230072969 + 3 ^ 40 * 387847 * 2
def baseEnd_387847 : Nat := 177023939026177138247849

theorem tailTrace_387847 : CollatzResearch.WordTrace tailWord_387847 prefixEnd_387847 177023939026177138247849 := by
  unfold tailWord_387847
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145942225904032839153795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9430628150602688559435863 14145942225904032839153795)
  ·
    refine ⟨21218913338856049258730693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14145942225904032839153795 21218913338856049258730693)
    ·
      refine ⟨3978546251035509236012005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21218913338856049258730693 3978546251035509236012005)
      ·
        refine ⟨745977422069157981752251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3978546251035509236012005 745977422069157981752251)
        ·
          refine ⟨1118966133103736972628377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745977422069157981752251 1118966133103736972628377)
          ·
            refine ⟨839224599827802729471283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118966133103736972628377 839224599827802729471283)
            ·
              refine ⟨1258836899741704094206925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839224599827802729471283 1258836899741704094206925)
              ·
                refine ⟨472063837403139035327597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258836899741704094206925 472063837403139035327597)
                ·
                  refine ⟨177023939026177138247849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472063837403139035327597 177023939026177138247849)
                  ·
                    rfl

theorem cell20_387847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_387847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387847 prefixEnd_387847 := by exact prefixLift 387847
  have htrace : WordTrace (prefixWord ++ tailWord_387847) baseStart_387847 baseEnd_387847 := by
    simpa [prefixWord, tailWord_387847, baseEnd_387847] using wordTrace_append hprefix tailTrace_387847
  have hstable : (prefixWord ++ tailWord_387847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387847).length < 2 ^ (prefixWord ++ tailWord_387847).sum := by decide
  have hdescent : baseEnd_387847 < baseStart_387847 := by decide
  rcases family_descends (prefixWord ++ tailWord_387847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387913 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_387913 : Nat := 118140960795 + 387913 * 2 ^ 59
def prefixEnd_387913 : Nat := 4983230072969 + 3 ^ 40 * 387913 * 2
def baseEnd_387913 : Nat := 177054063224574242047579

theorem tailTrace_387913 : CollatzResearch.WordTrace tailWord_387913 prefixEnd_387913 177054063224574242047579 := by
  unfold tailWord_387913
  simp only [CollatzResearch.WordTrace]
  refine ⟨14148349443664926111056393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9432232962443284074037595 14148349443664926111056393)
  ·
    refine ⟨10611262082748694583292295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14148349443664926111056393 10611262082748694583292295)
    ·
      refine ⟨15916893124123041874938443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10611262082748694583292295 15916893124123041874938443)
      ·
        refine ⟨23875339686184562812407665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15916893124123041874938443 23875339686184562812407665)
        ·
          refine ⟨17906504764638422109305749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23875339686184562812407665 17906504764638422109305749)
          ·
            refine ⟨839367410842426036373707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17906504764638422109305749 839367410842426036373707)
            ·
              refine ⟨1259051116263639054560561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839367410842426036373707 1259051116263639054560561)
              ·
                refine ⟨944288337197729290920421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259051116263639054560561 944288337197729290920421)
                ·
                  refine ⟨177054063224574242047579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944288337197729290920421 177054063224574242047579)
                  ·
                    rfl

theorem cell20_387913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_387913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387913 prefixEnd_387913 := by exact prefixLift 387913
  have htrace : WordTrace (prefixWord ++ tailWord_387913) baseStart_387913 baseEnd_387913 := by
    simpa [prefixWord, tailWord_387913, baseEnd_387913] using wordTrace_append hprefix tailTrace_387913
  have hstable : (prefixWord ++ tailWord_387913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387913).length < 2 ^ (prefixWord ++ tailWord_387913).sum := by decide
  have hdescent : baseEnd_387913 < baseStart_387913 := by decide
  rcases family_descends (prefixWord ++ tailWord_387913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387930 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_387930 : Nat := 118140960795 + 387930 * 2 ^ 59
def prefixEnd_387930 : Nat := 4983230072969 + 3 ^ 40 * 387930 * 2
def baseEnd_387930 : Nat := 177061822487797738480843

theorem tailTrace_387930 : CollatzResearch.WordTrace tailWord_387930 prefixEnd_387930 177061822487797738480843 := by
  unfold tailWord_387930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537242371150834503606311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9432646323068892009616829 3537242371150834503606311)
  ·
    refine ⟨5305863556726251755409467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3537242371150834503606311 5305863556726251755409467)
    ·
      refine ⟨7958795335089377633114201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5305863556726251755409467 7958795335089377633114201)
      ·
        refine ⟨5969096501317033224835651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7958795335089377633114201 5969096501317033224835651)
        ·
          refine ⟨8953644751975549837253477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969096501317033224835651 8953644751975549837253477)
          ·
            refine ⟨1678808390995415594485027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8953644751975549837253477 1678808390995415594485027)
            ·
              refine ⟨2518212586493123391727541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678808390995415594485027 2518212586493123391727541)
              ·
                refine ⟨236082429983730317974457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2518212586493123391727541 236082429983730317974457)
                ·
                  refine ⟨177061822487797738480843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236082429983730317974457 177061822487797738480843)
                  ·
                    rfl

theorem cell20_387930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_387930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387930 prefixEnd_387930 := by exact prefixLift 387930
  have htrace : WordTrace (prefixWord ++ tailWord_387930) baseStart_387930 baseEnd_387930 := by
    simpa [prefixWord, tailWord_387930, baseEnd_387930] using wordTrace_append hprefix tailTrace_387930
  have hstable : (prefixWord ++ tailWord_387930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387930).length < 2 ^ (prefixWord ++ tailWord_387930).sum := by decide
  have hdescent : baseEnd_387930 < baseStart_387930 := by decide
  rcases family_descends (prefixWord ++ tailWord_387930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387944 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_387944 : Nat := 118140960795 + 387944 * 2 ^ 59
def prefixEnd_387944 : Nat := 4983230072969 + 3 ^ 40 * 387944 * 2
def baseEnd_387944 : Nat := 177068212469275912014119

theorem tailTrace_387944 : CollatzResearch.WordTrace tailWord_387944 prefixEnd_387944 177068212469275912014119 := by
  unfold tailWord_387944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7074740053276309202717443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9432986737701745603623257 7074740053276309202717443)
  ·
    refine ⟨10612110079914463804076165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7074740053276309202717443 10612110079914463804076165)
    ·
      refine ⟨1989770639983961963264281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10612110079914463804076165 1989770639983961963264281)
      ·
        refine ⟨1492327979987971472448211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1989770639983961963264281 1492327979987971472448211)
        ·
          refine ⟨2238491969981957208672317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492327979987971472448211 2238491969981957208672317)
          ·
            refine ⟨839434488743233953252119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2238491969981957208672317 839434488743233953252119)
            ·
              refine ⟨1259151733114850929878179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839434488743233953252119 1259151733114850929878179)
              ·
                refine ⟨1888727599672276394817269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259151733114850929878179 1888727599672276394817269)
                ·
                  refine ⟨177068212469275912014119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888727599672276394817269 177068212469275912014119)
                  ·
                    rfl

theorem cell20_387944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_387944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387944 prefixEnd_387944 := by exact prefixLift 387944
  have htrace : WordTrace (prefixWord ++ tailWord_387944) baseStart_387944 baseEnd_387944 := by
    simpa [prefixWord, tailWord_387944, baseEnd_387944] using wordTrace_append hprefix tailTrace_387944
  have hstable : (prefixWord ++ tailWord_387944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387944).length < 2 ^ (prefixWord ++ tailWord_387944).sum := by decide
  have hdescent : baseEnd_387944 < baseStart_387944 := by decide
  rcases family_descends (prefixWord ++ tailWord_387944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387961 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 3]
def baseStart_387961 : Nat := 118140960795 + 387961 * 2 ^ 59
def prefixEnd_387961 : Nat := 4983230072969 + 3 ^ 40 * 387961 * 2
def baseEnd_387961 : Nat := 177075971732499408447383

theorem tailTrace_387961 : CollatzResearch.WordTrace tailWord_387961 prefixEnd_387961 177075971732499408447383 := by
  unfold tailWord_387961
  simp only [CollatzResearch.WordTrace]
  refine ⟨14150100147491030308803737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9433400098327353539202491 14150100147491030308803737)
  ·
    refine ⟨10612575110618272731602803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14150100147491030308803737 10612575110618272731602803)
    ·
      refine ⟨15918862665927409097404205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10612575110618272731602803 15918862665927409097404205)
      ·
        refine ⟨5969573499722778411526577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15918862665927409097404205 5969573499722778411526577)
        ·
          refine ⟨4477180124792083808644933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5969573499722778411526577 4477180124792083808644933)
          ·
            refine ⟨839471273398515714120925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4477180124792083808644933 839471273398515714120925)
            ·
              refine ⟨314801727524443392795347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839471273398515714120925 314801727524443392795347)
              ·
                refine ⟨472202591286665089193021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314801727524443392795347 472202591286665089193021)
                ·
                  refine ⟨177075971732499408447383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472202591286665089193021 177075971732499408447383)
                  ·
                    rfl

theorem cell20_387961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_387961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387961 prefixEnd_387961 := by exact prefixLift 387961
  have htrace : WordTrace (prefixWord ++ tailWord_387961) baseStart_387961 baseEnd_387961 := by
    simpa [prefixWord, tailWord_387961, baseEnd_387961] using wordTrace_append hprefix tailTrace_387961
  have hstable : (prefixWord ++ tailWord_387961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387961).length < 2 ^ (prefixWord ++ tailWord_387961).sum := by decide
  have hdescent : baseEnd_387961 < baseStart_387961 := by decide
  rcases family_descends (prefixWord ++ tailWord_387961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387975 : List Nat := [1, 1, 4, 2, 3, 1, 4, 4]
def baseStart_387975 : Nat := 118140960795 + 387975 * 2 ^ 59
def prefixEnd_387975 : Nat := 4983230072969 + 3 ^ 40 * 387975 * 2
def baseEnd_387975 : Nat := 59027453904659193993553

theorem tailTrace_387975 : CollatzResearch.WordTrace tailWord_387975 prefixEnd_387975 59027453904659193993553 := by
  unfold tailWord_387975
  simp only [CollatzResearch.WordTrace]
  refine ⟨14150610769440310699813379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9433740512960207133208919 14150610769440310699813379)
  ·
    refine ⟨21225916154160466049720069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14150610769440310699813379 21225916154160466049720069)
    ·
      refine ⟨3979859278905087384322513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21225916154160466049720069 3979859278905087384322513)
      ·
        refine ⟨2984894459178815538241885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979859278905087384322513 2984894459178815538241885)
        ·
          refine ⟨1119335422192055826840707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2984894459178815538241885 1119335422192055826840707)
          ·
            refine ⟨1679003133288083740261061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119335422192055826840707 1679003133288083740261061)
            ·
              refine ⟨314813087491515701298949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1679003133288083740261061 314813087491515701298949)
              ·
                refine ⟨59027453904659193993553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314813087491515701298949 59027453904659193993553)
                ·
                  rfl

theorem cell20_387975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_387975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_387975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_387975 prefixEnd_387975 := by exact prefixLift 387975
  have htrace : WordTrace (prefixWord ++ tailWord_387975) baseStart_387975 baseEnd_387975 := by
    simpa [prefixWord, tailWord_387975, baseEnd_387975] using wordTrace_append hprefix tailTrace_387975
  have hstable : (prefixWord ++ tailWord_387975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387975).length < 2 ^ (prefixWord ++ tailWord_387975).sum := by decide
  have hdescent : baseEnd_387975 < baseStart_387975 := by decide
  rcases family_descends (prefixWord ++ tailWord_387975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388002 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_388002 : Nat := 118140960795 + 388002 * 2 ^ 59
def prefixEnd_388002 : Nat := 4983230072969 + 3 ^ 40 * 388002 * 2
def baseEnd_388002 : Nat := 177094685249685488080549

theorem tailTrace_388002 : CollatzResearch.WordTrace tailWord_388002 prefixEnd_388002 177094685249685488080549 := by
  unfold tailWord_388002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537898885085623577761565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9434397026894996207364173 3537898885085623577761565)
  ·
    refine ⟨1326712081907108841660587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3537898885085623577761565 1326712081907108841660587)
    ·
      refine ⟨1990068122860663262490881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326712081907108841660587 1990068122860663262490881)
      ·
        refine ⟨1492551092145497446868161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1990068122860663262490881 1492551092145497446868161)
        ·
          refine ⟨1119413319109123085151121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492551092145497446868161 1119413319109123085151121)
          ·
            refine ⟨839559989331842313863341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119413319109123085151121 839559989331842313863341)
            ·
              refine ⟨314834995999440867698753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839559989331842313863341 314834995999440867698753)
              ·
                refine ⟨236126246999580650774065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314834995999440867698753 236126246999580650774065)
                ·
                  refine ⟨177094685249685488080549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236126246999580650774065 177094685249685488080549)
                  ·
                    rfl

theorem cell20_388002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_388002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388002 prefixEnd_388002 := by exact prefixLift 388002
  have htrace : WordTrace (prefixWord ++ tailWord_388002) baseStart_388002 baseEnd_388002 := by
    simpa [prefixWord, tailWord_388002, baseEnd_388002] using wordTrace_append hprefix tailTrace_388002
  have hstable : (prefixWord ++ tailWord_388002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388002).length < 2 ^ (prefixWord ++ tailWord_388002).sum := by decide
  have hdescent : baseEnd_388002 < baseStart_388002 := by decide
  rcases family_descends (prefixWord ++ tailWord_388002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388003 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_388003 : Nat := 118140960795 + 388003 * 2 ^ 59
def prefixEnd_388003 : Nat := 4983230072969 + 3 ^ 40 * 388003 * 2
def baseEnd_388003 : Nat := 177095141676933929047211

theorem tailTrace_388003 : CollatzResearch.WordTrace tailWord_388003 prefixEnd_388003 177095141676933929047211 := by
  unfold tailWord_388003
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151632013338871481832663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9434421342225914321221775 14151632013338871481832663)
  ·
    refine ⟨21227448020008307222748995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14151632013338871481832663 21227448020008307222748995)
    ·
      refine ⟨31841172030012460834123493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21227448020008307222748995 31841172030012460834123493)
      ·
        refine ⟨5970219755627336406398155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31841172030012460834123493 5970219755627336406398155)
        ·
          refine ⟨8955329633441004609597233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970219755627336406398155 8955329633441004609597233)
          ·
            refine ⟨6716497225080753457197925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8955329633441004609597233 6716497225080753457197925)
            ·
              refine ⟨1259343229702641273224611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6716497225080753457197925 1259343229702641273224611)
              ·
                refine ⟨1889014844553961909836917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259343229702641273224611 1889014844553961909836917)
                ·
                  refine ⟨177095141676933929047211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1889014844553961909836917 177095141676933929047211)
                  ·
                    rfl

theorem cell20_388003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_388003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388003 prefixEnd_388003 := by exact prefixLift 388003
  have htrace : WordTrace (prefixWord ++ tailWord_388003) baseStart_388003 baseEnd_388003 := by
    simpa [prefixWord, tailWord_388003, baseEnd_388003] using wordTrace_append hprefix tailTrace_388003
  have hstable : (prefixWord ++ tailWord_388003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388003).length < 2 ^ (prefixWord ++ tailWord_388003).sum := by decide
  have hdescent : baseEnd_388003 < baseStart_388003 := by decide
  rcases family_descends (prefixWord ++ tailWord_388003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388044 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 2]
def baseStart_388044 : Nat := 118140960795 + 388044 * 2 ^ 59
def prefixEnd_388044 : Nat := 4983230072969 + 3 ^ 40 * 388044 * 2
def baseEnd_388044 : Nat := 177113855194120008680377

theorem tailTrace_388044 : CollatzResearch.WordTrace tailWord_388044 prefixEnd_388044 177113855194120008680377 := by
  unfold tailWord_388044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076563703095167742037593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9435418270793556989383457 7076563703095167742037593)
  ·
    refine ⟨5307422777321375806528195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7076563703095167742037593 5307422777321375806528195)
    ·
      refine ⟨7961134165982063709792293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5307422777321375806528195 7961134165982063709792293)
      ·
        refine ⟨1492712656121636945586055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7961134165982063709792293 1492712656121636945586055)
        ·
          refine ⟨2239068984182455418379083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492712656121636945586055 2239068984182455418379083)
          ·
            refine ⟨3358603476273683127568625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239068984182455418379083 3358603476273683127568625)
            ·
              refine ⟨2518952607205262345676469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358603476273683127568625 2518952607205262345676469)
              ·
                refine ⟨236151806925493344907169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2518952607205262345676469 236151806925493344907169)
                ·
                  refine ⟨177113855194120008680377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236151806925493344907169 177113855194120008680377)
                  ·
                    rfl

theorem cell20_388044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_388044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388044 prefixEnd_388044 := by exact prefixLift 388044
  have htrace : WordTrace (prefixWord ++ tailWord_388044) baseStart_388044 baseEnd_388044 := by
    simpa [prefixWord, tailWord_388044, baseEnd_388044] using wordTrace_append hprefix tailTrace_388044
  have hstable : (prefixWord ++ tailWord_388044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388044).length < 2 ^ (prefixWord ++ tailWord_388044).sum := by decide
  have hdescent : baseEnd_388044 < baseStart_388044 := by decide
  rcases family_descends (prefixWord ++ tailWord_388044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388054 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_388054 : Nat := 118140960795 + 388054 * 2 ^ 59
def prefixEnd_388054 : Nat := 4983230072969 + 3 ^ 40 * 388054 * 2
def baseEnd_388054 : Nat := 177118419466604418347003

theorem tailTrace_388054 : CollatzResearch.WordTrace tailWord_388054 prefixEnd_388054 177118419466604418347003 := by
  unfold tailWord_388054
  simp only [CollatzResearch.WordTrace]
  refine ⟨884593258509631699496201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9435661424102738127959477 884593258509631699496201)
  ·
    refine ⟨663444943882223774622151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 884593258509631699496201 663444943882223774622151)
    ·
      refine ⟨995167415823335661933227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663444943882223774622151 995167415823335661933227)
      ·
        refine ⟨1492751123735003492899841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995167415823335661933227 1492751123735003492899841)
        ·
          refine ⟨1119563342801252619674881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492751123735003492899841 1119563342801252619674881)
          ·
            refine ⟨839672507100939464756161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119563342801252619674881 839672507100939464756161)
            ·
              refine ⟨629754380325704598567121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839672507100939464756161 629754380325704598567121)
              ·
                refine ⟨472315785244278448925341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629754380325704598567121 472315785244278448925341)
                ·
                  refine ⟨177118419466604418347003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472315785244278448925341 177118419466604418347003)
                  ·
                    rfl

theorem cell20_388054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_388054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388054 prefixEnd_388054 := by exact prefixLift 388054
  have htrace : WordTrace (prefixWord ++ tailWord_388054) baseStart_388054 baseEnd_388054 := by
    simpa [prefixWord, tailWord_388054, baseEnd_388054] using wordTrace_append hprefix tailTrace_388054
  have hstable : (prefixWord ++ tailWord_388054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388054).length < 2 ^ (prefixWord ++ tailWord_388054).sum := by decide
  have hdescent : baseEnd_388054 < baseStart_388054 := by decide
  rcases family_descends (prefixWord ++ tailWord_388054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388058 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_388058 : Nat := 118140960795 + 388058 * 2 ^ 59
def prefixEnd_388058 : Nat := 4983230072969 + 3 ^ 40 * 388058 * 2
def baseEnd_388058 : Nat := 177120245175598182213653

theorem tailTrace_388058 : CollatzResearch.WordTrace tailWord_388058 prefixEnd_388058 177120245175598182213653 := by
  unfold tailWord_388058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538409507034903968771207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9435758685426410583389885 3538409507034903968771207)
  ·
    refine ⟨5307614260552355953156811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538409507034903968771207 5307614260552355953156811)
    ·
      refine ⟨7961421390828533929735217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5307614260552355953156811 7961421390828533929735217)
      ·
        refine ⟨5971066043121400447301413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7961421390828533929735217 5971066043121400447301413)
        ·
          refine ⟨1119574883085262583869015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5971066043121400447301413 1119574883085262583869015)
          ·
            refine ⟨1679362324627893875803523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119574883085262583869015 1679362324627893875803523)
            ·
              refine ⟨2519043486941840813705285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679362324627893875803523 2519043486941840813705285)
              ·
                refine ⟨472320653801595152569741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2519043486941840813705285 472320653801595152569741)
                ·
                  refine ⟨177120245175598182213653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472320653801595152569741 177120245175598182213653)
                  ·
                    rfl

theorem cell20_388058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_388058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388058 prefixEnd_388058 := by exact prefixLift 388058
  have htrace : WordTrace (prefixWord ++ tailWord_388058) baseStart_388058 baseEnd_388058 := by
    simpa [prefixWord, tailWord_388058, baseEnd_388058] using wordTrace_append hprefix tailTrace_388058
  have hstable : (prefixWord ++ tailWord_388058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388058).length < 2 ^ (prefixWord ++ tailWord_388058).sum := by decide
  have hdescent : baseEnd_388058 < baseStart_388058 := by decide
  rcases family_descends (prefixWord ++ tailWord_388058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388061 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 2]
def baseStart_388061 : Nat := 118140960795 + 388061 * 2 ^ 59
def prefixEnd_388061 : Nat := 4983230072969 + 3 ^ 40 * 388061 * 2
def baseEnd_388061 : Nat := 177121614457343505113641

theorem tailTrace_388061 : CollatzResearch.WordTrace tailWord_388061 prefixEnd_388061 177121614457343505113641 := by
  unfold tailWord_388061
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153747447128747387444037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9435831631419164924962691 14153747447128747387444037)
  ·
    refine ⟨2653827646336640135145757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14153747447128747387444037 2653827646336640135145757)
    ·
      refine ⟨995185367376240050679659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2653827646336640135145757 995185367376240050679659)
      ·
        refine ⟨1492778051064360076019489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995185367376240050679659 1492778051064360076019489)
        ·
          refine ⟨1119583538298270057014617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492778051064360076019489 1119583538298270057014617)
          ·
            refine ⟨839687653723702542760963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119583538298270057014617 839687653723702542760963)
            ·
              refine ⟨1259531480585553814141445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839687653723702542760963 1259531480585553814141445)
              ·
                refine ⟨236162152609791340151521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1259531480585553814141445 236162152609791340151521)
                ·
                  refine ⟨177121614457343505113641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236162152609791340151521 177121614457343505113641)
                  ·
                    rfl

theorem cell20_388061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_388061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388061 prefixEnd_388061 := by exact prefixLift 388061
  have htrace : WordTrace (prefixWord ++ tailWord_388061) baseStart_388061 baseEnd_388061 := by
    simpa [prefixWord, tailWord_388061, baseEnd_388061] using wordTrace_append hprefix tailTrace_388061
  have hstable : (prefixWord ++ tailWord_388061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388061).length < 2 ^ (prefixWord ++ tailWord_388061).sum := by decide
  have hdescent : baseEnd_388061 < baseStart_388061 := by decide
  rcases family_descends (prefixWord ++ tailWord_388061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388072 : List Nat := [2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_388072 : Nat := 118140960795 + 388072 * 2 ^ 59
def prefixEnd_388072 : Nat := 4983230072969 + 3 ^ 40 * 388072 * 2
def baseEnd_388072 : Nat := 59042211719025451915643

theorem tailTrace_388072 : CollatzResearch.WordTrace tailWord_388072 prefixEnd_388072 59042211719025451915643 := by
  unfold tailWord_388072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077074325044448133047235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9436099100059264177396313 7077074325044448133047235)
  ·
    refine ⟨10615611487566672199570853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7077074325044448133047235 10615611487566672199570853)
    ·
      refine ⟨1990427153918751037419535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10615611487566672199570853 1990427153918751037419535)
      ·
        refine ⟨2985640730878126556129303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990427153918751037419535 2985640730878126556129303)
        ·
          refine ⟨4478461096317189834193955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2985640730878126556129303 4478461096317189834193955)
          ·
            refine ⟨6717691644475784751290933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478461096317189834193955 6717691644475784751290933)
            ·
              refine ⟨629783591669604820433525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6717691644475784751290933 629783591669604820433525)
              ·
                refine ⟨59042211719025451915643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629783591669604820433525 59042211719025451915643)
                ·
                  rfl

theorem cell20_388072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_388072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388072 prefixEnd_388072 := by exact prefixLift 388072
  have htrace : WordTrace (prefixWord ++ tailWord_388072) baseStart_388072 baseEnd_388072 := by
    simpa [prefixWord, tailWord_388072, baseEnd_388072] using wordTrace_append hprefix tailTrace_388072
  have hstable : (prefixWord ++ tailWord_388072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388072).length < 2 ^ (prefixWord ++ tailWord_388072).sum := by decide
  have hdescent : baseEnd_388072 < baseStart_388072 := by decide
  rcases family_descends (prefixWord ++ tailWord_388072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388085 : List Nat := [1, 3, 5, 2, 1, 1, 3, 4]
def baseStart_388085 : Nat := 118140960795 + 388085 * 2 ^ 59
def prefixEnd_388085 : Nat := 4983230072969 + 3 ^ 40 * 388085 * 2
def baseEnd_388085 : Nat := 59044189570435362771181

theorem tailTrace_388085 : CollatzResearch.WordTrace tailWord_388085 prefixEnd_388085 59044189570435362771181 := by
  unfold tailWord_388085
  simp only [CollatzResearch.WordTrace]
  refine ⟨14154622799041799486317709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9436415199361199657545139 14154622799041799486317709)
  ·
    refine ⟨5307983549640674807369141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14154622799041799486317709 5307983549640674807369141)
    ·
      refine ⟨497623457778813263190857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5307983549640674807369141 497623457778813263190857)
      ·
        refine ⟨373217593334109947393143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497623457778813263190857 373217593334109947393143)
        ·
          refine ⟨559826390001164921089715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373217593334109947393143 559826390001164921089715)
          ·
            refine ⟨839739585001747381634573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559826390001164921089715 839739585001747381634573)
            ·
              refine ⟨314902344375655268112965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839739585001747381634573 314902344375655268112965)
              ·
                refine ⟨59044189570435362771181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314902344375655268112965 59044189570435362771181)
                ·
                  rfl

theorem cell20_388085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_388085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388085 prefixEnd_388085 := by exact prefixLift 388085
  have htrace : WordTrace (prefixWord ++ tailWord_388085) baseStart_388085 baseEnd_388085 := by
    simpa [prefixWord, tailWord_388085, baseEnd_388085] using wordTrace_append hprefix tailTrace_388085
  have hstable : (prefixWord ++ tailWord_388085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388085).length < 2 ^ (prefixWord ++ tailWord_388085).sum := by decide
  have hdescent : baseEnd_388085 < baseStart_388085 := by decide
  rcases family_descends (prefixWord ++ tailWord_388085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388110 : List Nat := [4, 1, 1, 2, 2, 3, 7]
def baseStart_388110 : Nat := 118140960795 + 388110 * 2 ^ 59
def prefixEnd_388110 : Nat := 4983230072969 + 3 ^ 40 * 388110 * 2
def baseEnd_388110 : Nat := 19682664376946345831123

theorem tailTrace_388110 : CollatzResearch.WordTrace tailWord_388110 prefixEnd_388110 19682664376946345831123 := by
  unfold tailWord_388110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769441827993903594497223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9437023082634152503985189 1769441827993903594497223)
  ·
    refine ⟨2654162741990855391745835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1769441827993903594497223 2654162741990855391745835)
    ·
      refine ⟨3981244112986283087618753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2654162741990855391745835 3981244112986283087618753)
      ·
        refine ⟨2985933084739712315714065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3981244112986283087618753 2985933084739712315714065)
        ·
          refine ⟨2239449813554784236785549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2985933084739712315714065 2239449813554784236785549)
          ·
            refine ⟨839793680083044088794581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2239449813554784236785549 839793680083044088794581)
            ·
              refine ⟨19682664376946345831123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 839793680083044088794581 19682664376946345831123)
              ·
                rfl

theorem cell20_388110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_388110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388110 prefixEnd_388110 := by exact prefixLift 388110
  have htrace : WordTrace (prefixWord ++ tailWord_388110) baseStart_388110 baseEnd_388110 := by
    simpa [prefixWord, tailWord_388110, baseEnd_388110] using wordTrace_append hprefix tailTrace_388110
  have hstable : (prefixWord ++ tailWord_388110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388110).length < 2 ^ (prefixWord ++ tailWord_388110).sum := by decide
  have hdescent : baseEnd_388110 < baseStart_388110 := by decide
  rcases family_descends (prefixWord ++ tailWord_388110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388120 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 2]
def baseStart_388120 : Nat := 118140960795 + 388120 * 2 ^ 59
def prefixEnd_388120 : Nat := 4983230072969 + 3 ^ 40 * 388120 * 2
def baseEnd_388120 : Nat := 177148543665001522146733

theorem tailTrace_388120 : CollatzResearch.WordTrace tailWord_388120 prefixEnd_388120 177148543665001522146733 := by
  unfold tailWord_388120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077949676957500231920907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9437266235943333642561209 7077949676957500231920907)
  ·
    refine ⟨10616924515436250347881361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7077949676957500231920907 10616924515436250347881361)
    ·
      refine ⟨7962693386577187760911021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10616924515436250347881361 7962693386577187760911021)
      ·
        refine ⟨2986010019966445410341633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7962693386577187760911021 2986010019966445410341633)
        ·
          refine ⟨2239507514974834057756225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2986010019966445410341633 2239507514974834057756225)
          ·
            refine ⟨1679630636231125543317169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239507514974834057756225 1679630636231125543317169)
            ·
              refine ⟨1259722977173344157487877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679630636231125543317169 1259722977173344157487877)
              ·
                refine ⟨236198058220002029528977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1259722977173344157487877 236198058220002029528977)
                ·
                  refine ⟨177148543665001522146733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236198058220002029528977 177148543665001522146733)
                  ·
                    rfl

theorem cell20_388120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_388120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388120 prefixEnd_388120 := by exact prefixLift 388120
  have htrace : WordTrace (prefixWord ++ tailWord_388120) baseStart_388120 baseEnd_388120 := by
    simpa [prefixWord, tailWord_388120, baseEnd_388120] using wordTrace_append hprefix tailTrace_388120
  have hstable : (prefixWord ++ tailWord_388120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388120).length < 2 ^ (prefixWord ++ tailWord_388120).sum := by decide
  have hdescent : baseEnd_388120 < baseStart_388120 := by decide
  rcases family_descends (prefixWord ++ tailWord_388120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388207 : List Nat := [1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_388207 : Nat := 118140960795 + 388207 * 2 ^ 59
def prefixEnd_388207 : Nat := 4983230072969 + 3 ^ 40 * 388207 * 2
def baseEnd_388207 : Nat := 59062750945205295415459

theorem tailTrace_388207 : CollatzResearch.WordTrace tailWord_388207 prefixEnd_388207 59062750945205295415459 := by
  unfold tailWord_388207
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159072504599814322258875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9439381669733209548172583 14159072504599814322258875)
  ·
    refine ⟨21238608756899721483388313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14159072504599814322258875 21238608756899721483388313)
    ·
      refine ⟨15928956567674791112541235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21238608756899721483388313 15928956567674791112541235)
      ·
        refine ⟨23893434851512186668811853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15928956567674791112541235 23893434851512186668811853)
        ·
          refine ⟨8960038069317070000804445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23893434851512186668811853 8960038069317070000804445)
          ·
            refine ⟨3360014275993901250301667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8960038069317070000804445 3360014275993901250301667)
            ·
              refine ⟨5040021413990851875452501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360014275993901250301667 5040021413990851875452501)
              ·
                refine ⟨59062750945205295415459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5040021413990851875452501 59062750945205295415459)
                ·
                  rfl

theorem cell20_388207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_388207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388207 prefixEnd_388207 := by exact prefixLift 388207
  have htrace : WordTrace (prefixWord ++ tailWord_388207) baseStart_388207 baseEnd_388207 := by
    simpa [prefixWord, tailWord_388207, baseEnd_388207] using wordTrace_append hprefix tailTrace_388207
  have hstable : (prefixWord ++ tailWord_388207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388207).length < 2 ^ (prefixWord ++ tailWord_388207).sum := by decide
  have hdescent : baseEnd_388207 < baseStart_388207 := by decide
  rcases family_descends (prefixWord ++ tailWord_388207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388234 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_388234 : Nat := 118140960795 + 388234 * 2 ^ 59
def prefixEnd_388234 : Nat := 4983230072969 + 3 ^ 40 * 388234 * 2
def baseEnd_388234 : Nat := 177200576371323792346267

theorem tailTrace_388234 : CollatzResearch.WordTrace tailWord_388234 prefixEnd_388234 177200576371323792346267 := by
  unfold tailWord_388234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540014318875499483372939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9440038183667998622327837 3540014318875499483372939)
  ·
    refine ⟨5310021478313249225059409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3540014318875499483372939 5310021478313249225059409)
    ·
      refine ⟨3982516108734936918794557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5310021478313249225059409 3982516108734936918794557)
      ·
        refine ⟨1493443540775601344547959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3982516108734936918794557 1493443540775601344547959)
        ·
          refine ⟨2240165311163402016821939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493443540775601344547959 2240165311163402016821939)
          ·
            refine ⟨3360247966745103025232909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240165311163402016821939 3360247966745103025232909)
            ·
              refine ⟨1260092987529413634462341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3360247966745103025232909 1260092987529413634462341)
              ·
                refine ⟨236267435161765056461689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1260092987529413634462341 236267435161765056461689)
                ·
                  refine ⟨177200576371323792346267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236267435161765056461689 177200576371323792346267)
                  ·
                    rfl

theorem cell20_388234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_388234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388234 prefixEnd_388234 := by exact prefixLift 388234
  have htrace : WordTrace (prefixWord ++ tailWord_388234) baseStart_388234 baseEnd_388234 := by
    simpa [prefixWord, tailWord_388234, baseEnd_388234] using wordTrace_append hprefix tailTrace_388234
  have hstable : (prefixWord ++ tailWord_388234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388234).length < 2 ^ (prefixWord ++ tailWord_388234).sum := by decide
  have hdescent : baseEnd_388234 < baseStart_388234 := by decide
  rcases family_descends (prefixWord ++ tailWord_388234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388245 : List Nat := [1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_388245 : Nat := 118140960795 + 388245 * 2 ^ 59
def prefixEnd_388245 : Nat := 4983230072969 + 3 ^ 40 * 388245 * 2
def baseEnd_388245 : Nat := 59068532357018880993185

theorem tailTrace_388245 : CollatzResearch.WordTrace tailWord_388245 prefixEnd_388245 59068532357018880993185 := by
  unfold tailWord_388245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14160458478462146812142189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9440305652308097874761459 14160458478462146812142189)
  ·
    refine ⟨5310171929423305054553321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14160458478462146812142189 5310171929423305054553321)
    ·
      refine ⟨3982628947067478790914991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5310171929423305054553321 3982628947067478790914991)
      ·
        refine ⟨5973943420601218186372487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982628947067478790914991 5973943420601218186372487)
        ·
          refine ⟨8960915130901827279558731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973943420601218186372487 8960915130901827279558731)
          ·
            refine ⟨13441372696352740919338097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8960915130901827279558731 13441372696352740919338097)
            ·
              refine ⟨10081029522264555689503573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13441372696352740919338097 10081029522264555689503573)
              ·
                refine ⟨59068532357018880993185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10081029522264555689503573 59068532357018880993185)
                ·
                  rfl

theorem cell20_388245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_388245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388245 prefixEnd_388245 := by exact prefixLift 388245
  have htrace : WordTrace (prefixWord ++ tailWord_388245) baseStart_388245 baseEnd_388245 := by
    simpa [prefixWord, tailWord_388245, baseEnd_388245] using wordTrace_append hprefix tailTrace_388245
  have hstable : (prefixWord ++ tailWord_388245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388245).length < 2 ^ (prefixWord ++ tailWord_388245).sum := by decide
  have hdescent : baseEnd_388245 < baseStart_388245 := by decide
  rcases family_descends (prefixWord ++ tailWord_388245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388248 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_388248 : Nat := 118140960795 + 388248 * 2 ^ 59
def prefixEnd_388248 : Nat := 4983230072969 + 3 ^ 40 * 388248 * 2
def baseEnd_388248 : Nat := 177206966352801965879543

theorem tailTrace_388248 : CollatzResearch.WordTrace tailWord_388248 prefixEnd_388248 177206966352801965879543 := by
  unfold tailWord_388248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080283948725639162250699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9440378598300852216334265 7080283948725639162250699)
  ·
    refine ⟨10620425923088458743376049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7080283948725639162250699 10620425923088458743376049)
    ·
      refine ⟨7965319442316344057532037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10620425923088458743376049 7965319442316344057532037)
      ·
        refine ⟨1493497395434314510787257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7965319442316344057532037 1493497395434314510787257)
        ·
          refine ⟨1120123046575735883090443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493497395434314510787257 1120123046575735883090443)
          ·
            refine ⟨1680184569863603824635665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120123046575735883090443 1680184569863603824635665)
            ·
              refine ⟨1260138427397702868476749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680184569863603824635665 1260138427397702868476749)
              ·
                refine ⟨472551910274138575678781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1260138427397702868476749 472551910274138575678781)
                ·
                  refine ⟨177206966352801965879543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472551910274138575678781 177206966352801965879543)
                  ·
                    rfl

theorem cell20_388248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_388248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388248 prefixEnd_388248 := by exact prefixLift 388248
  have htrace : WordTrace (prefixWord ++ tailWord_388248) baseStart_388248 baseEnd_388248 := by
    simpa [prefixWord, tailWord_388248, baseEnd_388248] using wordTrace_append hprefix tailTrace_388248
  have hstable : (prefixWord ++ tailWord_388248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388248).length < 2 ^ (prefixWord ++ tailWord_388248).sum := by decide
  have hdescent : baseEnd_388248 < baseStart_388248 := by decide
  rcases family_descends (prefixWord ++ tailWord_388248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388258 : List Nat := [3, 3, 1, 3, 2, 1, 3, 4]
def baseStart_388258 : Nat := 118140960795 + 388258 * 2 ^ 59
def prefixEnd_388258 : Nat := 4983230072969 + 3 ^ 40 * 388258 * 2
def baseEnd_388258 : Nat := 59070510208428791848723

theorem tailTrace_388258 : CollatzResearch.WordTrace tailWord_388258 prefixEnd_388258 59070510208428791848723 := by
  unfold tailWord_388258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540233156853762508091357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9440621751610033354910285 3540233156853762508091357)
  ·
    refine ⟨1327587433820160940534259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3540233156853762508091357 1327587433820160940534259)
    ·
      refine ⟨1991381150730241410801389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327587433820160940534259 1991381150730241410801389)
      ·
        refine ⟨746767931523840529050521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1991381150730241410801389 746767931523840529050521)
        ·
          refine ⟨560075948642880396787891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746767931523840529050521 560075948642880396787891)
          ·
            refine ⟨840113922964320595181837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560075948642880396787891 840113922964320595181837)
            ·
              refine ⟨315042721111620223193189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840113922964320595181837 315042721111620223193189)
              ·
                refine ⟨59070510208428791848723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315042721111620223193189 59070510208428791848723)
                ·
                  rfl

theorem cell20_388258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_388258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388258 prefixEnd_388258 := by exact prefixLift 388258
  have htrace : WordTrace (prefixWord ++ tailWord_388258) baseStart_388258 baseEnd_388258 := by
    simpa [prefixWord, tailWord_388258, baseEnd_388258] using wordTrace_append hprefix tailTrace_388258
  have hstable : (prefixWord ++ tailWord_388258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388258).length < 2 ^ (prefixWord ++ tailWord_388258).sum := by decide
  have hdescent : baseEnd_388258 < baseStart_388258 := by decide
  rcases family_descends (prefixWord ++ tailWord_388258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388278 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_388278 : Nat := 118140960795 + 388278 * 2 ^ 59
def prefixEnd_388278 : Nat := 4983230072969 + 3 ^ 40 * 388278 * 2
def baseEnd_388278 : Nat := 177220659170255194879421

theorem tailTrace_388278 : CollatzResearch.WordTrace tailWord_388278 prefixEnd_388278 177220659170255194879421 := by
  unfold tailWord_388278
  simp only [CollatzResearch.WordTrace]
  refine ⟨885103880458912090505843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9441108058228395632062325 885103880458912090505843)
  ·
    refine ⟨1327655820688368135758765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 885103880458912090505843 1327655820688368135758765)
    ·
      refine ⟨497870932758138050909537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1327655820688368135758765 497870932758138050909537)
      ·
        refine ⟨373403199568603538182153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497870932758138050909537 373403199568603538182153)
        ·
          refine ⟨280052399676452653636615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373403199568603538182153 280052399676452653636615)
          ·
            refine ⟨420078599514678980454923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280052399676452653636615 420078599514678980454923)
            ·
              refine ⟨630117899272018470682385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420078599514678980454923 630117899272018470682385)
              ·
                refine ⟨472588424454013853011789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630117899272018470682385 472588424454013853011789)
                ·
                  refine ⟨177220659170255194879421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472588424454013853011789 177220659170255194879421)
                  ·
                    rfl

theorem cell20_388278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_388278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388278 prefixEnd_388278 := by exact prefixLift 388278
  have htrace : WordTrace (prefixWord ++ tailWord_388278) baseStart_388278 baseEnd_388278 := by
    simpa [prefixWord, tailWord_388278, baseEnd_388278] using wordTrace_append hprefix tailTrace_388278
  have hstable : (prefixWord ++ tailWord_388278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388278).length < 2 ^ (prefixWord ++ tailWord_388278).sum := by decide
  have hdescent : baseEnd_388278 < baseStart_388278 := by decide
  rcases family_descends (prefixWord ++ tailWord_388278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388286 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_388286 : Nat := 118140960795 + 388286 * 2 ^ 59
def prefixEnd_388286 : Nat := 4983230072969 + 3 ^ 40 * 388286 * 2
def baseEnd_388286 : Nat := 177224310588242722612721

theorem tailTrace_388286 : CollatzResearch.WordTrace tailWord_388286 prefixEnd_388286 177224310588242722612721 := by
  unfold tailWord_388286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770244233914201351798089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9441302580875740542923141 1770244233914201351798089)
  ·
    refine ⟨1327683175435651013848567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1770244233914201351798089 1327683175435651013848567)
    ·
      refine ⟨1991524763153476520772851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327683175435651013848567 1991524763153476520772851)
      ·
        refine ⟨2987287144730214781159277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991524763153476520772851 2987287144730214781159277)
        ·
          refine ⟨1120232679273830542934729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2987287144730214781159277 1120232679273830542934729)
          ·
            refine ⟨840174509455372907201047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120232679273830542934729 840174509455372907201047)
            ·
              refine ⟨1260261764183059360801571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840174509455372907201047 1260261764183059360801571)
              ·
                refine ⟨1890392646274589041202357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260261764183059360801571 1890392646274589041202357)
                ·
                  refine ⟨177224310588242722612721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1890392646274589041202357 177224310588242722612721)
                  ·
                    rfl

theorem cell20_388286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_388286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388286 prefixEnd_388286 := by exact prefixLift 388286
  have htrace : WordTrace (prefixWord ++ tailWord_388286) baseStart_388286 baseEnd_388286 := by
    simpa [prefixWord, tailWord_388286, baseEnd_388286] using wordTrace_append hprefix tailTrace_388286
  have hstable : (prefixWord ++ tailWord_388286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388286).length < 2 ^ (prefixWord ++ tailWord_388286).sum := by decide
  have hdescent : baseEnd_388286 < baseStart_388286 := by decide
  rcases family_descends (prefixWord ++ tailWord_388286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388289 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 2]
def baseStart_388289 : Nat := 118140960795 + 388289 * 2 ^ 59
def prefixEnd_388289 : Nat := 4983230072969 + 3 ^ 40 * 388289 * 2
def baseEnd_388289 : Nat := 177225679869988045512709

theorem tailTrace_388289 : CollatzResearch.WordTrace tailWord_388289 prefixEnd_388289 177225679869988045512709 := by
  unfold tailWord_388289
  simp only [CollatzResearch.WordTrace]
  refine ⟨14162063290302742326743921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9441375526868494884495947 14162063290302742326743921)
  ·
    refine ⟨10621547467727056745057941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14162063290302742326743921 10621547467727056745057941)
    ·
      refine ⟨497885037549705784924591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10621547467727056745057941 497885037549705784924591)
      ·
        refine ⟨746827556324558677386887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497885037549705784924591 746827556324558677386887)
        ·
          refine ⟨1120241334486838016080331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746827556324558677386887 1120241334486838016080331)
          ·
            refine ⟨1680362001730257024120497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120241334486838016080331 1680362001730257024120497)
            ·
              refine ⟨1260271501297692768090373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680362001730257024120497 1260271501297692768090373)
              ·
                refine ⟨236300906493317394016945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1260271501297692768090373 236300906493317394016945)
                ·
                  refine ⟨177225679869988045512709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236300906493317394016945 177225679869988045512709)
                  ·
                    rfl

theorem cell20_388289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_388289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388289 prefixEnd_388289 := by exact prefixLift 388289
  have htrace : WordTrace (prefixWord ++ tailWord_388289) baseStart_388289 baseEnd_388289 := by
    simpa [prefixWord, tailWord_388289, baseEnd_388289] using wordTrace_append hprefix tailTrace_388289
  have hstable : (prefixWord ++ tailWord_388289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388289).length < 2 ^ (prefixWord ++ tailWord_388289).sum := by decide
  have hdescent : baseEnd_388289 < baseStart_388289 := by decide
  rcases family_descends (prefixWord ++ tailWord_388289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388317 : List Nat := [1, 4, 3, 2, 2, 1, 1, 6]
def baseStart_388317 : Nat := 118140960795 + 388317 * 2 ^ 59
def prefixEnd_388317 : Nat := 4983230072969 + 3 ^ 40 * 388317 * 2
def baseEnd_388317 : Nat := 59079486610981464193087

theorem tailTrace_388317 : CollatzResearch.WordTrace tailWord_388317 prefixEnd_388317 59079486610981464193087 := by
  unfold tailWord_388317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163084534201303108763205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9442056356134202072508803 14163084534201303108763205)
  ·
    refine ⟨2655578350162744332893101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14163084534201303108763205 2655578350162744332893101)
    ·
      refine ⟨995841881311029124834913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2655578350162744332893101 995841881311029124834913)
      ·
        refine ⟨746881410983271843626185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995841881311029124834913 746881410983271843626185)
        ·
          refine ⟨560161058237453882719639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746881410983271843626185 560161058237453882719639)
          ·
            refine ⟨840241587356180824079459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560161058237453882719639 840241587356180824079459)
            ·
              refine ⟨1260362381034271236119189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840241587356180824079459 1260362381034271236119189)
              ·
                refine ⟨59079486610981464193087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1260362381034271236119189 59079486610981464193087)
                ·
                  rfl

theorem cell20_388317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_388317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388317 prefixEnd_388317 := by exact prefixLift 388317
  have htrace : WordTrace (prefixWord ++ tailWord_388317) baseStart_388317 baseEnd_388317 := by
    simpa [prefixWord, tailWord_388317, baseEnd_388317] using wordTrace_append hprefix tailTrace_388317
  have hstable : (prefixWord ++ tailWord_388317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388317).length < 2 ^ (prefixWord ++ tailWord_388317).sum := by decide
  have hdescent : baseEnd_388317 < baseStart_388317 := by decide
  rcases family_descends (prefixWord ++ tailWord_388317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388340 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 2]
def baseStart_388340 : Nat := 118140960795 + 388340 * 2 ^ 59
def prefixEnd_388340 : Nat := 4983230072969 + 3 ^ 40 * 388340 * 2
def baseEnd_388340 : Nat := 177248957659658534812501

theorem tailTrace_388340 : CollatzResearch.WordTrace tailWord_388340 prefixEnd_388340 177248957659658534812501 := by
  unfold tailWord_388340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081961706558989018425237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9442615608745318691233649 7081961706558989018425237)
  ·
    refine ⟨331966954994952610238683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7081961706558989018425237 331966954994952610238683)
    ·
      refine ⟨497950432492428915358025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331966954994952610238683 497950432492428915358025)
      ·
        refine ⟨373462824369321686518519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497950432492428915358025 373462824369321686518519)
        ·
          refine ⟨560194236553982529777779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373462824369321686518519 560194236553982529777779)
          ·
            refine ⟨840291354830973794666669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560194236553982529777779 840291354830973794666669)
            ·
              refine ⟨315109258061615173000001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840291354830973794666669 315109258061615173000001)
              ·
                refine ⟨236331943546211379750001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315109258061615173000001 236331943546211379750001)
                ·
                  refine ⟨177248957659658534812501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236331943546211379750001 177248957659658534812501)
                  ·
                    rfl

theorem cell20_388340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_388340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388340 prefixEnd_388340 := by exact prefixLift 388340
  have htrace : WordTrace (prefixWord ++ tailWord_388340) baseStart_388340 baseEnd_388340 := by
    simpa [prefixWord, tailWord_388340, baseEnd_388340] using wordTrace_append hprefix tailTrace_388340
  have hstable : (prefixWord ++ tailWord_388340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388340).length < 2 ^ (prefixWord ++ tailWord_388340).sum := by decide
  have hdescent : baseEnd_388340 < baseStart_388340 := by decide
  rcases family_descends (prefixWord ++ tailWord_388340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388345 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_388345 : Nat := 118140960795 + 388345 * 2 ^ 59
def prefixEnd_388345 : Nat := 4983230072969 + 3 ^ 40 * 388345 * 2
def baseEnd_388345 : Nat := 177251239795900739645813

theorem tailTrace_388345 : CollatzResearch.WordTrace tailWord_388345 prefixEnd_388345 177251239795900739645813 := by
  unfold tailWord_388345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164105778099863890782489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9442737185399909260521659 14164105778099863890782489)
  ·
    refine ⟨10623079333574897918086867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14164105778099863890782489 10623079333574897918086867)
    ·
      refine ⟨15934619000362346877130301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623079333574897918086867 15934619000362346877130301)
      ·
        refine ⟨5975482125135880078923863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15934619000362346877130301 5975482125135880078923863)
        ·
          refine ⟨8963223187703820118385795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975482125135880078923863 8963223187703820118385795)
          ·
            refine ⟨13444834781555730177578693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8963223187703820118385795 13444834781555730177578693)
            ·
              refine ⟨2520906521541699408296005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13444834781555730177578693 2520906521541699408296005)
              ·
                refine ⟨472669972789068639055501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2520906521541699408296005 472669972789068639055501)
                ·
                  refine ⟨177251239795900739645813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472669972789068639055501 177251239795900739645813)
                  ·
                    rfl

theorem cell20_388345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_388345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388345 prefixEnd_388345 := by exact prefixLift 388345
  have htrace : WordTrace (prefixWord ++ tailWord_388345) baseStart_388345 baseEnd_388345 := by
    simpa [prefixWord, tailWord_388345, baseEnd_388345] using wordTrace_append hprefix tailTrace_388345
  have hstable : (prefixWord ++ tailWord_388345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388345).length < 2 ^ (prefixWord ++ tailWord_388345).sum := by decide
  have hdescent : baseEnd_388345 < baseStart_388345 := by decide
  rcases family_descends (prefixWord ++ tailWord_388345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388348 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_388348 : Nat := 118140960795 + 388348 * 2 ^ 59
def prefixEnd_388348 : Nat := 4983230072969 + 3 ^ 40 * 388348 * 2
def baseEnd_388348 : Nat := 177252609077646062545801

theorem tailTrace_388348 : CollatzResearch.WordTrace tailWord_388348 prefixEnd_388348 177252609077646062545801 := by
  unfold tailWord_388348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082107598544497701570849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9442810131392663602094465 7082107598544497701570849)
  ·
    refine ⟨5311580698908373276178137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7082107598544497701570849 5311580698908373276178137)
    ·
      refine ⟨3983685524181279957133603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5311580698908373276178137 3983685524181279957133603)
      ·
        refine ⟨5975528286271919935700405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983685524181279957133603 5975528286271919935700405)
        ·
          refine ⟨560205776837992493971913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5975528286271919935700405 560205776837992493971913)
          ·
            refine ⟨420154332628494370478935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560205776837992493971913 420154332628494370478935)
            ·
              refine ⟨630231498942741555718403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420154332628494370478935 630231498942741555718403)
              ·
                refine ⟨945347248414112333577605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630231498942741555718403 945347248414112333577605)
                ·
                  refine ⟨177252609077646062545801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 945347248414112333577605 177252609077646062545801)
                  ·
                    rfl

theorem cell20_388348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_388348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388348 prefixEnd_388348 := by exact prefixLift 388348
  have htrace : WordTrace (prefixWord ++ tailWord_388348) baseStart_388348 baseEnd_388348 := by
    simpa [prefixWord, tailWord_388348, baseEnd_388348] using wordTrace_append hprefix tailTrace_388348
  have hstable : (prefixWord ++ tailWord_388348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388348).length < 2 ^ (prefixWord ++ tailWord_388348).sum := by decide
  have hdescent : baseEnd_388348 < baseStart_388348 := by decide
  rcases family_descends (prefixWord ++ tailWord_388348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388403 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 2]
def baseStart_388403 : Nat := 118140960795 + 388403 * 2 ^ 59
def prefixEnd_388403 : Nat := 4983230072969 + 3 ^ 40 * 388403 * 2
def baseEnd_388403 : Nat := 177277712576310315712243

theorem tailTrace_388403 : CollatzResearch.WordTrace tailWord_388403 prefixEnd_388403 177277712576310315712243 := by
  unfold tailWord_388403
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166221211889739796393863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9444147474593159864262575 14166221211889739796393863)
  ·
    refine ⟨21249331817834609694590795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14166221211889739796393863 21249331817834609694590795)
    ·
      refine ⟨31873997726751914541886193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21249331817834609694590795 31873997726751914541886193)
      ·
        refine ⟨23905498295063935906414645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31873997726751914541886193 23905498295063935906414645)
        ·
          refine ⟨2241140465162243991226373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23905498295063935906414645 2241140465162243991226373)
          ·
            refine ⟨420213837217920748354945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2241140465162243991226373 420213837217920748354945)
            ·
              refine ⟨315160377913440561266209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420213837217920748354945 315160377913440561266209)
              ·
                refine ⟨236370283435080420949657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315160377913440561266209 236370283435080420949657)
                ·
                  refine ⟨177277712576310315712243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236370283435080420949657 177277712576310315712243)
                  ·
                    rfl

theorem cell20_388403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 2].length) (baseStart_388403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388403 prefixEnd_388403 := by exact prefixLift 388403
  have htrace : WordTrace (prefixWord ++ tailWord_388403) baseStart_388403 baseEnd_388403 := by
    simpa [prefixWord, tailWord_388403, baseEnd_388403] using wordTrace_append hprefix tailTrace_388403
  have hstable : (prefixWord ++ tailWord_388403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388403).length < 2 ^ (prefixWord ++ tailWord_388403).sum := by decide
  have hdescent : baseEnd_388403 < baseStart_388403 := by decide
  rcases family_descends (prefixWord ++ tailWord_388403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388428 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_388428 : Nat := 118140960795 + 388428 * 2 ^ 59
def prefixEnd_388428 : Nat := 4983230072969 + 3 ^ 40 * 388428 * 2
def baseEnd_388428 : Nat := 177289123257521339878807

theorem tailTrace_388428 : CollatzResearch.WordTrace tailWord_388428 prefixEnd_388428 177289123257521339878807 := by
  unfold tailWord_388428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083566518399584533026969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9444755357866112710702625 7083566518399584533026969)
  ·
    refine ⟨5312674888799688399770227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7083566518399584533026969 5312674888799688399770227)
    ·
      refine ⟨7969012333199532599655341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5312674888799688399770227 7969012333199532599655341)
      ·
        refine ⟨2988379624949824724870753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7969012333199532599655341 2988379624949824724870753)
        ·
          refine ⟨2241284718712368543653065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988379624949824724870753 2241284718712368543653065)
          ·
            refine ⟨1680963539034276407739799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241284718712368543653065 1680963539034276407739799)
            ·
              refine ⟨2521445308551414611609699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680963539034276407739799 2521445308551414611609699)
              ·
                refine ⟨3782167962827121917414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521445308551414611609699 3782167962827121917414549)
                ·
                  refine ⟨177289123257521339878807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3782167962827121917414549 177289123257521339878807)
                  ·
                    rfl

theorem cell20_388428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_388428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388428 prefixEnd_388428 := by exact prefixLift 388428
  have htrace : WordTrace (prefixWord ++ tailWord_388428) baseStart_388428 baseEnd_388428 := by
    simpa [prefixWord, tailWord_388428, baseEnd_388428] using wordTrace_append hprefix tailTrace_388428
  have hstable : (prefixWord ++ tailWord_388428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388428).length < 2 ^ (prefixWord ++ tailWord_388428).sum := by decide
  have hdescent : baseEnd_388428 < baseStart_388428 := by decide
  rcases family_descends (prefixWord ++ tailWord_388428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388455 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 3]
def baseStart_388455 : Nat := 118140960795 + 388455 * 2 ^ 59
def prefixEnd_388455 : Nat := 4983230072969 + 3 ^ 40 * 388455 * 2
def baseEnd_388455 : Nat := 177301446793229245978697

theorem tailTrace_388455 : CollatzResearch.WordTrace tailWord_388455 prefixEnd_388455 177301446793229245978697 := by
  unfold tailWord_388455
  simp only [CollatzResearch.WordTrace]
  refine ⟨14168117807701352677286819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9445411871800901784857879 14168117807701352677286819)
  ·
    refine ⟨21252176711552029015930229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14168117807701352677286819 21252176711552029015930229)
    ·
      refine ⟨1992391566708002720243459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21252176711552029015930229 1992391566708002720243459)
      ·
        refine ⟨2988587350062004080365189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992391566708002720243459 2988587350062004080365189)
        ·
          refine ⟨560360128136625765068473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2988587350062004080365189 560360128136625765068473)
          ·
            refine ⟨420270096102469323801355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560360128136625765068473 420270096102469323801355)
            ·
              refine ⟨630405144153703985702033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420270096102469323801355 630405144153703985702033)
              ·
                refine ⟨472803858115277989276525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630405144153703985702033 472803858115277989276525)
                ·
                  refine ⟨177301446793229245978697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472803858115277989276525 177301446793229245978697)
                  ·
                    rfl

theorem cell20_388455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_388455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388455 prefixEnd_388455 := by exact prefixLift 388455
  have htrace : WordTrace (prefixWord ++ tailWord_388455) baseStart_388455 baseEnd_388455 := by
    simpa [prefixWord, tailWord_388455, baseEnd_388455] using wordTrace_append hprefix tailTrace_388455
  have hstable : (prefixWord ++ tailWord_388455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388455).length < 2 ^ (prefixWord ++ tailWord_388455).sum := by decide
  have hdescent : baseEnd_388455 < baseStart_388455 := by decide
  rcases family_descends (prefixWord ++ tailWord_388455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388476 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_388476 : Nat := 118140960795 + 388476 * 2 ^ 59
def prefixEnd_388476 : Nat := 4983230072969 + 3 ^ 40 * 388476 * 2
def baseEnd_388476 : Nat := 177311031765446506278611

theorem tailTrace_388476 : CollatzResearch.WordTrace tailWord_388476 prefixEnd_388476 177311031765446506278611 := by
  unfold tailWord_388476
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084441870312636631900641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9445922493750182175867521 7084441870312636631900641)
  ·
    refine ⟨5313331402734477473925481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7084441870312636631900641 5313331402734477473925481)
    ·
      refine ⟨3984998552050858105444111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5313331402734477473925481 3984998552050858105444111)
      ·
        refine ⟨5977497828076287158166167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984998552050858105444111 5977497828076287158166167)
        ·
          refine ⟨8966246742114430737249251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977497828076287158166167 8966246742114430737249251)
          ·
            refine ⟨13449370113171646105873877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966246742114430737249251 13449370113171646105873877)
            ·
              refine ⟨315219612027460455606419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13449370113171646105873877 315219612027460455606419)
              ·
                refine ⟨472829418041190683409629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315219612027460455606419 472829418041190683409629)
                ·
                  refine ⟨177311031765446506278611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472829418041190683409629 177311031765446506278611)
                  ·
                    rfl

theorem cell20_388476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_388476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388476 prefixEnd_388476 := by exact prefixLift 388476
  have htrace : WordTrace (prefixWord ++ tailWord_388476) baseStart_388476 baseEnd_388476 := by
    simpa [prefixWord, tailWord_388476, baseEnd_388476] using wordTrace_append hprefix tailTrace_388476
  have hstable : (prefixWord ++ tailWord_388476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388476).length < 2 ^ (prefixWord ++ tailWord_388476).sum := by decide
  have hdescent : baseEnd_388476 < baseStart_388476 := by decide
  rcases family_descends (prefixWord ++ tailWord_388476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388511 : List Nat := [1, 1, 2, 5, 1, 2, 8]
def baseStart_388511 : Nat := 118140960795 + 388511 * 2 ^ 59
def prefixEnd_388511 : Nat := 4983230072969 + 3 ^ 40 * 388511 * 2
def baseEnd_388511 : Nat := 19703000746571326679089

theorem tailTrace_388511 : CollatzResearch.WordTrace tailWord_388511 prefixEnd_388511 19703000746571326679089 := by
  unfold tailWord_388511
  simp only [CollatzResearch.WordTrace]
  refine ⟨14170160295498474241325387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9446773530332316160883591 14170160295498474241325387)
  ·
    refine ⟨21255240443247711361988081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14170160295498474241325387 21255240443247711361988081)
    ·
      refine ⟨15941430332435783521491061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21255240443247711361988081 15941430332435783521491061)
      ·
        refine ⟨1494509093665854705139787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15941430332435783521491061 1494509093665854705139787)
        ·
          refine ⟨2241763640498782057709681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494509093665854705139787 2241763640498782057709681)
          ·
            refine ⟨1681322730374086543282261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241763640498782057709681 1681322730374086543282261)
            ·
              refine ⟨19703000746571326679089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1681322730374086543282261 19703000746571326679089)
              ·
                rfl

theorem cell20_388511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_388511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388511 prefixEnd_388511 := by exact prefixLift 388511
  have htrace : WordTrace (prefixWord ++ tailWord_388511) baseStart_388511 baseEnd_388511 := by
    simpa [prefixWord, tailWord_388511, baseEnd_388511] using wordTrace_append hprefix tailTrace_388511
  have hstable : (prefixWord ++ tailWord_388511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388511).length < 2 ^ (prefixWord ++ tailWord_388511).sum := by decide
  have hdescent : baseEnd_388511 < baseStart_388511 := by decide
  rcases family_descends (prefixWord ++ tailWord_388511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388535 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_388535 : Nat := 118140960795 + 388535 * 2 ^ 59
def prefixEnd_388535 : Nat := 4983230072969 + 3 ^ 40 * 388535 * 2
def baseEnd_388535 : Nat := 177337960973104523311703

theorem tailTrace_388535 : CollatzResearch.WordTrace tailWord_388535 prefixEnd_388535 177337960973104523311703 := by
  unfold tailWord_388535
  simp only [CollatzResearch.WordTrace]
  refine ⟨14171035647411526340199059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9447357098274350893466039 14171035647411526340199059)
  ·
    refine ⟨21256553471117289510298589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14171035647411526340199059 21256553471117289510298589)
    ·
      refine ⟨7971207551668983566361971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21256553471117289510298589 7971207551668983566361971)
      ·
        refine ⟨11956811327503475349542957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971207551668983566361971 11956811327503475349542957)
        ·
          refine ⟨4483804247813803256078609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11956811327503475349542957 4483804247813803256078609)
          ·
            refine ⟨3362853185860352442058957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483804247813803256078609 3362853185860352442058957)
            ·
              refine ⟨1261069944697632165772109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3362853185860352442058957 1261069944697632165772109)
              ·
                refine ⟨472901229261612062164541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261069944697632165772109 472901229261612062164541)
                ·
                  refine ⟨177337960973104523311703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472901229261612062164541 177337960973104523311703)
                  ·
                    rfl

theorem cell20_388535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_388535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388535 prefixEnd_388535 := by exact prefixLift 388535
  have htrace : WordTrace (prefixWord ++ tailWord_388535) baseStart_388535 baseEnd_388535 := by
    simpa [prefixWord, tailWord_388535, baseEnd_388535] using wordTrace_append hprefix tailTrace_388535
  have hstable : (prefixWord ++ tailWord_388535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388535).length < 2 ^ (prefixWord ++ tailWord_388535).sum := by decide
  have hdescent : baseEnd_388535 < baseStart_388535 := by decide
  rcases family_descends (prefixWord ++ tailWord_388535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388542 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_388542 : Nat := 118140960795 + 388542 * 2 ^ 59
def prefixEnd_388542 : Nat := 4983230072969 + 3 ^ 40 * 388542 * 2
def baseEnd_388542 : Nat := 177341155963843610078341

theorem tailTrace_388542 : CollatzResearch.WordTrace tailWord_388542 prefixEnd_388542 177341155963843610078341 := by
  unfold tailWord_388542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771411369798270816962985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9447527305590777690469253 1771411369798270816962985)
  ·
    refine ⟨1328558527348703112722239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1771411369798270816962985 1328558527348703112722239)
    ·
      refine ⟨1992837791023054669083359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328558527348703112722239 1992837791023054669083359)
      ·
        refine ⟨2989256686534582003625039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992837791023054669083359 2989256686534582003625039)
        ·
          refine ⟨4483885029801873005437559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989256686534582003625039 4483885029801873005437559)
          ·
            refine ⟨6725827544702809508156339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483885029801873005437559 6725827544702809508156339)
            ·
              refine ⟨10088741317054214262234509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725827544702809508156339 10088741317054214262234509)
              ·
                refine ⟨3783277993895330348337941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10088741317054214262234509 3783277993895330348337941)
                ·
                  refine ⟨177341155963843610078341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3783277993895330348337941 177341155963843610078341)
                  ·
                    rfl

theorem cell20_388542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_388542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388542 prefixEnd_388542 := by exact prefixLift 388542
  have htrace : WordTrace (prefixWord ++ tailWord_388542) baseStart_388542 baseEnd_388542 := by
    simpa [prefixWord, tailWord_388542, baseEnd_388542] using wordTrace_append hprefix tailTrace_388542
  have hstable : (prefixWord ++ tailWord_388542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388542).length < 2 ^ (prefixWord ++ tailWord_388542).sum := by decide
  have hdescent : baseEnd_388542 < baseStart_388542 := by decide
  rcases family_descends (prefixWord ++ tailWord_388542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388566 : List Nat := [5, 2, 1, 1, 1, 10]
def baseStart_388566 : Nat := 118140960795 + 388566 * 2 ^ 59
def prefixEnd_388566 : Nat := 4983230072969 + 3 ^ 40 * 388566 * 2
def baseEnd_388566 : Nat := 6568596674733562714009

theorem tailTrace_388566 : CollatzResearch.WordTrace tailWord_388566 prefixEnd_388566 6568596674733562714009 := by
  unfold tailWord_388566
  simp only [CollatzResearch.WordTrace]
  refine ⟨885760394393701164661097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9448110873532812423051701 885760394393701164661097)
  ·
    refine ⟨664320295795275873495823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 885760394393701164661097 664320295795275873495823)
    ·
      refine ⟨996480443692913810243735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664320295795275873495823 996480443692913810243735)
      ·
        refine ⟨1494720665539370715365603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996480443692913810243735 1494720665539370715365603)
        ·
          refine ⟨2242080998309056073048405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494720665539370715365603 2242080998309056073048405)
          ·
            refine ⟨6568596674733562714009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2242080998309056073048405 6568596674733562714009)
            ·
              rfl

theorem cell20_388566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 10].length) (baseStart_388566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388566 prefixEnd_388566 := by exact prefixLift 388566
  have htrace : WordTrace (prefixWord ++ tailWord_388566) baseStart_388566 baseEnd_388566 := by
    simpa [prefixWord, tailWord_388566, baseEnd_388566] using wordTrace_append hprefix tailTrace_388566
  have hstable : (prefixWord ++ tailWord_388566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388566).length < 2 ^ (prefixWord ++ tailWord_388566).sum := by decide
  have hdescent : baseEnd_388566 < baseStart_388566 := by decide
  rcases family_descends (prefixWord ++ tailWord_388566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388597 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_388597 : Nat := 118140960795 + 388597 * 2 ^ 59
def prefixEnd_388597 : Nat := 4983230072969 + 3 ^ 40 * 388597 * 2
def baseEnd_388597 : Nat := 177366259462507863244783

theorem tailTrace_388597 : CollatzResearch.WordTrace tailWord_388597 prefixEnd_388597 177366259462507863244783 := by
  unfold tailWord_388597
  simp only [CollatzResearch.WordTrace]
  refine ⟨14173296973186910928956045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9448864648791273952637363 14173296973186910928956045)
  ·
    refine ⟨5314986364945091598358517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14173296973186910928956045 5314986364945091598358517)
    ·
      refine ⟨498279971713602337346111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5314986364945091598358517 498279971713602337346111)
      ·
        refine ⟨747419957570403506019167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498279971713602337346111 747419957570403506019167)
        ·
          refine ⟨1121129936355605259028751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747419957570403506019167 1121129936355605259028751)
          ·
            refine ⟨1681694904533407888543127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121129936355605259028751 1681694904533407888543127)
            ·
              refine ⟨2522542356800111832814691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681694904533407888543127 2522542356800111832814691)
              ·
                refine ⟨3783813535200167749222037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522542356800111832814691 3783813535200167749222037)
                ·
                  refine ⟨177366259462507863244783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3783813535200167749222037 177366259462507863244783)
                  ·
                    rfl

theorem cell20_388597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_388597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388597 prefixEnd_388597 := by exact prefixLift 388597
  have htrace : WordTrace (prefixWord ++ tailWord_388597) baseStart_388597 baseEnd_388597 := by
    simpa [prefixWord, tailWord_388597, baseEnd_388597] using wordTrace_append hprefix tailTrace_388597
  have hstable : (prefixWord ++ tailWord_388597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388597).length < 2 ^ (prefixWord ++ tailWord_388597).sum := by decide
  have hdescent : baseEnd_388597 < baseStart_388597 := by decide
  rcases family_descends (prefixWord ++ tailWord_388597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388663 : List Nat := [1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_388663 : Nat := 118140960795 + 388663 * 2 ^ 59
def prefixEnd_388663 : Nat := 4983230072969 + 3 ^ 40 * 388663 * 2
def baseEnd_388663 : Nat := 59132127886968322348171

theorem tailTrace_388663 : CollatzResearch.WordTrace tailWord_388663 prefixEnd_388663 59132127886968322348171 := by
  unfold tailWord_388663
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175704190947804200858643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9450469460631869467239095 14175704190947804200858643)
  ·
    refine ⟨21263556286421706301287965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14175704190947804200858643 21263556286421706301287965)
    ·
      refine ⟨7973833607408139862982987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21263556286421706301287965 7973833607408139862982987)
      ·
        refine ⟨11960750411112209794474481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973833607408139862982987 11960750411112209794474481)
        ·
          refine ⟨8970562808334157345855861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11960750411112209794474481 8970562808334157345855861)
          ·
            refine ⟨840990263281327251173987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8970562808334157345855861 840990263281327251173987)
            ·
              refine ⟨1261485394921990876760981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840990263281327251173987 1261485394921990876760981)
              ·
                refine ⟨59132127886968322348171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1261485394921990876760981 59132127886968322348171)
                ·
                  rfl

theorem cell20_388663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_388663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388663 prefixEnd_388663 := by exact prefixLift 388663
  have htrace : WordTrace (prefixWord ++ tailWord_388663) baseStart_388663 baseEnd_388663 := by
    simpa [prefixWord, tailWord_388663, baseEnd_388663] using wordTrace_append hprefix tailTrace_388663
  have hstable : (prefixWord ++ tailWord_388663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388663).length < 2 ^ (prefixWord ++ tailWord_388663).sum := by decide
  have hdescent : baseEnd_388663 < baseStart_388663 := by decide
  rcases family_descends (prefixWord ++ tailWord_388663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388669 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 2]
def baseStart_388669 : Nat := 118140960795 + 388669 * 2 ^ 59
def prefixEnd_388669 : Nat := 4983230072969 + 3 ^ 40 * 388669 * 2
def baseEnd_388669 : Nat := 177399122224395612844489

theorem tailTrace_388669 : CollatzResearch.WordTrace tailWord_388669 prefixEnd_388669 177399122224395612844489 := by
  unfold tailWord_388669
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175923028926067225577061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9450615352617378150384707 14175923028926067225577061)
  ·
    refine ⟨2657985567923637604795699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14175923028926067225577061 2657985567923637604795699)
    ·
      refine ⟨3986978351885456407193549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2657985567923637604795699 3986978351885456407193549)
      ·
        refine ⟨1495116881957046152697581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3986978351885456407193549 1495116881957046152697581)
        ·
          refine ⟨560668830733892307261593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1495116881957046152697581 560668830733892307261593)
          ·
            refine ⟨420501623050419230446195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560668830733892307261593 420501623050419230446195)
            ·
              refine ⟨630752434575628845669293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420501623050419230446195 630752434575628845669293)
              ·
                refine ⟨236532162965860817125985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630752434575628845669293 236532162965860817125985)
                ·
                  refine ⟨177399122224395612844489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236532162965860817125985 177399122224395612844489)
                  ·
                    rfl

theorem cell20_388669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_388669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388669 prefixEnd_388669 := by exact prefixLift 388669
  have htrace : WordTrace (prefixWord ++ tailWord_388669) baseStart_388669 baseEnd_388669 := by
    simpa [prefixWord, tailWord_388669, baseEnd_388669] using wordTrace_append hprefix tailTrace_388669
  have hstable : (prefixWord ++ tailWord_388669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388669).length < 2 ^ (prefixWord ++ tailWord_388669).sum := by decide
  have hdescent : baseEnd_388669 < baseStart_388669 := by decide
  rcases family_descends (prefixWord ++ tailWord_388669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388787 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 2]
def baseStart_388787 : Nat := 118140960795 + 388787 * 2 ^ 59
def prefixEnd_388787 : Nat := 4983230072969 + 3 ^ 40 * 388787 * 2
def baseEnd_388787 : Nat := 177452980639711646910673

theorem tailTrace_388787 : CollatzResearch.WordTrace tailWord_388787 prefixEnd_388787 177452980639711646910673 := by
  unfold tailWord_388787
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180226842498573378372615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9453484561665715585581743 14180226842498573378372615)
  ·
    refine ⟨21270340263747860067558923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14180226842498573378372615 21270340263747860067558923)
    ·
      refine ⟨31905510395621790101338385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21270340263747860067558923 31905510395621790101338385)
      ·
        refine ⟨23929132796716342576003789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31905510395621790101338385 23929132796716342576003789)
        ·
          refine ⟨8973424798768628466001421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23929132796716342576003789 8973424798768628466001421)
          ·
            refine ⟨3365034299538235674750533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8973424798768628466001421 3365034299538235674750533)
            ·
              refine ⟨630943931163419189015725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3365034299538235674750533 630943931163419189015725)
              ·
                refine ⟨236603974186282195880897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630943931163419189015725 236603974186282195880897)
                ·
                  refine ⟨177452980639711646910673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236603974186282195880897 177452980639711646910673)
                  ·
                    rfl

theorem cell20_388787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 2].length) (baseStart_388787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388787 prefixEnd_388787 := by exact prefixLift 388787
  have htrace : WordTrace (prefixWord ++ tailWord_388787) baseStart_388787 baseEnd_388787 := by
    simpa [prefixWord, tailWord_388787, baseEnd_388787] using wordTrace_append hprefix tailTrace_388787
  have hstable : (prefixWord ++ tailWord_388787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388787).length < 2 ^ (prefixWord ++ tailWord_388787).sum := by decide
  have hdescent : baseEnd_388787 < baseStart_388787 := by decide
  rcases family_descends (prefixWord ++ tailWord_388787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388808 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_388808 : Nat := 118140960795 + 388808 * 2 ^ 59
def prefixEnd_388808 : Nat := 4983230072969 + 3 ^ 40 * 388808 * 2
def baseEnd_388808 : Nat := 177462565611928907210587

theorem tailTrace_388808 : CollatzResearch.WordTrace tailWord_388808 prefixEnd_388808 177462565611928907210587 := by
  unfold tailWord_388808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7090496387711246982443539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9453995183614995976591385 7090496387711246982443539)
  ·
    refine ⟨10635744581566870473665309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7090496387711246982443539 10635744581566870473665309)
    ·
      refine ⟨3988404218087576427624491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10635744581566870473665309 3988404218087576427624491)
      ·
        refine ⟨5982606327131364641436737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988404218087576427624491 5982606327131364641436737)
        ·
          refine ⟨4486954745348523481077553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5982606327131364641436737 4486954745348523481077553)
          ·
            refine ⟨3365216059011392610808165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4486954745348523481077553 3365216059011392610808165)
            ·
              refine ⟨630978011064636114526531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3365216059011392610808165 630978011064636114526531)
              ·
                refine ⟨946467016596954171789797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630978011064636114526531 946467016596954171789797)
                ·
                  refine ⟨177462565611928907210587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946467016596954171789797 177462565611928907210587)
                  ·
                    rfl

theorem cell20_388808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_388808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388808 prefixEnd_388808 := by exact prefixLift 388808
  have htrace : WordTrace (prefixWord ++ tailWord_388808) baseStart_388808 baseEnd_388808 := by
    simpa [prefixWord, tailWord_388808, baseEnd_388808] using wordTrace_append hprefix tailTrace_388808
  have hstable : (prefixWord ++ tailWord_388808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388808).length < 2 ^ (prefixWord ++ tailWord_388808).sum := by decide
  have hdescent : baseEnd_388808 < baseStart_388808 := by decide
  rcases family_descends (prefixWord ++ tailWord_388808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388828 : List Nat := [2, 2, 5, 1, 2, 2, 2, 4]
def baseStart_388828 : Nat := 118140960795 + 388828 * 2 ^ 59
def prefixEnd_388828 : Nat := 4983230072969 + 3 ^ 40 * 388828 * 2
def baseEnd_388828 : Nat := 59157231385632575514613

theorem tailTrace_388828 : CollatzResearch.WordTrace tailWord_388828 prefixEnd_388828 59157231385632575514613 := by
  unfold tailWord_388828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7090861117675018690307569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9454481490233358253743425 7090861117675018690307569)
  ·
    refine ⟨5318145838256264017730677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7090861117675018690307569 5318145838256264017730677)
    ·
      refine ⟨498576172336524751662251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5318145838256264017730677 498576172336524751662251)
      ·
        refine ⟨747864258504787127493377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498576172336524751662251 747864258504787127493377)
        ·
          refine ⟨560898193878590345620033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747864258504787127493377 560898193878590345620033)
          ·
            refine ⟨420673645408942759215025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560898193878590345620033 420673645408942759215025)
            ·
              refine ⟨315505234056707069411269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420673645408942759215025 315505234056707069411269)
              ·
                refine ⟨59157231385632575514613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315505234056707069411269 59157231385632575514613)
                ·
                  rfl

theorem cell20_388828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_388828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388828 prefixEnd_388828 := by exact prefixLift 388828
  have htrace : WordTrace (prefixWord ++ tailWord_388828) baseStart_388828 baseEnd_388828 := by
    simpa [prefixWord, tailWord_388828, baseEnd_388828] using wordTrace_append hprefix tailTrace_388828
  have hstable : (prefixWord ++ tailWord_388828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388828).length < 2 ^ (prefixWord ++ tailWord_388828).sum := by decide
  have hdescent : baseEnd_388828 < baseStart_388828 := by decide
  rcases family_descends (prefixWord ++ tailWord_388828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388860 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_388860 : Nat := 118140960795 + 388860 * 2 ^ 59
def prefixEnd_388860 : Nat := 4983230072969 + 3 ^ 40 * 388860 * 2
def baseEnd_388860 : Nat := 177486299828847837477041

theorem tailTrace_388860 : CollatzResearch.WordTrace tailWord_388860 prefixEnd_388860 177486299828847837477041 := by
  unfold tailWord_388860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091444685617053422890017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9455259580822737897186689 7091444685617053422890017)
  ·
    refine ⟨5318583514212790067167513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7091444685617053422890017 5318583514212790067167513)
    ·
      refine ⟨3988937635659592550375635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5318583514212790067167513 3988937635659592550375635)
      ·
        refine ⟨5983406453489388825563453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988937635659592550375635 5983406453489388825563453)
        ·
          refine ⟨2243777420058520809586295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5983406453489388825563453 2243777420058520809586295)
          ·
            refine ⟨3365666130087781214379443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243777420058520809586295 3365666130087781214379443)
            ·
              refine ⟨5048499195131671821569165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365666130087781214379443 5048499195131671821569165)
              ·
                refine ⟨1893187198174376933088437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5048499195131671821569165 1893187198174376933088437)
                ·
                  refine ⟨177486299828847837477041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1893187198174376933088437 177486299828847837477041)
                  ·
                    rfl

theorem cell20_388860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_388860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388860 prefixEnd_388860 := by exact prefixLift 388860
  have htrace : WordTrace (prefixWord ++ tailWord_388860) baseStart_388860 baseEnd_388860 := by
    simpa [prefixWord, tailWord_388860, baseEnd_388860] using wordTrace_append hprefix tailTrace_388860
  have hstable : (prefixWord ++ tailWord_388860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388860).length < 2 ^ (prefixWord ++ tailWord_388860).sum := by decide
  have hdescent : baseEnd_388860 < baseStart_388860 := by decide
  rcases family_descends (prefixWord ++ tailWord_388860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388946 : List Nat := [3, 2, 2, 1, 1, 4, 3, 4]
def baseStart_388946 : Nat := 118140960795 + 388946 * 2 ^ 59
def prefixEnd_388946 : Nat := 4983230072969 + 3 ^ 40 * 388946 * 2
def baseEnd_388946 : Nat := 59175184190737920203341

theorem tailTrace_388946 : CollatzResearch.WordTrace tailWord_388946 prefixEnd_388946 59175184190737920203341 := by
  unfold tailWord_388946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546506512230635883352673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9457350699281695688940461 3546506512230635883352673)
  ·
    refine ⟨2659879884172976912514505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3546506512230635883352673 2659879884172976912514505)
    ·
      refine ⟨1994909913129732684385879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2659879884172976912514505 1994909913129732684385879)
      ·
        refine ⟨2992364869694599026578819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994909913129732684385879 2992364869694599026578819)
        ·
          refine ⟨4488547304541898539868229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992364869694599026578819 4488547304541898539868229)
          ·
            refine ⟨841602619601605976225293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4488547304541898539868229 841602619601605976225293)
            ·
              refine ⟨315600982350602241084485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 841602619601605976225293 315600982350602241084485)
              ·
                refine ⟨59175184190737920203341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315600982350602241084485 59175184190737920203341)
                ·
                  rfl

theorem cell20_388946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_388946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388946 prefixEnd_388946 := by exact prefixLift 388946
  have htrace : WordTrace (prefixWord ++ tailWord_388946) baseStart_388946 baseEnd_388946 := by
    simpa [prefixWord, tailWord_388946, baseEnd_388946] using wordTrace_append hprefix tailTrace_388946
  have hstable : (prefixWord ++ tailWord_388946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388946).length < 2 ^ (prefixWord ++ tailWord_388946).sum := by decide
  have hdescent : baseEnd_388946 < baseStart_388946 := by decide
  rcases family_descends (prefixWord ++ tailWord_388946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388970 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_388970 : Nat := 118140960795 + 388970 * 2 ^ 59
def prefixEnd_388970 : Nat := 4983230072969 + 3 ^ 40 * 388970 * 2
def baseEnd_388970 : Nat := 177536506826176343809925

theorem tailTrace_388970 : CollatzResearch.WordTrace tailWord_388970 prefixEnd_388970 177536506826176343809925 := by
  unfold tailWord_388970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546725350208898908071091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9457934267223730421522909 3546725350208898908071091)
  ·
    refine ⟨5320088025313348362106637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3546725350208898908071091 5320088025313348362106637)
    ·
      refine ⟨1995033009492505635789989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5320088025313348362106637 1995033009492505635789989)
      ·
        refine ⟨374068689279844806710623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1995033009492505635789989 374068689279844806710623)
        ·
          refine ⟨561103033919767210065935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374068689279844806710623 561103033919767210065935)
          ·
            refine ⟨841654550879650815098903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561103033919767210065935 841654550879650815098903)
            ·
              refine ⟨1262481826319476222648355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841654550879650815098903 1262481826319476222648355)
              ·
                refine ⟨1893722739479214333972533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262481826319476222648355 1893722739479214333972533)
                ·
                  refine ⟨177536506826176343809925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1893722739479214333972533 177536506826176343809925)
                  ·
                    rfl

theorem cell20_388970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_388970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_388970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_388970 prefixEnd_388970 := by exact prefixLift 388970
  have htrace : WordTrace (prefixWord ++ tailWord_388970) baseStart_388970 baseEnd_388970 := by
    simpa [prefixWord, tailWord_388970, baseEnd_388970] using wordTrace_append hprefix tailTrace_388970
  have hstable : (prefixWord ++ tailWord_388970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388970).length < 2 ^ (prefixWord ++ tailWord_388970).sum := by decide
  have hdescent : baseEnd_388970 < baseStart_388970 := by decide
  rcases family_descends (prefixWord ++ tailWord_388970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389015 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 2]
def baseStart_389015 : Nat := 118140960795 + 389015 * 2 ^ 59
def prefixEnd_389015 : Nat := 4983230072969 + 3 ^ 40 * 389015 * 2
def baseEnd_389015 : Nat := 177557046052356187309741

theorem tailTrace_389015 : CollatzResearch.WordTrace tailWord_389015 prefixEnd_389015 177557046052356187309741 := by
  unfold tailWord_389015
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188542685672568317672499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9459028457115045545114999 14188542685672568317672499)
  ·
    refine ⟨21282814028508852476508749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14188542685672568317672499 21282814028508852476508749)
    ·
      refine ⟨7981055260690819678690781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21282814028508852476508749 7981055260690819678690781)
      ·
        refine ⟨2992895722759057379509043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7981055260690819678690781 2992895722759057379509043)
        ·
          refine ⟨4489343584138586069263565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992895722759057379509043 4489343584138586069263565)
          ·
            refine ⟨1683503844051969775973837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4489343584138586069263565 1683503844051969775973837)
            ·
              refine ⟨631313941519488665990189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683503844051969775973837 631313941519488665990189)
              ·
                refine ⟨236742728069808249746321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631313941519488665990189 236742728069808249746321)
                ·
                  refine ⟨177557046052356187309741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236742728069808249746321 177557046052356187309741)
                  ·
                    rfl

theorem cell20_389015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 2].length) (baseStart_389015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389015 prefixEnd_389015 := by exact prefixLift 389015
  have htrace : WordTrace (prefixWord ++ tailWord_389015) baseStart_389015 baseEnd_389015 := by
    simpa [prefixWord, tailWord_389015, baseEnd_389015] using wordTrace_append hprefix tailTrace_389015
  have hstable : (prefixWord ++ tailWord_389015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389015).length < 2 ^ (prefixWord ++ tailWord_389015).sum := by decide
  have hdescent : baseEnd_389015 < baseStart_389015 := by decide
  rcases family_descends (prefixWord ++ tailWord_389015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389038 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_389038 : Nat := 118140960795 + 389038 * 2 ^ 59
def prefixEnd_389038 : Nat := 4983230072969 + 3 ^ 40 * 389038 * 2
def baseEnd_389038 : Nat := 177567543879070329542981

theorem tailTrace_389038 : CollatzResearch.WordTrace tailWord_389038 prefixEnd_389038 177567543879070329542981 := by
  unfold tailWord_389038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773672695573655405719971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9459587709726162163839845 1773672695573655405719971)
  ·
    refine ⟨2660509043360483108579957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1773672695573655405719971 2660509043360483108579957)
    ·
      refine ⟨249422722815045291429371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2660509043360483108579957 249422722815045291429371)
      ·
        refine ⟨374134084222567937144057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249422722815045291429371 374134084222567937144057)
        ·
          refine ⟨280600563166925952858043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374134084222567937144057 280600563166925952858043)
          ·
            refine ⟨420900844750388929287065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280600563166925952858043 420900844750388929287065)
            ·
              refine ⟨315675633562791696965299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420900844750388929287065 315675633562791696965299)
              ·
                refine ⟨473513450344187545447949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315675633562791696965299 473513450344187545447949)
                ·
                  refine ⟨177567543879070329542981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473513450344187545447949 177567543879070329542981)
                  ·
                    rfl

theorem cell20_389038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_389038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389038 prefixEnd_389038 := by exact prefixLift 389038
  have htrace : WordTrace (prefixWord ++ tailWord_389038) baseStart_389038 baseEnd_389038 := by
    simpa [prefixWord, tailWord_389038, baseEnd_389038] using wordTrace_append hprefix tailTrace_389038
  have hstable : (prefixWord ++ tailWord_389038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389038).length < 2 ^ (prefixWord ++ tailWord_389038).sum := by decide
  have hdescent : baseEnd_389038 < baseStart_389038 := by decide
  rcases family_descends (prefixWord ++ tailWord_389038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389081 : List Nat := [1, 2, 1, 2, 7, 7]
def baseStart_389081 : Nat := 118140960795 + 389081 * 2 ^ 59
def prefixEnd_389081 : Nat := 4983230072969 + 3 ^ 40 * 389081 * 2
def baseEnd_389081 : Nat := 6577302601879751522573

theorem tailTrace_389081 : CollatzResearch.WordTrace tailWord_389081 prefixEnd_389081 6577302601879751522573 := by
  unfold tailWord_389081
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190949903433461589575097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9460633268955641059716731 14190949903433461589575097)
  ·
    refine ⟨10643212427575096192181323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14190949903433461589575097 10643212427575096192181323)
    ·
      refine ⟨15964818641362644288271985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643212427575096192181323 15964818641362644288271985)
      ·
        refine ⟨11973613981021983216203989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15964818641362644288271985 11973613981021983216203989)
        ·
          refine ⟨280631577680202731629781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11973613981021983216203989 280631577680202731629781)
          ·
            refine ⟨6577302601879751522573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 280631577680202731629781 6577302601879751522573)
            ·
              rfl

theorem cell20_389081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 7].length) (baseStart_389081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389081 prefixEnd_389081 := by exact prefixLift 389081
  have htrace : WordTrace (prefixWord ++ tailWord_389081) baseStart_389081 baseEnd_389081 := by
    simpa [prefixWord, tailWord_389081, baseEnd_389081] using wordTrace_append hprefix tailTrace_389081
  have hstable : (prefixWord ++ tailWord_389081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389081).length < 2 ^ (prefixWord ++ tailWord_389081).sum := by decide
  have hdescent : baseEnd_389081 < baseStart_389081 := by decide
  rcases family_descends (prefixWord ++ tailWord_389081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389091 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 2]
def baseStart_389091 : Nat := 118140960795 + 389091 * 2 ^ 59
def prefixEnd_389091 : Nat := 4983230072969 + 3 ^ 40 * 389091 * 2
def baseEnd_389091 : Nat := 177591734523237700776097

theorem tailTrace_389091 : CollatzResearch.WordTrace tailWord_389091 prefixEnd_389091 177591734523237700776097 := by
  unfold tailWord_389091
  simp only [CollatzResearch.WordTrace]
  refine ⟨14191314633397233297439127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9460876422264822198292751 14191314633397233297439127)
  ·
    refine ⟨21286971950095849946158691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14191314633397233297439127 21286971950095849946158691)
    ·
      refine ⟨31930457925143774919238037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21286971950095849946158691 31930457925143774919238037)
      ·
        refine ⟨1496740215241114449339283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31930457925143774919238037 1496740215241114449339283)
        ·
          refine ⟨2245110322861671674008925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496740215241114449339283 2245110322861671674008925)
          ·
            refine ⟨841916371073126877753347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2245110322861671674008925 841916371073126877753347)
            ·
              refine ⟨1262874556609690316630021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841916371073126877753347 1262874556609690316630021)
              ·
                refine ⟨236788979364316934368129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1262874556609690316630021 236788979364316934368129)
                ·
                  refine ⟨177591734523237700776097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236788979364316934368129 177591734523237700776097)
                  ·
                    rfl

theorem cell20_389091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 2].length) (baseStart_389091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389091 prefixEnd_389091 := by exact prefixLift 389091
  have htrace : WordTrace (prefixWord ++ tailWord_389091) baseStart_389091 baseEnd_389091 := by
    simpa [prefixWord, tailWord_389091, baseEnd_389091] using wordTrace_append hprefix tailTrace_389091
  have hstable : (prefixWord ++ tailWord_389091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389091).length < 2 ^ (prefixWord ++ tailWord_389091).sum := by decide
  have hdescent : baseEnd_389091 < baseStart_389091 := by decide
  rcases family_descends (prefixWord ++ tailWord_389091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389143 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_389143 : Nat := 118140960795 + 389143 * 2 ^ 59
def prefixEnd_389143 : Nat := 4983230072969 + 3 ^ 40 * 389143 * 2
def baseEnd_389143 : Nat := 177615468740156631042551

theorem tailTrace_389143 : CollatzResearch.WordTrace tailWord_389143 prefixEnd_389143 177615468740156631042551 := by
  unfold tailWord_389143
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193211229208846178332083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9462140819472564118888055 14193211229208846178332083)
  ·
    refine ⟨21289816843813269267498125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14193211229208846178332083 21289816843813269267498125)
    ·
      refine ⟨7983681316429975975311797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21289816843813269267498125 7983681316429975975311797)
      ·
        refine ⟨748470123415310247685481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7983681316429975975311797 748470123415310247685481)
        ·
          refine ⟨561352592561482685764111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748470123415310247685481 561352592561482685764111)
          ·
            refine ⟨842028888842224028646167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561352592561482685764111 842028888842224028646167)
            ·
              refine ⟨1263043333263336042969251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842028888842224028646167 1263043333263336042969251)
              ·
                refine ⟨1894564999895004064453877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263043333263336042969251 1894564999895004064453877)
                ·
                  refine ⟨177615468740156631042551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894564999895004064453877 177615468740156631042551)
                  ·
                    rfl

theorem cell20_389143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_389143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389143 prefixEnd_389143 := by exact prefixLift 389143
  have htrace : WordTrace (prefixWord ++ tailWord_389143) baseStart_389143 baseEnd_389143 := by
    simpa [prefixWord, tailWord_389143, baseEnd_389143] using wordTrace_append hprefix tailTrace_389143
  have hstable : (prefixWord ++ tailWord_389143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389143).length < 2 ^ (prefixWord ++ tailWord_389143).sum := by decide
  have hdescent : baseEnd_389143 < baseStart_389143 := by decide
  rcases family_descends (prefixWord ++ tailWord_389143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389171 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_389171 : Nat := 118140960795 + 389171 * 2 ^ 59
def prefixEnd_389171 : Nat := 4983230072969 + 3 ^ 40 * 389171 * 2
def baseEnd_389171 : Nat := 177628248703112978109103

theorem tailTrace_389171 : CollatzResearch.WordTrace tailWord_389171 prefixEnd_389171 177628248703112978109103 := by
  unfold tailWord_389171
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194232473107406960351367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9462821648738271306900911 14194232473107406960351367)
  ·
    refine ⟨21291348709661110440527051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14194232473107406960351367 21291348709661110440527051)
    ·
      refine ⟨31937023064491665660790577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21291348709661110440527051 31937023064491665660790577)
      ·
        refine ⟨23952767298368749245592933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31937023064491665660790577 23952767298368749245592933)
        ·
          refine ⟨4491143868444140483548675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23952767298368749245592933 4491143868444140483548675)
          ·
            refine ⟨6736715802666210725323013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491143868444140483548675 6736715802666210725323013)
            ·
              refine ⟨1263134212999914510998065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6736715802666210725323013 1263134212999914510998065)
              ·
                refine ⟨947350659749935883248549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263134212999914510998065 947350659749935883248549)
                ·
                  refine ⟨177628248703112978109103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947350659749935883248549 177628248703112978109103)
                  ·
                    rfl

theorem cell20_389171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_389171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389171 prefixEnd_389171 := by exact prefixLift 389171
  have htrace : WordTrace (prefixWord ++ tailWord_389171) baseStart_389171 baseEnd_389171 := by
    simpa [prefixWord, tailWord_389171, baseEnd_389171] using wordTrace_append hprefix tailTrace_389171
  have hstable : (prefixWord ++ tailWord_389171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389171).length < 2 ^ (prefixWord ++ tailWord_389171).sum := by decide
  have hdescent : baseEnd_389171 < baseStart_389171 := by decide
  rcases family_descends (prefixWord ++ tailWord_389171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389216 : List Nat := [2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_389216 : Nat := 118140960795 + 389216 * 2 ^ 59
def prefixEnd_389216 : Nat := 4983230072969 + 3 ^ 40 * 389216 * 2
def baseEnd_389216 : Nat := 59216262643097607202973

theorem tailTrace_389216 : CollatzResearch.WordTrace tailWord_389216 prefixEnd_389216 59216262643097607202973 := by
  unfold tailWord_389216
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097936878972189822869751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9463915838629586430493001 7097936878972189822869751)
  ·
    refine ⟨10646905318458284734304627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7097936878972189822869751 10646905318458284734304627)
    ·
      refine ⟨15970357977687427101456941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10646905318458284734304627 15970357977687427101456941)
      ·
        refine ⟨5988884241632785163046353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15970357977687427101456941 5988884241632785163046353)
        ·
          refine ⟨4491663181224588872284765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5988884241632785163046353 4491663181224588872284765)
          ·
            refine ⟨1684373692959220827106787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4491663181224588872284765 1684373692959220827106787)
            ·
              refine ⟨2526560539438831240660181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684373692959220827106787 2526560539438831240660181)
              ·
                refine ⟨59216262643097607202973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2526560539438831240660181 59216262643097607202973)
                ·
                  rfl

theorem cell20_389216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_389216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389216 prefixEnd_389216 := by exact prefixLift 389216
  have htrace : WordTrace (prefixWord ++ tailWord_389216) baseStart_389216 baseEnd_389216 := by
    simpa [prefixWord, tailWord_389216, baseEnd_389216] using wordTrace_append hprefix tailTrace_389216
  have hstable : (prefixWord ++ tailWord_389216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389216).length < 2 ^ (prefixWord ++ tailWord_389216).sum := by decide
  have hdescent : baseEnd_389216 < baseStart_389216 := by decide
  rcases family_descends (prefixWord ++ tailWord_389216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389219 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 3]
def baseStart_389219 : Nat := 118140960795 + 389219 * 2 ^ 59
def prefixEnd_389219 : Nat := 4983230072969 + 3 ^ 40 * 389219 * 2
def baseEnd_389219 : Nat := 177650157211038144508907

theorem tailTrace_389219 : CollatzResearch.WordTrace tailWord_389219 prefixEnd_389219 177650157211038144508907 := by
  unfold tailWord_389219
  simp only [CollatzResearch.WordTrace]
  refine ⟨14195983176933511158098711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9463988784622340772065807 14195983176933511158098711)
  ·
    refine ⟨21293974765400266737148067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14195983176933511158098711 21293974765400266737148067)
    ·
      refine ⟨31940962148100400105722101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293974765400266737148067 31940962148100400105722101)
      ·
        refine ⟨2994465201384412509911447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31940962148100400105722101 2994465201384412509911447)
        ·
          refine ⟨4491697802076618764867171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994465201384412509911447 4491697802076618764867171)
          ·
            refine ⟨6737546703114928147300757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491697802076618764867171 6737546703114928147300757)
            ·
              refine ⟨315822501708512256904723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6737546703114928147300757 315822501708512256904723)
              ·
                refine ⟨473733752562768385357085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315822501708512256904723 473733752562768385357085)
                ·
                  refine ⟨177650157211038144508907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473733752562768385357085 177650157211038144508907)
                  ·
                    rfl

theorem cell20_389219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_389219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389219 prefixEnd_389219 := by exact prefixLift 389219
  have htrace : WordTrace (prefixWord ++ tailWord_389219) baseStart_389219 baseEnd_389219 := by
    simpa [prefixWord, tailWord_389219, baseEnd_389219] using wordTrace_append hprefix tailTrace_389219
  have hstable : (prefixWord ++ tailWord_389219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389219).length < 2 ^ (prefixWord ++ tailWord_389219).sum := by decide
  have hdescent : baseEnd_389219 < baseStart_389219 := by decide
  rcases family_descends (prefixWord ++ tailWord_389219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389264 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 2]
def baseStart_389264 : Nat := 118140960795 + 389264 * 2 ^ 59
def prefixEnd_389264 : Nat := 4983230072969 + 3 ^ 40 * 389264 * 2
def baseEnd_389264 : Nat := 177670696437217988008723

theorem tailTrace_389264 : CollatzResearch.WordTrace tailWord_389264 prefixEnd_389264 177670696437217988008723 := by
  unfold tailWord_389264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098812230885241921743423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9465082974513655895657897 7098812230885241921743423)
  ·
    refine ⟨10648218346327862882615135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7098812230885241921743423 10648218346327862882615135)
    ·
      refine ⟨15972327519491794323922703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10648218346327862882615135 15972327519491794323922703)
      ·
        refine ⟨23958491279237691485884055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15972327519491794323922703 23958491279237691485884055)
        ·
          refine ⟨35937736918856537228826083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23958491279237691485884055 35937736918856537228826083)
          ·
            refine ⟨53906605378284805843239125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35937736918856537228826083 53906605378284805843239125)
            ·
              refine ⟨1263436063553550136950917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53906605378284805843239125 1263436063553550136950917)
              ·
                refine ⟨236894261916290650678297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1263436063553550136950917 236894261916290650678297)
                ·
                  refine ⟨177670696437217988008723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236894261916290650678297 177670696437217988008723)
                  ·
                    rfl

theorem cell20_389264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_389264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389264 prefixEnd_389264 := by exact prefixLift 389264
  have htrace : WordTrace (prefixWord ++ tailWord_389264) baseStart_389264 baseEnd_389264 := by
    simpa [prefixWord, tailWord_389264, baseEnd_389264] using wordTrace_append hprefix tailTrace_389264
  have hstable : (prefixWord ++ tailWord_389264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389264).length < 2 ^ (prefixWord ++ tailWord_389264).sum := by decide
  have hdescent : baseEnd_389264 < baseStart_389264 := by decide
  rcases family_descends (prefixWord ++ tailWord_389264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389285 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_389285 : Nat := 118140960795 + 389285 * 2 ^ 59
def prefixEnd_389285 : Nat := 4983230072969 + 3 ^ 40 * 389285 * 2
def baseEnd_389285 : Nat := 177680281409435248308637

theorem tailTrace_389285 : CollatzResearch.WordTrace tailWord_389285 prefixEnd_389285 177680281409435248308637 := by
  unfold tailWord_389285
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198390394694404430001309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9465593596462936286667539 14198390394694404430001309)
  ·
    refine ⟨5324396398010401661250491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14198390394694404430001309 5324396398010401661250491)
    ·
      refine ⟨7986594597015602491875737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5324396398010401661250491 7986594597015602491875737)
      ·
        refine ⟨5989945947761701868906803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7986594597015602491875737 5989945947761701868906803)
        ·
          refine ⟨8984918921642552803360205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989945947761701868906803 8984918921642552803360205)
          ·
            refine ⟨3369344595615957301260077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8984918921642552803360205 3369344595615957301260077)
            ·
              refine ⟨1263504223355983987972529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3369344595615957301260077 1263504223355983987972529)
              ·
                refine ⟨947628167516987990979397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263504223355983987972529 947628167516987990979397)
                ·
                  refine ⟨177680281409435248308637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947628167516987990979397 177680281409435248308637)
                  ·
                    rfl

theorem cell20_389285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_389285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389285 prefixEnd_389285 := by exact prefixLift 389285
  have htrace : WordTrace (prefixWord ++ tailWord_389285) baseStart_389285 baseEnd_389285 := by
    simpa [prefixWord, tailWord_389285, baseEnd_389285] using wordTrace_append hprefix tailTrace_389285
  have hstable : (prefixWord ++ tailWord_389285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389285).length < 2 ^ (prefixWord ++ tailWord_389285).sum := by decide
  have hdescent : baseEnd_389285 < baseStart_389285 := by decide
  rcases family_descends (prefixWord ++ tailWord_389285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389299 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_389299 : Nat := 118140960795 + 389299 * 2 ^ 59
def prefixEnd_389299 : Nat := 4983230072969 + 3 ^ 40 * 389299 * 2
def baseEnd_389299 : Nat := 177686671390913421841913

theorem tailTrace_389299 : CollatzResearch.WordTrace tailWord_389299 prefixEnd_389299 177686671390913421841913 := by
  unfold tailWord_389299
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198901016643684821010951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9465934011095789880673967 14198901016643684821010951)
  ·
    refine ⟨21298351524965527231516427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14198901016643684821010951 21298351524965527231516427)
    ·
      refine ⟨31947527287448290847274641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21298351524965527231516427 31947527287448290847274641)
      ·
        refine ⟨23960645465586218135455981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31947527287448290847274641 23960645465586218135455981)
        ·
          refine ⟨8985242049594831800795993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23960645465586218135455981 8985242049594831800795993)
          ·
            refine ⟨6738931537196123850596995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985242049594831800795993 6738931537196123850596995)
            ·
              refine ⟨10108397305794185775895493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738931537196123850596995 10108397305794185775895493)
              ·
                refine ⟨1895324494836409832980405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10108397305794185775895493 1895324494836409832980405)
                ·
                  refine ⟨177686671390913421841913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895324494836409832980405 177686671390913421841913)
                  ·
                    rfl

theorem cell20_389299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_389299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389299 prefixEnd_389299 := by exact prefixLift 389299
  have htrace : WordTrace (prefixWord ++ tailWord_389299) baseStart_389299 baseEnd_389299 := by
    simpa [prefixWord, tailWord_389299, baseEnd_389299] using wordTrace_append hprefix tailTrace_389299
  have hstable : (prefixWord ++ tailWord_389299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389299).length < 2 ^ (prefixWord ++ tailWord_389299).sum := by decide
  have hdescent : baseEnd_389299 < baseStart_389299 := by decide
  rcases family_descends (prefixWord ++ tailWord_389299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389323 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_389323 : Nat := 118140960795 + 389323 * 2 ^ 59
def prefixEnd_389323 : Nat := 4983230072969 + 3 ^ 40 * 389323 * 2
def baseEnd_389323 : Nat := 177697625644876005041815

theorem tailTrace_389323 : CollatzResearch.WordTrace tailWord_389323 prefixEnd_389323 177697625644876005041815 := by
  unfold tailWord_389323
  simp only [CollatzResearch.WordTrace]
  refine ⟨14199776368556736919884623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9466517579037824613256415 14199776368556736919884623)
  ·
    refine ⟨21299664552835105379826935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14199776368556736919884623 21299664552835105379826935)
    ·
      refine ⟨31949496829252658069740403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21299664552835105379826935 31949496829252658069740403)
      ·
        refine ⟨47924245243878987104610605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31949496829252658069740403 47924245243878987104610605)
        ·
          refine ⟨17971591966454620164228977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47924245243878987104610605 17971591966454620164228977)
          ·
            refine ⟨13478693974840965123171733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17971591966454620164228977 13478693974840965123171733)
            ·
              refine ⟨631813780070670240148675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13478693974840965123171733 631813780070670240148675)
              ·
                refine ⟨947720670106005360223013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631813780070670240148675 947720670106005360223013)
                ·
                  refine ⟨177697625644876005041815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947720670106005360223013 177697625644876005041815)
                  ·
                    rfl

theorem cell20_389323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_389323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389323 prefixEnd_389323 := by exact prefixLift 389323
  have htrace : WordTrace (prefixWord ++ tailWord_389323) baseStart_389323 baseEnd_389323 := by
    simpa [prefixWord, tailWord_389323, baseEnd_389323] using wordTrace_append hprefix tailTrace_389323
  have hstable : (prefixWord ++ tailWord_389323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389323).length < 2 ^ (prefixWord ++ tailWord_389323).sum := by decide
  have hdescent : baseEnd_389323 < baseStart_389323 := by decide
  rcases family_descends (prefixWord ++ tailWord_389323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389374 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_389374 : Nat := 118140960795 + 389374 * 2 ^ 59
def prefixEnd_389374 : Nat := 4983230072969 + 3 ^ 40 * 389374 * 2
def baseEnd_389374 : Nat := 177720903434546494341607

theorem tailTrace_389374 : CollatzResearch.WordTrace tailWord_389374 prefixEnd_389374 177720903434546494341607 := by
  unfold tailWord_389374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775204561421496578748897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9467757660914648419994117 1775204561421496578748897)
  ·
    refine ⟨1331403421066122434061673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1775204561421496578748897 1331403421066122434061673)
    ·
      refine ⟨998552565799591825546255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331403421066122434061673 998552565799591825546255)
      ·
        refine ⟨1497828848699387738319383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998552565799591825546255 1497828848699387738319383)
        ·
          refine ⟨2246743273049081607479075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497828848699387738319383 2246743273049081607479075)
          ·
            refine ⟨3370114909573622411218613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246743273049081607479075 3370114909573622411218613)
            ·
              refine ⟨315948272772527101051745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3370114909573622411218613 315948272772527101051745)
              ·
                refine ⟨236961204579395325788809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315948272772527101051745 236961204579395325788809)
                ·
                  refine ⟨177720903434546494341607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236961204579395325788809 177720903434546494341607)
                  ·
                    rfl

theorem cell20_389374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_389374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389374 prefixEnd_389374 := by exact prefixLift 389374
  have htrace : WordTrace (prefixWord ++ tailWord_389374) baseStart_389374 baseEnd_389374 := by
    simpa [prefixWord, tailWord_389374, baseEnd_389374] using wordTrace_append hprefix tailTrace_389374
  have hstable : (prefixWord ++ tailWord_389374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389374).length < 2 ^ (prefixWord ++ tailWord_389374).sum := by decide
  have hdescent : baseEnd_389374 < baseStart_389374 := by decide
  rcases family_descends (prefixWord ++ tailWord_389374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389375 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_389375 : Nat := 118140960795 + 389375 * 2 ^ 59
def prefixEnd_389375 : Nat := 4983230072969 + 3 ^ 40 * 389375 * 2
def baseEnd_389375 : Nat := 177721359861794935308269

theorem tailTrace_389375 : CollatzResearch.WordTrace tailWord_389375 prefixEnd_389375 177721359861794935308269 := by
  unfold tailWord_389375
  simp only [CollatzResearch.WordTrace]
  refine ⟨14201672964368349800777579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9467781976245566533851719 14201672964368349800777579)
  ·
    refine ⟨21302509446552524701166369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14201672964368349800777579 21302509446552524701166369)
    ·
      refine ⟨15976882084914393525874777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21302509446552524701166369 15976882084914393525874777)
      ·
        refine ⟨11982661563685795144406083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15976882084914393525874777 11982661563685795144406083)
        ·
          refine ⟨17973992345528692716609125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11982661563685795144406083 17973992345528692716609125)
          ·
            refine ⟨3370123564786629884364211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17973992345528692716609125 3370123564786629884364211)
            ·
              refine ⟨5055185347179944826546317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370123564786629884364211 5055185347179944826546317)
              ·
                refine ⟨1895694505192479309954869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5055185347179944826546317 1895694505192479309954869)
                ·
                  refine ⟨177721359861794935308269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895694505192479309954869 177721359861794935308269)
                  ·
                    rfl

theorem cell20_389375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_389375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389375 prefixEnd_389375 := by exact prefixLift 389375
  have htrace : WordTrace (prefixWord ++ tailWord_389375) baseStart_389375 baseEnd_389375 := by
    simpa [prefixWord, tailWord_389375, baseEnd_389375] using wordTrace_append hprefix tailTrace_389375
  have hstable : (prefixWord ++ tailWord_389375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389375).length < 2 ^ (prefixWord ++ tailWord_389375).sum := by decide
  have hdescent : baseEnd_389375 < baseStart_389375 := by decide
  rcases family_descends (prefixWord ++ tailWord_389375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389433 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 2]
def baseStart_389433 : Nat := 118140960795 + 389433 * 2 ^ 59
def prefixEnd_389433 : Nat := 4983230072969 + 3 ^ 40 * 389433 * 2
def baseEnd_389433 : Nat := 177747832642204511374699

theorem tailTrace_389433 : CollatzResearch.WordTrace tailWord_389433 prefixEnd_389433 177747832642204511374699 := by
  unfold tailWord_389433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203788398158225706388953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9469192265438817137592635 14203788398158225706388953)
  ·
    refine ⟨10652841298618669279791715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14203788398158225706388953 10652841298618669279791715)
    ·
      refine ⟨15979261947928003919687573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10652841298618669279791715 15979261947928003919687573)
      ·
        refine ⟨749027903809125183735355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15979261947928003919687573 749027903809125183735355)
        ·
          refine ⟨1123541855713687775603033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749027903809125183735355 1123541855713687775603033)
          ·
            refine ⟨842656391785265831702275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123541855713687775603033 842656391785265831702275)
            ·
              refine ⟨1263984587677898747553413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842656391785265831702275 1263984587677898747553413)
              ·
                refine ⟨236997110189606015166265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1263984587677898747553413 236997110189606015166265)
                ·
                  refine ⟨177747832642204511374699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236997110189606015166265 177747832642204511374699)
                  ·
                    rfl

theorem cell20_389433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_389433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389433 prefixEnd_389433 := by exact prefixLift 389433
  have htrace : WordTrace (prefixWord ++ tailWord_389433) baseStart_389433 baseEnd_389433 := by
    simpa [prefixWord, tailWord_389433, baseEnd_389433] using wordTrace_append hprefix tailTrace_389433
  have hstable : (prefixWord ++ tailWord_389433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389433).length < 2 ^ (prefixWord ++ tailWord_389433).sum := by decide
  have hdescent : baseEnd_389433 < baseStart_389433 := by decide
  rcases family_descends (prefixWord ++ tailWord_389433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389513 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_389513 : Nat := 118140960795 + 389513 * 2 ^ 59
def prefixEnd_389513 : Nat := 4983230072969 + 3 ^ 40 * 389513 * 2
def baseEnd_389513 : Nat := 177784346822079788707705

theorem tailTrace_389513 : CollatzResearch.WordTrace tailWord_389513 prefixEnd_389513 177784346822079788707705 := by
  unfold tailWord_389513
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206706237868399369301193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9471137491912266246200795 14206706237868399369301193)
  ·
    refine ⟨10655029678401299526975895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14206706237868399369301193 10655029678401299526975895)
    ·
      refine ⟨15982544517601949290463843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10655029678401299526975895 15982544517601949290463843)
      ·
        refine ⟨23973816776402923935695765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15982544517601949290463843 23973816776402923935695765)
        ·
          refine ⟨1123772661393887059485739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23973816776402923935695765 1123772661393887059485739)
          ·
            refine ⟨1685658992090830589228609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123772661393887059485739 1685658992090830589228609)
            ·
              refine ⟨1264244244068122941921457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685658992090830589228609 1264244244068122941921457)
              ·
                refine ⟨948183183051092206441093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264244244068122941921457 948183183051092206441093)
                ·
                  refine ⟨177784346822079788707705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948183183051092206441093 177784346822079788707705)
                  ·
                    rfl

theorem cell20_389513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_389513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389513 prefixEnd_389513 := by exact prefixLift 389513
  have htrace : WordTrace (prefixWord ++ tailWord_389513) baseStart_389513 baseEnd_389513 := by
    simpa [prefixWord, tailWord_389513, baseEnd_389513] using wordTrace_append hprefix tailTrace_389513
  have hstable : (prefixWord ++ tailWord_389513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389513).length < 2 ^ (prefixWord ++ tailWord_389513).sum := by decide
  have hdescent : baseEnd_389513 < baseStart_389513 := by decide
  rcases family_descends (prefixWord ++ tailWord_389513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389527 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_389527 : Nat := 118140960795 + 389527 * 2 ^ 59
def prefixEnd_389527 : Nat := 4983230072969 + 3 ^ 40 * 389527 * 2
def baseEnd_389527 : Nat := 177790736803557962240981

theorem tailTrace_389527 : CollatzResearch.WordTrace tailWord_389527 prefixEnd_389527 177790736803557962240981 := by
  unfold tailWord_389527
  simp only [CollatzResearch.WordTrace]
  refine ⟨14207216859817679760310835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9471477906545119840207223 14207216859817679760310835)
  ·
    refine ⟨21310825289726519640466253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14207216859817679760310835 21310825289726519640466253)
    ·
      refine ⟨7991559483647444865174845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21310825289726519640466253 7991559483647444865174845)
      ·
        refine ⟨2996834806367791824440567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7991559483647444865174845 2996834806367791824440567)
        ·
          refine ⟨4495252209551687736660851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996834806367791824440567 4495252209551687736660851)
          ·
            refine ⟨6742878314327531604991277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495252209551687736660851 6742878314327531604991277)
            ·
              refine ⟨2528579367872824351871729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6742878314327531604991277 2528579367872824351871729)
              ·
                refine ⟨1896434525904618263903797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528579367872824351871729 1896434525904618263903797)
                ·
                  refine ⟨177790736803557962240981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896434525904618263903797 177790736803557962240981)
                  ·
                    rfl

theorem cell20_389527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_389527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389527 prefixEnd_389527 := by exact prefixLift 389527
  have htrace : WordTrace (prefixWord ++ tailWord_389527) baseStart_389527 baseEnd_389527 := by
    simpa [prefixWord, tailWord_389527, baseEnd_389527] using wordTrace_append hprefix tailTrace_389527
  have hstable : (prefixWord ++ tailWord_389527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389527).length < 2 ^ (prefixWord ++ tailWord_389527).sum := by decide
  have hdescent : baseEnd_389527 < baseStart_389527 := by decide
  rcases family_descends (prefixWord ++ tailWord_389527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389557 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 3]
def baseStart_389557 : Nat := 118140960795 + 389557 * 2 ^ 59
def prefixEnd_389557 : Nat := 4983230072969 + 3 ^ 40 * 389557 * 2
def baseEnd_389557 : Nat := 177804429621011191240859

theorem tailTrace_389557 : CollatzResearch.WordTrace tailWord_389557 prefixEnd_389557 177804429621011191240859 := by
  unfold tailWord_389557
  simp only [CollatzResearch.WordTrace]
  refine ⟨14208311049708994883902925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9472207366472663255935283 14208311049708994883902925)
  ·
    refine ⟨5328116643640873081463597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14208311049708994883902925 5328116643640873081463597)
    ·
      refine ⟨1998043741365327405548849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5328116643640873081463597 1998043741365327405548849)
      ·
        refine ⟨1498532806023995554161637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998043741365327405548849 1498532806023995554161637)
        ·
          refine ⟨280974901129499166405307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1498532806023995554161637 280974901129499166405307)
          ·
            refine ⟨421462351694248749607961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280974901129499166405307 421462351694248749607961)
            ·
              refine ⟨316096763770686562205971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421462351694248749607961 316096763770686562205971)
              ·
                refine ⟨474145145656029843308957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316096763770686562205971 474145145656029843308957)
                ·
                  refine ⟨177804429621011191240859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474145145656029843308957 177804429621011191240859)
                  ·
                    rfl

theorem cell20_389557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_389557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389557 prefixEnd_389557 := by exact prefixLift 389557
  have htrace : WordTrace (prefixWord ++ tailWord_389557) baseStart_389557 baseEnd_389557 := by
    simpa [prefixWord, tailWord_389557, baseEnd_389557] using wordTrace_append hprefix tailTrace_389557
  have hstable : (prefixWord ++ tailWord_389557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389557).length < 2 ^ (prefixWord ++ tailWord_389557).sum := by decide
  have hdescent : baseEnd_389557 < baseStart_389557 := by decide
  rcases family_descends (prefixWord ++ tailWord_389557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389561 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 3]
def baseStart_389561 : Nat := 118140960795 + 389561 * 2 ^ 59
def prefixEnd_389561 : Nat := 4983230072969 + 3 ^ 40 * 389561 * 2
def baseEnd_389561 : Nat := 177806255330004955107509

theorem tailTrace_389561 : CollatzResearch.WordTrace tailWord_389561 prefixEnd_389561 177806255330004955107509 := by
  unfold tailWord_389561
  simp only [CollatzResearch.WordTrace]
  refine ⟨14208456941694503567048537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9472304627796335711365691 14208456941694503567048537)
  ·
    refine ⟨10656342706270877675286403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14208456941694503567048537 10656342706270877675286403)
    ·
      refine ⟨15984514059406316512929605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10656342706270877675286403 15984514059406316512929605)
      ·
        refine ⟨2997096386138684346174301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15984514059406316512929605 2997096386138684346174301)
        ·
          refine ⟨1123911144802006629815363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2997096386138684346174301 1123911144802006629815363)
          ·
            refine ⟨1685866717203009944723045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123911144802006629815363 1685866717203009944723045)
            ·
              refine ⟨316100009475564364635571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1685866717203009944723045 316100009475564364635571)
              ·
                refine ⟨474150014213346546953357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316100009475564364635571 474150014213346546953357)
                ·
                  refine ⟨177806255330004955107509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474150014213346546953357 177806255330004955107509)
                  ·
                    rfl

theorem cell20_389561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_389561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389561 prefixEnd_389561 := by exact prefixLift 389561
  have htrace : WordTrace (prefixWord ++ tailWord_389561) baseStart_389561 baseEnd_389561 := by
    simpa [prefixWord, tailWord_389561, baseEnd_389561] using wordTrace_append hprefix tailTrace_389561
  have hstable : (prefixWord ++ tailWord_389561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389561).length < 2 ^ (prefixWord ++ tailWord_389561).sum := by decide
  have hdescent : baseEnd_389561 < baseStart_389561 := by decide
  rcases family_descends (prefixWord ++ tailWord_389561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389613 : List Nat := [1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_389613 : Nat := 118140960795 + 389613 * 2 ^ 59
def prefixEnd_389613 : Nat := 4983230072969 + 3 ^ 40 * 389613 * 2
def baseEnd_389613 : Nat := 59276663182307961791321

theorem tailTrace_389613 : CollatzResearch.WordTrace tailWord_389613 prefixEnd_389613 59276663182307961791321 := by
  unfold tailWord_389613
  simp only [CollatzResearch.WordTrace]
  refine ⟨14210353537506116447941493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9473569025004077631960995 14210353537506116447941493)
  ·
    refine ⟨1332220644141198416994515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14210353537506116447941493 1332220644141198416994515)
    ·
      refine ⟨1998330966211797625491773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332220644141198416994515 1998330966211797625491773)
      ·
        refine ⟨749374112329424109559415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1998330966211797625491773 749374112329424109559415)
        ·
          refine ⟨1124061168494136164339123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749374112329424109559415 1124061168494136164339123)
          ·
            refine ⟨1686091752741204246508685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124061168494136164339123 1686091752741204246508685)
            ·
              refine ⟨632284407277951592440757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1686091752741204246508685 632284407277951592440757)
              ·
                refine ⟨59276663182307961791321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 632284407277951592440757 59276663182307961791321)
                ·
                  rfl

theorem cell20_389613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_389613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389613 prefixEnd_389613 := by exact prefixLift 389613
  have htrace : WordTrace (prefixWord ++ tailWord_389613) baseStart_389613 baseEnd_389613 := by
    simpa [prefixWord, tailWord_389613, baseEnd_389613] using wordTrace_append hprefix tailTrace_389613
  have hstable : (prefixWord ++ tailWord_389613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389613).length < 2 ^ (prefixWord ++ tailWord_389613).sum := by decide
  have hdescent : baseEnd_389613 < baseStart_389613 := by decide
  rcases family_descends (prefixWord ++ tailWord_389613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389644 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 2]
def baseStart_389644 : Nat := 118140960795 + 389644 * 2 ^ 59
def prefixEnd_389644 : Nat := 4983230072969 + 3 ^ 40 * 389644 * 2
def baseEnd_389644 : Nat := 177844138791625555340503

theorem tailTrace_389644 : CollatzResearch.WordTrace tailWord_389644 prefixEnd_389644 177844138791625555340503 := by
  unfold tailWord_389644
  simp only [CollatzResearch.WordTrace]
  refine ⟨7105742100196904371159993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9474322800262539161546657 7105742100196904371159993)
  ·
    refine ⟨5329306575147678278369995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7105742100196904371159993 5329306575147678278369995)
    ·
      refine ⟨7993959862721517417554993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329306575147678278369995 7993959862721517417554993)
      ·
        refine ⟨5995469897041138063166245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7993959862721517417554993 5995469897041138063166245)
        ·
          refine ⟨1124150605695213386843671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5995469897041138063166245 1124150605695213386843671)
          ·
            refine ⟨1686225908542820080265507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124150605695213386843671 1686225908542820080265507)
            ·
              refine ⟨2529338862814230120398261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686225908542820080265507 2529338862814230120398261)
              ·
                refine ⟨237125518388834073787337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2529338862814230120398261 237125518388834073787337)
                ·
                  refine ⟨177844138791625555340503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237125518388834073787337 177844138791625555340503)
                  ·
                    rfl

theorem cell20_389644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_389644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389644 prefixEnd_389644 := by exact prefixLift 389644
  have htrace : WordTrace (prefixWord ++ tailWord_389644) baseStart_389644 baseEnd_389644 := by
    simpa [prefixWord, tailWord_389644, baseEnd_389644] using wordTrace_append hprefix tailTrace_389644
  have hstable : (prefixWord ++ tailWord_389644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389644).length < 2 ^ (prefixWord ++ tailWord_389644).sum := by decide
  have hdescent : baseEnd_389644 < baseStart_389644 := by decide
  rcases family_descends (prefixWord ++ tailWord_389644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389658 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_389658 : Nat := 118140960795 + 389658 * 2 ^ 59
def prefixEnd_389658 : Nat := 4983230072969 + 3 ^ 40 * 389658 * 2
def baseEnd_389658 : Nat := 177850528773103728873779

theorem tailTrace_389658 : CollatzResearch.WordTrace tailWord_389658 prefixEnd_389658 177850528773103728873779 := by
  unfold tailWord_389658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552998705585772283332407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9474663214895392755553085 3552998705585772283332407)
  ·
    refine ⟨5329498058378658424998611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552998705585772283332407 5329498058378658424998611)
    ·
      refine ⟨7994247087567987637497917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329498058378658424998611 7994247087567987637497917)
      ·
        refine ⟨2997842657837995364061719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7994247087567987637497917 2997842657837995364061719)
        ·
          refine ⟨4496763986756993046092579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997842657837995364061719 4496763986756993046092579)
          ·
            refine ⟨6745145980135489569138869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496763986756993046092579 6745145980135489569138869)
            ·
              refine ⟨632357435637702147106769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6745145980135489569138869 632357435637702147106769)
              ·
                refine ⟨474268076728276610330077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632357435637702147106769 474268076728276610330077)
                ·
                  refine ⟨177850528773103728873779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474268076728276610330077 177850528773103728873779)
                  ·
                    rfl

theorem cell20_389658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_389658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389658 prefixEnd_389658 := by exact prefixLift 389658
  have htrace : WordTrace (prefixWord ++ tailWord_389658) baseStart_389658 baseEnd_389658 := by
    simpa [prefixWord, tailWord_389658, baseEnd_389658] using wordTrace_append hprefix tailTrace_389658
  have hstable : (prefixWord ++ tailWord_389658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389658).length < 2 ^ (prefixWord ++ tailWord_389658).sum := by decide
  have hdescent : baseEnd_389658 < baseStart_389658 := by decide
  rcases family_descends (prefixWord ++ tailWord_389658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389665 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_389665 : Nat := 118140960795 + 389665 * 2 ^ 59
def prefixEnd_389665 : Nat := 4983230072969 + 3 ^ 40 * 389665 * 2
def baseEnd_389665 : Nat := 177853723763842815640417

theorem tailTrace_389665 : CollatzResearch.WordTrace tailWord_389665 prefixEnd_389665 177853723763842815640417 := by
  unfold tailWord_389665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212250133317729328834449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9474833422211819552556299 14212250133317729328834449)
  ·
    refine ⟨10659187599988296996625837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14212250133317729328834449 10659187599988296996625837)
    ·
      refine ⟨3997195349995611373734689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10659187599988296996625837 3997195349995611373734689)
      ·
        refine ⟨2997896512496708530301017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3997195349995611373734689 2997896512496708530301017)
        ·
          refine ⟨2248422384372531397725763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997896512496708530301017 2248422384372531397725763)
          ·
            refine ⟨3372633576558797096588645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248422384372531397725763 3372633576558797096588645)
            ·
              refine ⟨632368795604774455610371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3372633576558797096588645 632368795604774455610371)
              ·
                refine ⟨948553193407161683415557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632368795604774455610371 948553193407161683415557)
                ·
                  refine ⟨177853723763842815640417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948553193407161683415557 177853723763842815640417)
                  ·
                    rfl

theorem cell20_389665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_389665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389665 prefixEnd_389665 := by exact prefixLift 389665
  have htrace : WordTrace (prefixWord ++ tailWord_389665) baseStart_389665 baseEnd_389665 := by
    simpa [prefixWord, tailWord_389665, baseEnd_389665] using wordTrace_append hprefix tailTrace_389665
  have hstable : (prefixWord ++ tailWord_389665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389665).length < 2 ^ (prefixWord ++ tailWord_389665).sum := by decide
  have hdescent : baseEnd_389665 < baseStart_389665 := by decide
  rcases family_descends (prefixWord ++ tailWord_389665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389671 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 3]
def baseStart_389671 : Nat := 118140960795 + 389671 * 2 ^ 59
def prefixEnd_389671 : Nat := 4983230072969 + 3 ^ 40 * 389671 * 2
def baseEnd_389671 : Nat := 177856462327333461440393

theorem tailTrace_389671 : CollatzResearch.WordTrace tailWord_389671 prefixEnd_389671 177856462327333461440393 := by
  unfold tailWord_389671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212468971295992353552867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9474979314197328235701911 14212468971295992353552867)
  ·
    refine ⟨21318703456943988530329301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14212468971295992353552867 21318703456943988530329301)
    ·
      refine ⟨499657112272124731179593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21318703456943988530329301 499657112272124731179593)
      ·
        refine ⟨374742834204093548384695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499657112272124731179593 374742834204093548384695)
        ·
          refine ⟨562114251306140322577043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374742834204093548384695 562114251306140322577043)
          ·
            refine ⟨843171376959210483865565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562114251306140322577043 843171376959210483865565)
            ·
              refine ⟨316189266359703931449587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843171376959210483865565 316189266359703931449587)
              ·
                refine ⟨474283899539555897174381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316189266359703931449587 474283899539555897174381)
                ·
                  refine ⟨177856462327333461440393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474283899539555897174381 177856462327333461440393)
                  ·
                    rfl

theorem cell20_389671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_389671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389671 prefixEnd_389671 := by exact prefixLift 389671
  have htrace : WordTrace (prefixWord ++ tailWord_389671) baseStart_389671 baseEnd_389671 := by
    simpa [prefixWord, tailWord_389671, baseEnd_389671] using wordTrace_append hprefix tailTrace_389671
  have hstable : (prefixWord ++ tailWord_389671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389671).length < 2 ^ (prefixWord ++ tailWord_389671).sum := by decide
  have hdescent : baseEnd_389671 < baseStart_389671 := by decide
  rcases family_descends (prefixWord ++ tailWord_389671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389717 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_389717 : Nat := 118140960795 + 389717 * 2 ^ 59
def prefixEnd_389717 : Nat := 4983230072969 + 3 ^ 40 * 389717 * 2
def baseEnd_389717 : Nat := 177877457980761745906871

theorem tailTrace_389717 : CollatzResearch.WordTrace tailWord_389717 prefixEnd_389717 177877457980761745906871 := by
  unfold tailWord_389717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214146729129342209727405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9476097819419561473151603 14214146729129342209727405)
  ·
    refine ⟨5330305023423503328647777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14214146729129342209727405 5330305023423503328647777)
    ·
      refine ⟨3997728767567627496485833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5330305023423503328647777 3997728767567627496485833)
      ·
        refine ⟨2998296575675720622364375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3997728767567627496485833 2998296575675720622364375)
        ·
          refine ⟨4497444863513580933546563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998296575675720622364375 4497444863513580933546563)
          ·
            refine ⟨6746167295270371400319845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497444863513580933546563 6746167295270371400319845)
            ·
              refine ⟨1264906367863194637559971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6746167295270371400319845 1264906367863194637559971)
              ·
                refine ⟨1897359551794791956339957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264906367863194637559971 1897359551794791956339957)
                ·
                  refine ⟨177877457980761745906871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1897359551794791956339957 177877457980761745906871)
                  ·
                    rfl

theorem cell20_389717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_389717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389717 prefixEnd_389717 := by exact prefixLift 389717
  have htrace : WordTrace (prefixWord ++ tailWord_389717) baseStart_389717 baseEnd_389717 := by
    simpa [prefixWord, tailWord_389717, baseEnd_389717] using wordTrace_append hprefix tailTrace_389717
  have hstable : (prefixWord ++ tailWord_389717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389717).length < 2 ^ (prefixWord ++ tailWord_389717).sum := by decide
  have hdescent : baseEnd_389717 < baseStart_389717 := by decide
  rcases family_descends (prefixWord ++ tailWord_389717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389730 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_389730 : Nat := 118140960795 + 389730 * 2 ^ 59
def prefixEnd_389730 : Nat := 4983230072969 + 3 ^ 40 * 389730 * 2
def baseEnd_389730 : Nat := 177883391534991478473485

theorem tailTrace_389730 : CollatzResearch.WordTrace tailWord_389730 prefixEnd_389730 177883391534991478473485 := by
  unfold tailWord_389730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553655219520561357487661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9476413918721496953300429 3553655219520561357487661)
  ·
    refine ⟨1332620707320210509057873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3553655219520561357487661 1332620707320210509057873)
    ·
      refine ⟨999465530490157881793405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1332620707320210509057873 999465530490157881793405)
      ·
        refine ⟨374799573933809205672527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 999465530490157881793405 374799573933809205672527)
        ·
          refine ⟨562199360900713808508791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374799573933809205672527 562199360900713808508791)
          ·
            refine ⟨843299041351070712763187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562199360900713808508791 843299041351070712763187)
            ·
              refine ⟨1264948562026606069144781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843299041351070712763187 1264948562026606069144781)
              ·
                refine ⟨474355710759977275929293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1264948562026606069144781 474355710759977275929293)
                ·
                  refine ⟨177883391534991478473485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474355710759977275929293 177883391534991478473485)
                  ·
                    rfl

theorem cell20_389730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_389730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389730 prefixEnd_389730 := by exact prefixLift 389730
  have htrace : WordTrace (prefixWord ++ tailWord_389730) baseStart_389730 baseEnd_389730 := by
    simpa [prefixWord, tailWord_389730, baseEnd_389730] using wordTrace_append hprefix tailTrace_389730
  have hstable : (prefixWord ++ tailWord_389730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389730).length < 2 ^ (prefixWord ++ tailWord_389730).sum := by decide
  have hdescent : baseEnd_389730 < baseStart_389730 := by decide
  rcases family_descends (prefixWord ++ tailWord_389730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389779 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 2]
def baseStart_389779 : Nat := 118140960795 + 389779 * 2 ^ 59
def prefixEnd_389779 : Nat := 4983230072969 + 3 ^ 40 * 389779 * 2
def baseEnd_389779 : Nat := 177905756470165085839951

theorem tailTrace_389779 : CollatzResearch.WordTrace tailWord_389779 prefixEnd_389779 177905756470165085839951 := by
  unfold tailWord_389779
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216408054904726798484391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9477605369936484532322927 14216408054904726798484391)
  ·
    refine ⟨21324612082357090197726587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14216408054904726798484391 21324612082357090197726587)
    ·
      refine ⟨31986918123535635296589881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21324612082357090197726587 31986918123535635296589881)
      ·
        refine ⟨23990188592651726472442411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31986918123535635296589881 23990188592651726472442411)
        ·
          refine ⟨35985282888977589708663617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23990188592651726472442411 35985282888977589708663617)
          ·
            refine ⟨26988962166733192281497713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35985282888977589708663617 26988962166733192281497713)
            ·
              refine ⟨20241721625049894211123285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26988962166733192281497713 20241721625049894211123285)
              ·
                refine ⟨237207675293553447786601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20241721625049894211123285 237207675293553447786601)
                ·
                  refine ⟨177905756470165085839951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237207675293553447786601 177905756470165085839951)
                  ·
                    rfl

theorem cell20_389779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 2].length) (baseStart_389779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389779 prefixEnd_389779 := by exact prefixLift 389779
  have htrace : WordTrace (prefixWord ++ tailWord_389779) baseStart_389779 baseEnd_389779 := by
    simpa [prefixWord, tailWord_389779, baseEnd_389779] using wordTrace_append hprefix tailTrace_389779
  have hstable : (prefixWord ++ tailWord_389779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389779).length < 2 ^ (prefixWord ++ tailWord_389779).sum := by decide
  have hdescent : baseEnd_389779 < baseStart_389779 := by decide
  rcases family_descends (prefixWord ++ tailWord_389779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389813 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 2]
def baseStart_389813 : Nat := 118140960795 + 389813 * 2 ^ 59
def prefixEnd_389813 : Nat := 4983230072969 + 3 ^ 40 * 389813 * 2
def baseEnd_389813 : Nat := 177921274996612078706479

theorem tailTrace_389813 : CollatzResearch.WordTrace tailWord_389813 prefixEnd_389813 177921274996612078706479 := by
  unfold tailWord_389813
  simp only [CollatzResearch.WordTrace]
  refine ⟨14217648136781550605222093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9478432091187700403481395 14217648136781550605222093)
  ·
    refine ⟨5331618051293081476958285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14217648136781550605222093 5331618051293081476958285)
    ·
      refine ⟨1999356769234905553859357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5331618051293081476958285 1999356769234905553859357)
      ·
        refine ⟨749758788463089582697259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1999356769234905553859357 749758788463089582697259)
        ·
          refine ⟨1124638182694634374045889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749758788463089582697259 1124638182694634374045889)
          ·
            refine ⟨843478637020975780534417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1124638182694634374045889 843478637020975780534417)
            ·
              refine ⟨632608977765731835400813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843478637020975780534417 632608977765731835400813)
              ·
                refine ⟨237228366662149438275305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632608977765731835400813 237228366662149438275305)
                ·
                  refine ⟨177921274996612078706479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237228366662149438275305 177921274996612078706479)
                  ·
                    rfl

theorem cell20_389813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_389813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389813 prefixEnd_389813 := by exact prefixLift 389813
  have htrace : WordTrace (prefixWord ++ tailWord_389813) baseStart_389813 baseEnd_389813 := by
    simpa [prefixWord, tailWord_389813, baseEnd_389813] using wordTrace_append hprefix tailTrace_389813
  have hstable : (prefixWord ++ tailWord_389813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389813).length < 2 ^ (prefixWord ++ tailWord_389813).sum := by decide
  have hdescent : baseEnd_389813 < baseStart_389813 := by decide
  rcases family_descends (prefixWord ++ tailWord_389813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389830 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_389830 : Nat := 118140960795 + 389830 * 2 ^ 59
def prefixEnd_389830 : Nat := 4983230072969 + 3 ^ 40 * 389830 * 2
def baseEnd_389830 : Nat := 177929034259835575139743

theorem tailTrace_389830 : CollatzResearch.WordTrace tailWord_389830 prefixEnd_389830 177929034259835575139743 := by
  unfold tailWord_389830
  simp only [CollatzResearch.WordTrace]
  refine ⟨444320880553748828393467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9478845451813308339060629 444320880553748828393467)
  ·
    refine ⟨666481320830623242590201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444320880553748828393467 666481320830623242590201)
    ·
      refine ⟨499860990622967431942651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666481320830623242590201 499860990622967431942651)
      ·
        refine ⟨749791485934451147913977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499860990622967431942651 749791485934451147913977)
        ·
          refine ⟨562343614450838360935483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749791485934451147913977 562343614450838360935483)
          ·
            refine ⟨843515421676257541403225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562343614450838360935483 843515421676257541403225)
            ·
              refine ⟨632636566257193156052419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843515421676257541403225 632636566257193156052419)
              ·
                refine ⟨948954849385789734078629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632636566257193156052419 948954849385789734078629)
                ·
                  refine ⟨177929034259835575139743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948954849385789734078629 177929034259835575139743)
                  ·
                    rfl

theorem cell20_389830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_389830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389830 prefixEnd_389830 := by exact prefixLift 389830
  have htrace : WordTrace (prefixWord ++ tailWord_389830) baseStart_389830 baseEnd_389830 := by
    simpa [prefixWord, tailWord_389830, baseEnd_389830] using wordTrace_append hprefix tailTrace_389830
  have hstable : (prefixWord ++ tailWord_389830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389830).length < 2 ^ (prefixWord ++ tailWord_389830).sum := by decide
  have hdescent : baseEnd_389830 < baseStart_389830 := by decide
  rcases family_descends (prefixWord ++ tailWord_389830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389831 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_389831 : Nat := 118140960795 + 389831 * 2 ^ 59
def prefixEnd_389831 : Nat := 4983230072969 + 3 ^ 40 * 389831 * 2
def baseEnd_389831 : Nat := 177929490687084016106405

theorem tailTrace_389831 : CollatzResearch.WordTrace tailWord_389831 prefixEnd_389831 177929490687084016106405 := by
  unfold tailWord_389831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14218304650716339679377347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9478869767144226452918231 14218304650716339679377347)
  ·
    refine ⟨21327456976074509519066021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14218304650716339679377347 21327456976074509519066021)
    ·
      refine ⟨3998898183013970534824879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21327456976074509519066021 3998898183013970534824879)
      ·
        refine ⟨5998347274520955802237319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998898183013970534824879 5998347274520955802237319)
        ·
          refine ⟨8997520911781433703355979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5998347274520955802237319 8997520911781433703355979)
          ·
            refine ⟨13496281367672150555033969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8997520911781433703355979 13496281367672150555033969)
            ·
              refine ⟨10122211025754112916275477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13496281367672150555033969 10122211025754112916275477)
              ·
                refine ⟨474478641832224042950413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10122211025754112916275477 474478641832224042950413)
                ·
                  refine ⟨177929490687084016106405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474478641832224042950413 177929490687084016106405)
                  ·
                    rfl

theorem cell20_389831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_389831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389831 prefixEnd_389831 := by exact prefixLift 389831
  have htrace : WordTrace (prefixWord ++ tailWord_389831) baseStart_389831 baseEnd_389831 := by
    simpa [prefixWord, tailWord_389831, baseEnd_389831] using wordTrace_append hprefix tailTrace_389831
  have hstable : (prefixWord ++ tailWord_389831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389831).length < 2 ^ (prefixWord ++ tailWord_389831).sum := by decide
  have hdescent : baseEnd_389831 < baseStart_389831 := by decide
  rcases family_descends (prefixWord ++ tailWord_389831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389834 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_389834 : Nat := 118140960795 + 389834 * 2 ^ 59
def prefixEnd_389834 : Nat := 4983230072969 + 3 ^ 40 * 389834 * 2
def baseEnd_389834 : Nat := 177930859968829339006393

theorem tailTrace_389834 : CollatzResearch.WordTrace tailWord_389834 prefixEnd_389834 177930859968829339006393 := by
  unfold tailWord_389834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3554603517426367797934139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9478942713136980794491037 3554603517426367797934139)
  ·
    refine ⟨5331905276139551696901209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3554603517426367797934139 5331905276139551696901209)
    ·
      refine ⟨3998928957104663772675907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5331905276139551696901209 3998928957104663772675907)
      ·
        refine ⟨5998393435656995659013861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998928957104663772675907 5998393435656995659013861)
        ·
          refine ⟨1124698769185686686065099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5998393435656995659013861 1124698769185686686065099)
          ·
            refine ⟨1687048153778530029097649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124698769185686686065099 1687048153778530029097649)
            ·
              refine ⟨1265286115333897521823237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687048153778530029097649 1265286115333897521823237)
              ·
                refine ⟨237241146625105785341857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1265286115333897521823237 237241146625105785341857)
                ·
                  refine ⟨177930859968829339006393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237241146625105785341857 177930859968829339006393)
                  ·
                    rfl

theorem cell20_389834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_389834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389834 prefixEnd_389834 := by exact prefixLift 389834
  have htrace : WordTrace (prefixWord ++ tailWord_389834) baseStart_389834 baseEnd_389834 := by
    simpa [prefixWord, tailWord_389834, baseEnd_389834] using wordTrace_append hprefix tailTrace_389834
  have hstable : (prefixWord ++ tailWord_389834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389834).length < 2 ^ (prefixWord ++ tailWord_389834).sum := by decide
  have hdescent : baseEnd_389834 < baseStart_389834 := by decide
  rcases family_descends (prefixWord ++ tailWord_389834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389844 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_389844 : Nat := 118140960795 + 389844 * 2 ^ 59
def prefixEnd_389844 : Nat := 4983230072969 + 3 ^ 40 * 389844 * 2
def baseEnd_389844 : Nat := 177935424241313748673019

theorem tailTrace_389844 : CollatzResearch.WordTrace tailWord_389844 prefixEnd_389844 177935424241313748673019 := by
  unfold tailWord_389844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109389399834621449800293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9479185866446161933067057 7109389399834621449800293)
  ·
    refine ⟨1333010512468991521837555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7109389399834621449800293 1333010512468991521837555)
    ·
      refine ⟨1999515768703487282756333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333010512468991521837555 1999515768703487282756333)
      ·
        refine ⟨749818413263807731033625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1999515768703487282756333 749818413263807731033625)
        ·
          refine ⟨562363809947855798275219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749818413263807731033625 562363809947855798275219)
          ·
            refine ⟨843545714921783697412829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562363809947855798275219 843545714921783697412829)
            ·
              refine ⟨316329643095668886529811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843545714921783697412829 316329643095668886529811)
              ·
                refine ⟨474494464643503329794717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316329643095668886529811 474494464643503329794717)
                ·
                  refine ⟨177935424241313748673019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474494464643503329794717 177935424241313748673019)
                  ·
                    rfl

theorem cell20_389844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_389844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389844 prefixEnd_389844 := by exact prefixLift 389844
  have htrace : WordTrace (prefixWord ++ tailWord_389844) baseStart_389844 baseEnd_389844 := by
    simpa [prefixWord, tailWord_389844, baseEnd_389844] using wordTrace_append hprefix tailTrace_389844
  have hstable : (prefixWord ++ tailWord_389844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389844).length < 2 ^ (prefixWord ++ tailWord_389844).sum := by decide
  have hdescent : baseEnd_389844 < baseStart_389844 := by decide
  rcases family_descends (prefixWord ++ tailWord_389844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389869 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_389869 : Nat := 118140960795 + 389869 * 2 ^ 59
def prefixEnd_389869 : Nat := 4983230072969 + 3 ^ 40 * 389869 * 2
def baseEnd_389869 : Nat := 177946834922524772839583

theorem tailTrace_389869 : CollatzResearch.WordTrace tailWord_389869 prefixEnd_389869 177946834922524772839583 := by
  unfold tailWord_389869
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219690624578672169260661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9479793749719114779507107 14219690624578672169260661)
  ·
    refine ⟨1333095996054250515868187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14219690624578672169260661 1333095996054250515868187)
    ·
      refine ⟨1999643994081375773802281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333095996054250515868187 1999643994081375773802281)
      ·
        refine ⟨1499732995561031830351711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1999643994081375773802281 1499732995561031830351711)
        ·
          refine ⟨2249599493341547745527567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499732995561031830351711 2249599493341547745527567)
          ·
            refine ⟨3374399240012321618291351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2249599493341547745527567 3374399240012321618291351)
            ·
              refine ⟨5061598860018482427437027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374399240012321618291351 5061598860018482427437027)
              ·
                refine ⟨7592398290027723641155541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061598860018482427437027 7592398290027723641155541)
                ·
                  refine ⟨177946834922524772839583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7592398290027723641155541 177946834922524772839583)
                  ·
                    rfl

theorem cell20_389869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_389869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389869 prefixEnd_389869 := by exact prefixLift 389869
  have htrace : WordTrace (prefixWord ++ tailWord_389869) baseStart_389869 baseEnd_389869 := by
    simpa [prefixWord, tailWord_389869, baseEnd_389869] using wordTrace_append hprefix tailTrace_389869
  have hstable : (prefixWord ++ tailWord_389869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389869).length < 2 ^ (prefixWord ++ tailWord_389869).sum := by decide
  have hdescent : baseEnd_389869 < baseStart_389869 := by decide
  rcases family_descends (prefixWord ++ tailWord_389869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389886 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_389886 : Nat := 118140960795 + 389886 * 2 ^ 59
def prefixEnd_389886 : Nat := 4983230072969 + 3 ^ 40 * 389886 * 2
def baseEnd_389886 : Nat := 177954594185748269272847

theorem tailTrace_389886 : CollatzResearch.WordTrace tailWord_389886 prefixEnd_389886 177954594185748269272847 := by
  unfold tailWord_389886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777538833189635509078689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9480207110344722715086341 1777538833189635509078689)
  ·
    refine ⟨1333154124892226631809017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1777538833189635509078689 1333154124892226631809017)
    ·
      refine ⟨999865593669169973856763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1333154124892226631809017 999865593669169973856763)
      ·
        refine ⟨1499798390503754960785145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999865593669169973856763 1499798390503754960785145)
        ·
          refine ⟨1124848792877816220588859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1499798390503754960785145 1124848792877816220588859)
          ·
            refine ⟨1687273189316724330883289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124848792877816220588859 1687273189316724330883289)
            ·
              refine ⟨1265454891987543248162467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687273189316724330883289 1265454891987543248162467)
              ·
                refine ⟨1898182337981314872243701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265454891987543248162467 1898182337981314872243701)
                ·
                  refine ⟨177954594185748269272847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1898182337981314872243701 177954594185748269272847)
                  ·
                    rfl

theorem cell20_389886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_389886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389886 prefixEnd_389886 := by exact prefixLift 389886
  have htrace : WordTrace (prefixWord ++ tailWord_389886) baseStart_389886 baseEnd_389886 := by
    simpa [prefixWord, tailWord_389886, baseEnd_389886] using wordTrace_append hprefix tailTrace_389886
  have hstable : (prefixWord ++ tailWord_389886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389886).length < 2 ^ (prefixWord ++ tailWord_389886).sum := by decide
  have hdescent : baseEnd_389886 < baseStart_389886 := by decide
  rcases family_descends (prefixWord ++ tailWord_389886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389893 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 2]
def baseStart_389893 : Nat := 118140960795 + 389893 * 2 ^ 59
def prefixEnd_389893 : Nat := 4983230072969 + 3 ^ 40 * 389893 * 2
def baseEnd_389893 : Nat := 177957789176487356039485

theorem tailTrace_389893 : CollatzResearch.WordTrace tailWord_389893 prefixEnd_389893 177957789176487356039485 := by
  unfold tailWord_389893
  simp only [CollatzResearch.WordTrace]
  refine ⟨14220565976491724268134333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9480377317661149512089555 14220565976491724268134333)
  ·
    refine ⟨5332712241184396600550375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14220565976491724268134333 5332712241184396600550375)
    ·
      refine ⟨7999068361776594900825563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5332712241184396600550375 7999068361776594900825563)
      ·
        refine ⟨11998602542664892351238345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7999068361776594900825563 11998602542664892351238345)
        ·
          refine ⟨8998951906998669263428759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11998602542664892351238345 8998951906998669263428759)
          ·
            refine ⟨13498427860498003895143139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8998951906998669263428759 13498427860498003895143139)
            ·
              refine ⟨20247641790747005842714709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13498427860498003895143139 20247641790747005842714709)
              ·
                refine ⟨237277052235316474719313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20247641790747005842714709 237277052235316474719313)
                ·
                  refine ⟨177957789176487356039485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237277052235316474719313 177957789176487356039485)
                  ·
                    rfl

theorem cell20_389893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_389893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389893 prefixEnd_389893 := by exact prefixLift 389893
  have htrace : WordTrace (prefixWord ++ tailWord_389893) baseStart_389893 baseEnd_389893 := by
    simpa [prefixWord, tailWord_389893, baseEnd_389893] using wordTrace_append hprefix tailTrace_389893
  have hstable : (prefixWord ++ tailWord_389893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389893).length < 2 ^ (prefixWord ++ tailWord_389893).sum := by decide
  have hdescent : baseEnd_389893 < baseStart_389893 := by decide
  rcases family_descends (prefixWord ++ tailWord_389893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389907 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_389907 : Nat := 118140960795 + 389907 * 2 ^ 59
def prefixEnd_389907 : Nat := 4983230072969 + 3 ^ 40 * 389907 * 2
def baseEnd_389907 : Nat := 177964179157965529572761

theorem tailTrace_389907 : CollatzResearch.WordTrace tailWord_389907 prefixEnd_389907 177964179157965529572761 := by
  unfold tailWord_389907
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221076598441004659143975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9480717732294003106095983 14221076598441004659143975)
  ·
    refine ⟨21331614897661506988715963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14221076598441004659143975 21331614897661506988715963)
    ·
      refine ⟨31997422346492260483073945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21331614897661506988715963 31997422346492260483073945)
      ·
        refine ⟨23998066759869195362305459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31997422346492260483073945 23998066759869195362305459)
        ·
          refine ⟨35997100139803793043458189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23998066759869195362305459 35997100139803793043458189)
          ·
            refine ⟨13498912552426422391296821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35997100139803793043458189 13498912552426422391296821)
            ·
              refine ⟨1265523051789977099184077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13498912552426422391296821 1265523051789977099184077)
              ·
                refine ⟨474571144421241412194029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265523051789977099184077 474571144421241412194029)
                ·
                  refine ⟨177964179157965529572761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474571144421241412194029 177964179157965529572761)
                  ·
                    rfl

theorem cell20_389907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_389907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389907 prefixEnd_389907 := by exact prefixLift 389907
  have htrace : WordTrace (prefixWord ++ tailWord_389907) baseStart_389907 baseEnd_389907 := by
    simpa [prefixWord, tailWord_389907, baseEnd_389907] using wordTrace_append hprefix tailTrace_389907
  have hstable : (prefixWord ++ tailWord_389907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389907).length < 2 ^ (prefixWord ++ tailWord_389907).sum := by decide
  have hdescent : baseEnd_389907 < baseStart_389907 := by decide
  rcases family_descends (prefixWord ++ tailWord_389907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389914 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_389914 : Nat := 118140960795 + 389914 * 2 ^ 59
def prefixEnd_389914 : Nat := 4983230072969 + 3 ^ 40 * 389914 * 2
def baseEnd_389914 : Nat := 177967374148704616339399

theorem tailTrace_389914 : CollatzResearch.WordTrace tailWord_389914 prefixEnd_389914 177967374148704616339399 := by
  unfold tailWord_389914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555332977353911213662199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9480887939610429903099197 3555332977353911213662199)
  ·
    refine ⟨5332999466030866820493299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3555332977353911213662199 5332999466030866820493299)
    ·
      refine ⟨7999499199046300230739949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5332999466030866820493299 7999499199046300230739949)
      ·
        refine ⟨2999812199642362586527481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7999499199046300230739949 2999812199642362586527481)
        ·
          refine ⟨2249859149731771939895611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2999812199642362586527481 2249859149731771939895611)
          ·
            refine ⟨3374788724597657909843417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2249859149731771939895611 3374788724597657909843417)
            ·
              refine ⟨2531091543448243432382563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3374788724597657909843417 2531091543448243432382563)
              ·
                refine ⟨3796637315172365148573845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531091543448243432382563 3796637315172365148573845)
                ·
                  refine ⟨177967374148704616339399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3796637315172365148573845 177967374148704616339399)
                  ·
                    rfl

theorem cell20_389914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_389914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389914 prefixEnd_389914 := by exact prefixLift 389914
  have htrace : WordTrace (prefixWord ++ tailWord_389914) baseStart_389914 baseEnd_389914 := by
    simpa [prefixWord, tailWord_389914, baseEnd_389914] using wordTrace_append hprefix tailTrace_389914
  have hstable : (prefixWord ++ tailWord_389914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389914).length < 2 ^ (prefixWord ++ tailWord_389914).sum := by decide
  have hdescent : baseEnd_389914 < baseStart_389914 := by decide
  rcases family_descends (prefixWord ++ tailWord_389914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389921 : List Nat := [1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_389921 : Nat := 118140960795 + 389921 * 2 ^ 59
def prefixEnd_389921 : Nat := 4983230072969 + 3 ^ 40 * 389921 * 2
def baseEnd_389921 : Nat := 59323523046481234368679

theorem tailTrace_389921 : CollatzResearch.WordTrace tailWord_389921 prefixEnd_389921 59323523046481234368679 := by
  unfold tailWord_389921
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221587220390285050153617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9481058146926856700102411 14221587220390285050153617)
  ·
    refine ⟨10666190415292713787615213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14221587220390285050153617 10666190415292713787615213)
    ·
      refine ⟨3999821405734767670355705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10666190415292713787615213 3999821405734767670355705)
      ·
        refine ⟨2999866054301075752766779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3999821405734767670355705 2999866054301075752766779)
        ·
          refine ⟨4499799081451613629150169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999866054301075752766779 4499799081451613629150169)
          ·
            refine ⟨3374849311088710221862627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4499799081451613629150169 3374849311088710221862627)
            ·
              refine ⟨5062273966633065332793941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374849311088710221862627 5062273966633065332793941)
              ·
                refine ⟨59323523046481234368679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5062273966633065332793941 59323523046481234368679)
                ·
                  rfl

theorem cell20_389921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_389921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389921 prefixEnd_389921 := by exact prefixLift 389921
  have htrace : WordTrace (prefixWord ++ tailWord_389921) baseStart_389921 baseEnd_389921 := by
    simpa [prefixWord, tailWord_389921, baseEnd_389921] using wordTrace_append hprefix tailTrace_389921
  have hstable : (prefixWord ++ tailWord_389921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389921).length < 2 ^ (prefixWord ++ tailWord_389921).sum := by decide
  have hdescent : baseEnd_389921 < baseStart_389921 := by decide
  rcases family_descends (prefixWord ++ tailWord_389921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389969 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_389969 : Nat := 118140960795 + 389969 * 2 ^ 59
def prefixEnd_389969 : Nat := 4983230072969 + 3 ^ 40 * 389969 * 2
def baseEnd_389969 : Nat := 177992477647368869505841

theorem tailTrace_389969 : CollatzResearch.WordTrace tailWord_389969 prefixEnd_389969 177992477647368869505841 := by
  unfold tailWord_389969
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223337924216389247900961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9482225282810926165267307 14223337924216389247900961)
  ·
    refine ⟨10667503443162291935925721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14223337924216389247900961 10667503443162291935925721)
    ·
      refine ⟨8000627582371718951944291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10667503443162291935925721 8000627582371718951944291)
      ·
        refine ⟨12000941373557578427916437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000627582371718951944291 12000941373557578427916437)
        ·
          refine ⟨562544126885511488808583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12000941373557578427916437 562544126885511488808583)
          ·
            refine ⟨843816190328267233212875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562544126885511488808583 843816190328267233212875)
            ·
              refine ⟨1265724285492400849819313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843816190328267233212875 1265724285492400849819313)
              ·
                refine ⟨949293214119300637364485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265724285492400849819313 949293214119300637364485)
                ·
                  refine ⟨177992477647368869505841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949293214119300637364485 177992477647368869505841)
                  ·
                    rfl

theorem cell20_389969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_389969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_389969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_389969 prefixEnd_389969 := by exact prefixLift 389969
  have htrace : WordTrace (prefixWord ++ tailWord_389969) baseStart_389969 baseEnd_389969 := by
    simpa [prefixWord, tailWord_389969, baseEnd_389969] using wordTrace_append hprefix tailTrace_389969
  have hstable : (prefixWord ++ tailWord_389969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389969).length < 2 ^ (prefixWord ++ tailWord_389969).sum := by decide
  have hdescent : baseEnd_389969 < baseStart_389969 := by decide
  rcases family_descends (prefixWord ++ tailWord_389969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390028 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_390028 : Nat := 118140960795 + 390028 * 2 ^ 59
def prefixEnd_390028 : Nat := 4983230072969 + 3 ^ 40 * 390028 * 2
def baseEnd_390028 : Nat := 178019406855026886538933

theorem tailTrace_390028 : CollatzResearch.WordTrace tailWord_390028 prefixEnd_390028 178019406855026886538933 := by
  unfold tailWord_390028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7112744915501321162149369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9483659887335094882865825 7112744915501321162149369)
  ·
    refine ⟨5334558686625990871612027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7112744915501321162149369 5334558686625990871612027)
    ·
      refine ⟨8001838029938986307418041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5334558686625990871612027 8001838029938986307418041)
      ·
        refine ⟨6001378522454239730563531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8001838029938986307418041 6001378522454239730563531)
        ·
          refine ⟨9002067783681359595845297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001378522454239730563531 9002067783681359595845297)
          ·
            refine ⟨6751550837761019696883973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9002067783681359595845297 6751550837761019696883973)
            ·
              refine ⟨1265915782080191193165745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6751550837761019696883973 1265915782080191193165745)
              ·
                refine ⟨949436836560143394874309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265915782080191193165745 949436836560143394874309)
                ·
                  refine ⟨178019406855026886538933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949436836560143394874309 178019406855026886538933)
                  ·
                    rfl

theorem cell20_390028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_390028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390028 prefixEnd_390028 := by exact prefixLift 390028
  have htrace : WordTrace (prefixWord ++ tailWord_390028) baseStart_390028 baseEnd_390028 := by
    simpa [prefixWord, tailWord_390028, baseEnd_390028] using wordTrace_append hprefix tailTrace_390028
  have hstable : (prefixWord ++ tailWord_390028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390028).length < 2 ^ (prefixWord ++ tailWord_390028).sum := by decide
  have hdescent : baseEnd_390028 < baseStart_390028 := by decide
  rcases family_descends (prefixWord ++ tailWord_390028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390073 : List Nat := [1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_390073 : Nat := 118140960795 + 390073 * 2 ^ 59
def prefixEnd_390073 : Nat := 4983230072969 + 3 ^ 40 * 390073 * 2
def baseEnd_390073 : Nat := 59346648693735576679583

theorem tailTrace_390073 : CollatzResearch.WordTrace tailWord_390073 prefixEnd_390073 59346648693735576679583 := by
  unfold tailWord_390073
  simp only [CollatzResearch.WordTrace]
  refine ⟨14227131115839615009686873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9484754077226410006457915 14227131115839615009686873)
  ·
    refine ⟨10670348336879711257265155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14227131115839615009686873 10670348336879711257265155)
    ·
      refine ⟨16005522505319566885897733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10670348336879711257265155 16005522505319566885897733)
      ·
        refine ⟨3001035469747418791105825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16005522505319566885897733 3001035469747418791105825)
        ·
          refine ⟨2250776602310564093329369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3001035469747418791105825 2250776602310564093329369)
          ·
            refine ⟨1688082451732923069997027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250776602310564093329369 1688082451732923069997027)
            ·
              refine ⟨2532123677599384604995541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688082451732923069997027 2532123677599384604995541)
              ·
                refine ⟨59346648693735576679583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2532123677599384604995541 59346648693735576679583)
                ·
                  rfl

theorem cell20_390073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_390073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390073 prefixEnd_390073 := by exact prefixLift 390073
  have htrace : WordTrace (prefixWord ++ tailWord_390073) baseStart_390073 baseEnd_390073 := by
    simpa [prefixWord, tailWord_390073, baseEnd_390073] using wordTrace_append hprefix tailTrace_390073
  have hstable : (prefixWord ++ tailWord_390073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390073).length < 2 ^ (prefixWord ++ tailWord_390073).sum := by decide
  have hdescent : baseEnd_390073 < baseStart_390073 := by decide
  rcases family_descends (prefixWord ++ tailWord_390073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390111 : List Nat := [1, 1, 2, 3, 5, 8]
def baseStart_390111 : Nat := 118140960795 + 390111 * 2 ^ 59
def prefixEnd_390111 : Nat := 4983230072969 + 3 ^ 40 * 390111 * 2
def baseEnd_390111 : Nat := 6594714456172129139701

theorem tailTrace_390111 : CollatzResearch.WordTrace tailWord_390111 prefixEnd_390111 6594714456172129139701 := by
  unfold tailWord_390111
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228517089701947499570187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9485678059801298333046791 14228517089701947499570187)
  ·
    refine ⟨21342775634552921249355281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14228517089701947499570187 21342775634552921249355281)
    ·
      refine ⟨16007081725914690937016461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21342775634552921249355281 16007081725914690937016461)
      ·
        refine ⟨6002655647218009101381173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16007081725914690937016461 6002655647218009101381173)
        ·
          refine ⟨562748966926688353254485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6002655647218009101381173 562748966926688353254485)
          ·
            refine ⟨6594714456172129139701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 562748966926688353254485 6594714456172129139701)
            ·
              rfl

theorem cell20_390111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 8].length) (baseStart_390111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390111 prefixEnd_390111 := by exact prefixLift 390111
  have htrace : WordTrace (prefixWord ++ tailWord_390111) baseStart_390111 baseEnd_390111 := by
    simpa [prefixWord, tailWord_390111, baseEnd_390111] using wordTrace_append hprefix tailTrace_390111
  have hstable : (prefixWord ++ tailWord_390111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390111).length < 2 ^ (prefixWord ++ tailWord_390111).sum := by decide
  have hdescent : baseEnd_390111 < baseStart_390111 := by decide
  rcases family_descends (prefixWord ++ tailWord_390111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390117 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 2]
def baseStart_390117 : Nat := 118140960795 + 390117 * 2 ^ 59
def prefixEnd_390117 : Nat := 4983230072969 + 3 ^ 40 * 390117 * 2
def baseEnd_390117 : Nat := 178060028880138132571903

theorem tailTrace_390117 : CollatzResearch.WordTrace tailWord_390117 prefixEnd_390117 178060028880138132571903 := by
  unfold tailWord_390117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228735927680210524288605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9485823951786807016192403 14228735927680210524288605)
  ·
    refine ⟨5335775972880078946608227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14228735927680210524288605 5335775972880078946608227)
    ·
      refine ⟨8003663959320118419912341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335775972880078946608227 8003663959320118419912341)
      ·
        refine ⟨375171748093130550933391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8003663959320118419912341 375171748093130550933391)
        ·
          refine ⟨562757622139695826400087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375171748093130550933391 562757622139695826400087)
          ·
            refine ⟨844136433209543739600131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562757622139695826400087 844136433209543739600131)
            ·
              refine ⟨1266204649814315609400197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844136433209543739600131 1266204649814315609400197)
              ·
                refine ⟨237413371840184176762537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1266204649814315609400197 237413371840184176762537)
                ·
                  refine ⟨178060028880138132571903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237413371840184176762537 178060028880138132571903)
                  ·
                    rfl

theorem cell20_390117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_390117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390117 prefixEnd_390117 := by exact prefixLift 390117
  have htrace : WordTrace (prefixWord ++ tailWord_390117) baseStart_390117 baseEnd_390117 := by
    simpa [prefixWord, tailWord_390117, baseEnd_390117] using wordTrace_append hprefix tailTrace_390117
  have hstable : (prefixWord ++ tailWord_390117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390117).length < 2 ^ (prefixWord ++ tailWord_390117).sum := by decide
  have hdescent : baseEnd_390117 < baseStart_390117 := by decide
  rcases family_descends (prefixWord ++ tailWord_390117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390162 : List Nat := [3, 2, 5, 1, 1, 1, 7]
def baseStart_390162 : Nat := 118140960795 + 390162 * 2 ^ 59
def prefixEnd_390162 : Nat := 4983230072969 + 3 ^ 40 * 390162 * 2
def baseEnd_390162 : Nat := 19786729789590886230191

theorem tailTrace_390162 : CollatzResearch.WordTrace tailWord_390162 prefixEnd_390162 19786729789590886230191 := by
  unfold tailWord_390162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557594303129295802419185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9486918141678122139784493 3557594303129295802419185)
  ·
    refine ⟨2668195727346971851814389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3557594303129295802419185 2668195727346971851814389)
    ·
      refine ⟨250143349438778611107599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2668195727346971851814389 250143349438778611107599)
      ·
        refine ⟨375215024158167916661399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250143349438778611107599 375215024158167916661399)
        ·
          refine ⟨562822536237251874992099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375215024158167916661399 562822536237251874992099)
          ·
            refine ⟨844233804355877812488149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562822536237251874992099 844233804355877812488149)
            ·
              refine ⟨19786729789590886230191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 844233804355877812488149 19786729789590886230191)
              ·
                rfl

theorem cell20_390162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 7].length) (baseStart_390162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390162 prefixEnd_390162 := by exact prefixLift 390162
  have htrace : WordTrace (prefixWord ++ tailWord_390162) baseStart_390162 baseEnd_390162 := by
    simpa [prefixWord, tailWord_390162, baseEnd_390162] using wordTrace_append hprefix tailTrace_390162
  have hstable : (prefixWord ++ tailWord_390162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390162).length < 2 ^ (prefixWord ++ tailWord_390162).sum := by decide
  have hdescent : baseEnd_390162 < baseStart_390162 := by decide
  rcases family_descends (prefixWord ++ tailWord_390162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390163 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_390163 : Nat := 118140960795 + 390163 * 2 ^ 59
def prefixEnd_390163 : Nat := 4983230072969 + 3 ^ 40 * 390163 * 2
def baseEnd_390163 : Nat := 178081024533566417038381

theorem tailTrace_390163 : CollatzResearch.WordTrace tailWord_390163 prefixEnd_390163 178081024533566417038381 := by
  unfold tailWord_390163
  simp only [CollatzResearch.WordTrace]
  refine ⟨14230413685513560380463143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9486942457009040253642095 14230413685513560380463143)
  ·
    refine ⟨21345620528270340570694715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14230413685513560380463143 21345620528270340570694715)
    ·
      refine ⟨32018430792405510856042073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21345620528270340570694715 32018430792405510856042073)
      ·
        refine ⟨24013823094304133142031555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32018430792405510856042073 24013823094304133142031555)
        ·
          refine ⟨36020734641456199713047333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24013823094304133142031555 36020734641456199713047333)
          ·
            refine ⟨6753887745273037446196375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36020734641456199713047333 6753887745273037446196375)
            ·
              refine ⟨10130831617909556169294563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753887745273037446196375 10130831617909556169294563)
              ·
                refine ⟨15196247426864334253941845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10130831617909556169294563 15196247426864334253941845)
                ·
                  refine ⟨178081024533566417038381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15196247426864334253941845 178081024533566417038381)
                  ·
                    rfl

theorem cell20_390163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_390163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390163 prefixEnd_390163 := by exact prefixLift 390163
  have htrace : WordTrace (prefixWord ++ tailWord_390163) baseStart_390163 baseEnd_390163 := by
    simpa [prefixWord, tailWord_390163, baseEnd_390163] using wordTrace_append hprefix tailTrace_390163
  have hstable : (prefixWord ++ tailWord_390163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390163).length < 2 ^ (prefixWord ++ tailWord_390163).sum := by decide
  have hdescent : baseEnd_390163 < baseStart_390163 := by decide
  rcases family_descends (prefixWord ++ tailWord_390163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390176 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_390176 : Nat := 118140960795 + 390176 * 2 ^ 59
def prefixEnd_390176 : Nat := 4983230072969 + 3 ^ 40 * 390176 * 2
def baseEnd_390176 : Nat := 178086958087796149604995

theorem tailTrace_390176 : CollatzResearch.WordTrace tailWord_390176 prefixEnd_390176 178086958087796149604995 := by
  unfold tailWord_390176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115443917233231800343191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9487258556310975733790921 7115443917233231800343191)
  ·
    refine ⟨10673165875849847700514787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115443917233231800343191 10673165875849847700514787)
    ·
      refine ⟨16009748813774771550772181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673165875849847700514787 16009748813774771550772181)
      ·
        refine ⟨375228487822846208221223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16009748813774771550772181 375228487822846208221223)
        ·
          refine ⟨562842731734269312331835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375228487822846208221223 562842731734269312331835)
          ·
            refine ⟨844264097601403968497753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562842731734269312331835 844264097601403968497753)
            ·
              refine ⟨633198073201052976373315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844264097601403968497753 633198073201052976373315)
              ·
                refine ⟨949797109801579464559973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633198073201052976373315 949797109801579464559973)
                ·
                  refine ⟨178086958087796149604995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949797109801579464559973 178086958087796149604995)
                  ·
                    rfl

theorem cell20_390176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_390176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390176 prefixEnd_390176 := by exact prefixLift 390176
  have htrace : WordTrace (prefixWord ++ tailWord_390176) baseStart_390176 baseEnd_390176 := by
    simpa [prefixWord, tailWord_390176, baseEnd_390176] using wordTrace_append hprefix tailTrace_390176
  have hstable : (prefixWord ++ tailWord_390176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390176).length < 2 ^ (prefixWord ++ tailWord_390176).sum := by decide
  have hdescent : baseEnd_390176 < baseStart_390176 := by decide
  rcases family_descends (prefixWord ++ tailWord_390176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390204 : List Nat := [2, 2, 2, 2, 2, 2, 4, 4]
def baseStart_390204 : Nat := 118140960795 + 390204 * 2 ^ 59
def prefixEnd_390204 : Nat := 4983230072969 + 3 ^ 40 * 390204 * 2
def baseEnd_390204 : Nat := 59366579350250832223849

theorem tailTrace_390204 : CollatzResearch.WordTrace tailWord_390204 prefixEnd_390204 59366579350250832223849 := by
  unfold tailWord_390204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115954539182512191352833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9487939385576682921803777 7115954539182512191352833)
  ·
    refine ⟨5336965904386884143514625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7115954539182512191352833 5336965904386884143514625)
    ·
      refine ⟨4002724428290163107635969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5336965904386884143514625 4002724428290163107635969)
      ·
        refine ⟨3002043321217622330726977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4002724428290163107635969 3002043321217622330726977)
        ·
          refine ⟨2251532490913216748045233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3002043321217622330726977 2251532490913216748045233)
          ·
            refine ⟨1688649368184912561033925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2251532490913216748045233 1688649368184912561033925)
            ·
              refine ⟨316621756534671105193861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1688649368184912561033925 316621756534671105193861)
              ·
                refine ⟨59366579350250832223849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316621756534671105193861 59366579350250832223849)
                ·
                  rfl

theorem cell20_390204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_390204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390204 prefixEnd_390204 := by exact prefixLift 390204
  have htrace : WordTrace (prefixWord ++ tailWord_390204) baseStart_390204 baseEnd_390204 := by
    simpa [prefixWord, tailWord_390204, baseEnd_390204] using wordTrace_append hprefix tailTrace_390204
  have hstable : (prefixWord ++ tailWord_390204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390204).length < 2 ^ (prefixWord ++ tailWord_390204).sum := by decide
  have hdescent : baseEnd_390204 < baseStart_390204 := by decide
  rcases family_descends (prefixWord ++ tailWord_390204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390232 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_390232 : Nat := 118140960795 + 390232 * 2 ^ 59
def prefixEnd_390232 : Nat := 4983230072969 + 3 ^ 40 * 390232 * 2
def baseEnd_390232 : Nat := 178112518013708843738099

theorem tailTrace_390232 : CollatzResearch.WordTrace tailWord_390232 prefixEnd_390232 178112518013708843738099 := by
  unfold tailWord_390232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116465161131792582362475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9488620214842390109816633 7116465161131792582362475)
  ·
    refine ⟨10674697741697688873543713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7116465161131792582362475 10674697741697688873543713)
    ·
      refine ⟨8006023306273266655157785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10674697741697688873543713 8006023306273266655157785)
      ·
        refine ⟨6004517479704949991368339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8006023306273266655157785 6004517479704949991368339)
        ·
          refine ⟨9006776219557424987052509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6004517479704949991368339 9006776219557424987052509)
          ·
            refine ⟨3377541082334034370144691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9006776219557424987052509 3377541082334034370144691)
            ·
              refine ⟨5066311623501051555217037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377541082334034370144691 5066311623501051555217037)
              ·
                refine ⟨1899866858812894333206389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5066311623501051555217037 1899866858812894333206389)
                ·
                  refine ⟨178112518013708843738099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1899866858812894333206389 178112518013708843738099)
                  ·
                    rfl

theorem cell20_390232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_390232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390232 prefixEnd_390232 := by exact prefixLift 390232
  have htrace : WordTrace (prefixWord ++ tailWord_390232) baseStart_390232 baseEnd_390232 := by
    simpa [prefixWord, tailWord_390232, baseEnd_390232] using wordTrace_append hprefix tailTrace_390232
  have hstable : (prefixWord ++ tailWord_390232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390232).length < 2 ^ (prefixWord ++ tailWord_390232).sum := by decide
  have hdescent : baseEnd_390232 < baseStart_390232 := by decide
  rcases family_descends (prefixWord ++ tailWord_390232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390238 : List Nat := [4, 4, 1, 1, 1, 2, 2, 5]
def baseStart_390238 : Nat := 118140960795 + 390238 * 2 ^ 59
def prefixEnd_390238 : Nat := 4983230072969 + 3 ^ 40 * 390238 * 2
def baseEnd_390238 : Nat := 59371752192399829846025

theorem tailTrace_390238 : CollatzResearch.WordTrace tailWord_390238 prefixEnd_390238 59371752192399829846025 := by
  unfold tailWord_390238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779143645030231023680421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9488766106827898792962245 1779143645030231023680421)
  ·
    refine ⟨333589433443168316940079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1779143645030231023680421 333589433443168316940079)
    ·
      refine ⟨500384150164752475410119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333589433443168316940079 500384150164752475410119)
      ·
        refine ⟨750576225247128713115179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500384150164752475410119 750576225247128713115179)
        ·
          refine ⟨1125864337870693069672769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750576225247128713115179 1125864337870693069672769)
          ·
            refine ⟨844398253403019802254577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125864337870693069672769 844398253403019802254577)
            ·
              refine ⟨633298690052264851690933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844398253403019802254577 633298690052264851690933)
              ·
                refine ⟨59371752192399829846025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 633298690052264851690933 59371752192399829846025)
                ·
                  rfl

theorem cell20_390238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_390238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390238 prefixEnd_390238 := by exact prefixLift 390238
  have htrace : WordTrace (prefixWord ++ tailWord_390238) baseStart_390238 baseEnd_390238 := by
    simpa [prefixWord, tailWord_390238, baseEnd_390238] using wordTrace_append hprefix tailTrace_390238
  have hstable : (prefixWord ++ tailWord_390238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390238).length < 2 ^ (prefixWord ++ tailWord_390238).sum := by decide
  have hdescent : baseEnd_390238 < baseStart_390238 := by decide
  rcases family_descends (prefixWord ++ tailWord_390238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390242 : List Nat := [3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_390242 : Nat := 118140960795 + 390242 * 2 ^ 59
def prefixEnd_390242 : Nat := 4983230072969 + 3 ^ 40 * 390242 * 2
def baseEnd_390242 : Nat := 59372360762064417801575

theorem tailTrace_390242 : CollatzResearch.WordTrace tailWord_390242 prefixEnd_390242 59372360762064417801575 := by
  unfold tailWord_390242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558323763056839218147245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9488863368151571248392653 3558323763056839218147245)
  ·
    refine ⟨1334371411146314706805217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3558323763056839218147245 1334371411146314706805217)
    ·
      refine ⟨1000778558359736030103913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1334371411146314706805217 1000778558359736030103913)
      ·
        refine ⟨750583918769802022577935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1000778558359736030103913 750583918769802022577935)
        ·
          refine ⟨1125875878154703033866903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750583918769802022577935 1125875878154703033866903)
          ·
            refine ⟨1688813817232054550800355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125875878154703033866903 1688813817232054550800355)
            ·
              refine ⟨2533220725848081826200533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688813817232054550800355 2533220725848081826200533)
              ·
                refine ⟨59372360762064417801575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2533220725848081826200533 59372360762064417801575)
                ·
                  rfl

theorem cell20_390242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_390242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390242 prefixEnd_390242 := by exact prefixLift 390242
  have htrace : WordTrace (prefixWord ++ tailWord_390242) baseStart_390242 baseEnd_390242 := by
    simpa [prefixWord, tailWord_390242, baseEnd_390242] using wordTrace_append hprefix tailTrace_390242
  have hstable : (prefixWord ++ tailWord_390242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390242).length < 2 ^ (prefixWord ++ tailWord_390242).sum := by decide
  have hdescent : baseEnd_390242 < baseStart_390242 := by decide
  rcases family_descends (prefixWord ++ tailWord_390242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390249 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_390249 : Nat := 118140960795 + 390249 * 2 ^ 59
def prefixEnd_390249 : Nat := 4983230072969 + 3 ^ 40 * 390249 * 2
def baseEnd_390249 : Nat := 178120277276932340171363

theorem tailTrace_390249 : CollatzResearch.WordTrace tailWord_390249 prefixEnd_390249 178120277276932340171363 := by
  unfold tailWord_390249
  simp only [CollatzResearch.WordTrace]
  refine ⟨14233550363201997068093801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9489033575467998045395867 14233550363201997068093801)
  ·
    refine ⟨10675162772401497801070351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14233550363201997068093801 10675162772401497801070351)
    ·
      refine ⟨16012744158602246701605527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10675162772401497801070351 16012744158602246701605527)
      ·
        refine ⟨24019116237903370052408291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16012744158602246701605527 24019116237903370052408291)
        ·
          refine ⟨36028674356855055078612437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24019116237903370052408291 36028674356855055078612437)
          ·
            refine ⟨844422055238790353404979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36028674356855055078612437 844422055238790353404979)
            ·
              refine ⟨1266633082858185530107469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844422055238790353404979 1266633082858185530107469)
              ·
                refine ⟨474987406071819573790301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266633082858185530107469 474987406071819573790301)
                ·
                  refine ⟨178120277276932340171363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474987406071819573790301 178120277276932340171363)
                  ·
                    rfl

theorem cell20_390249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_390249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390249 prefixEnd_390249 := by exact prefixLift 390249
  have htrace : WordTrace (prefixWord ++ tailWord_390249) baseStart_390249 baseEnd_390249 := by
    simpa [prefixWord, tailWord_390249, baseEnd_390249] using wordTrace_append hprefix tailTrace_390249
  have hstable : (prefixWord ++ tailWord_390249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390249).length < 2 ^ (prefixWord ++ tailWord_390249).sum := by decide
  have hdescent : baseEnd_390249 < baseStart_390249 := by decide
  rcases family_descends (prefixWord ++ tailWord_390249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
