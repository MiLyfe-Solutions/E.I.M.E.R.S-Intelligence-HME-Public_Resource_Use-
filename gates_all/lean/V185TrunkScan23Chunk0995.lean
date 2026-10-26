import V185TrunkScan23Chunk0994

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5891573 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5891573 : Nat := 118140960795 + 5891573 * 2 ^ 59
def prefixEnd_5891573 : Nat := 4983230072969 + 3 ^ 40 * 5891573 * 2
def baseEnd_5891573 : Nat := 1008402920017194309080885

theorem tailTrace_5891573 : CollatzResearch.WordTrace tailWord_5891573 prefixEnd_5891573 1008402920017194309080885 := by
  unfold tailWord_5891573
  simp only [CollatzResearch.WordTrace]
  refine ⟨214883320684844696405791373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143255547123229797603860915 214883320684844696405791373)
  ·
    refine ⟨80581245256816761152171765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214883320684844696405791373 80581245256816761152171765)
    ·
      refine ⟨7554491742826571358016103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80581245256816761152171765 7554491742826571358016103)
      ·
        refine ⟨11331737614239857037024155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7554491742826571358016103 11331737614239857037024155)
        ·
          refine ⟨16997606421359785555536233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11331737614239857037024155 16997606421359785555536233)
          ·
            refine ⟨12748204816019839166652175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16997606421359785555536233 12748204816019839166652175)
            ·
              refine ⟨19122307224029758749978263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12748204816019839166652175 19122307224029758749978263)
              ·
                refine ⟨28683460836044638124967395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19122307224029758749978263 28683460836044638124967395)
                ·
                  refine ⟨43025191254066957187451093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28683460836044638124967395 43025191254066957187451093)
                  ·
                    refine ⟨1008402920017194309080885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43025191254066957187451093 1008402920017194309080885)
                    ·
                      rfl

theorem cell23_5891573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5891573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891573 prefixEnd_5891573 := by exact prefixLift 5891573
  have htrace : WordTrace (prefixWord ++ tailWord_5891573) baseStart_5891573 baseEnd_5891573 := by
    simpa [prefixWord, tailWord_5891573, baseEnd_5891573] using wordTrace_append hprefix tailTrace_5891573
  have hstable : (prefixWord ++ tailWord_5891573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891573).length < 2 ^ (prefixWord ++ tailWord_5891573).sum := by decide
  have hdescent : baseEnd_5891573 < baseStart_5891573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891576 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_5891576 : Nat := 118140960795 + 5891576 * 2 ^ 59
def prefixEnd_5891576 : Nat := 4983230072969 + 3 ^ 40 * 5891576 * 2
def baseEnd_5891576 : Nat := 3025210300493546415505141

theorem tailTrace_5891576 : CollatzResearch.WordTrace tailWord_5891576 prefixEnd_5891576 3025210300493546415505141 := by
  unfold tailWord_5891576
  simp only [CollatzResearch.WordTrace]
  refine ⟨107441715051916913959075291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143255620069222551945433721 107441715051916913959075291)
  ·
    refine ⟨161162572577875370938612937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107441715051916913959075291 161162572577875370938612937)
    ·
      refine ⟨120871929433406528203959703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161162572577875370938612937 120871929433406528203959703)
      ·
        refine ⟨181307894150109792305939555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120871929433406528203959703 181307894150109792305939555)
        ·
          refine ⟨271961841225164688458909333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181307894150109792305939555 271961841225164688458909333)
          ·
            refine ⟨12748211307429594771511375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 271961841225164688458909333 12748211307429594771511375)
            ·
              refine ⟨19122316961144392157267063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12748211307429594771511375 19122316961144392157267063)
              ·
                refine ⟨28683475441716588235900595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19122316961144392157267063 28683475441716588235900595)
                ·
                  refine ⟨43025213162574882353850893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28683475441716588235900595 43025213162574882353850893)
                  ·
                    refine ⟨16134454935965580882694085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43025213162574882353850893 16134454935965580882694085)
                    ·
                      refine ⟨3025210300493546415505141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16134454935965580882694085 3025210300493546415505141)
                      ·
                        rfl

theorem cell23_5891576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_5891576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891576 prefixEnd_5891576 := by exact prefixLift 5891576
  have htrace : WordTrace (prefixWord ++ tailWord_5891576) baseStart_5891576 baseEnd_5891576 := by
    simpa [prefixWord, tailWord_5891576, baseEnd_5891576] using wordTrace_append hprefix tailTrace_5891576
  have hstable : (prefixWord ++ tailWord_5891576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891576).length < 2 ^ (prefixWord ++ tailWord_5891576).sum := by decide
  have hdescent : baseEnd_5891576 < baseStart_5891576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891603 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 3, 4]
def baseStart_5891603 : Nat := 118140960795 + 5891603 * 2 ^ 59
def prefixEnd_5891603 : Nat := 4983230072969 + 3 ^ 40 * 5891603 * 2
def baseEnd_5891603 : Nat := 1008408054823739269955839

theorem tailTrace_5891603 : CollatzResearch.WordTrace tailWord_5891603 prefixEnd_5891603 1008408054823739269955839 := by
  unfold tailWord_5891603
  simp only [CollatzResearch.WordTrace]
  refine ⟨214884414874736011529383463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143256276583157341019588975 214884414874736011529383463)
  ·
    refine ⟨322326622312104017294075195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214884414874736011529383463 322326622312104017294075195)
    ·
      refine ⟨483489933468156025941112793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322326622312104017294075195 483489933468156025941112793)
      ·
        refine ⟨362617450101117019455834595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483489933468156025941112793 362617450101117019455834595)
        ·
          refine ⟨543926175151675529183751893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362617450101117019455834595 543926175151675529183751893)
          ·
            refine ⟨12748269730117395215244185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 543926175151675529183751893 12748269730117395215244185)
            ·
              refine ⟨9561202297588046411433139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12748269730117395215244185 9561202297588046411433139)
              ·
                refine ⟨14341803446382069617149709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9561202297588046411433139 14341803446382069617149709)
                ·
                  refine ⟨5378176292393276106431141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14341803446382069617149709 5378176292393276106431141)
                  ·
                    refine ⟨1008408054823739269955839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378176292393276106431141 1008408054823739269955839)
                    ·
                      rfl

theorem cell23_5891603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 4].length) (baseStart_5891603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891603 prefixEnd_5891603 := by exact prefixLift 5891603
  have htrace : WordTrace (prefixWord ++ tailWord_5891603) baseStart_5891603 baseEnd_5891603 := by
    simpa [prefixWord, tailWord_5891603, baseEnd_5891603] using wordTrace_append hprefix tailTrace_5891603
  have hstable : (prefixWord ++ tailWord_5891603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891603).length < 2 ^ (prefixWord ++ tailWord_5891603).sum := by decide
  have hdescent : baseEnd_5891603 < baseStart_5891603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891637 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_5891637 : Nat := 118140960795 + 5891637 * 2 ^ 59
def prefixEnd_5891637 : Nat := 4983230072969 + 3 ^ 40 * 5891637 * 2
def baseEnd_5891637 : Nat := 1008413874271156892280787

theorem tailTrace_5891637 : CollatzResearch.WordTrace tailWord_5891637 prefixEnd_5891637 1008413874271156892280787 := by
  unfold tailWord_5891637
  simp only [CollatzResearch.WordTrace]
  refine ⟨214885654956612835336121165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143257103304408556890747443 214885654956612835336121165)
  ·
    refine ⟨80582120608729813251045437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214885654956612835336121165 80582120608729813251045437)
    ·
      refine ⟨30218295228273679969142039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80582120608729813251045437 30218295228273679969142039)
      ·
        refine ⟨45327442842410519953713059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30218295228273679969142039 45327442842410519953713059)
        ·
          refine ⟨67991164263615779930569589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45327442842410519953713059 67991164263615779930569589)
          ·
            refine ⟨6374171649713979368490899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67991164263615779930569589 6374171649713979368490899)
            ·
              refine ⟨9561257474570969052736349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374171649713979368490899 9561257474570969052736349)
              ·
                refine ⟨3585471552964113394776131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9561257474570969052736349 3585471552964113394776131)
                ·
                  refine ⟨5378207329446170092164197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585471552964113394776131 5378207329446170092164197)
                  ·
                    refine ⟨1008413874271156892280787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378207329446170092164197 1008413874271156892280787)
                    ·
                      rfl

theorem cell23_5891637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_5891637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891637 prefixEnd_5891637 := by exact prefixLift 5891637
  have htrace : WordTrace (prefixWord ++ tailWord_5891637) baseStart_5891637 baseEnd_5891637 := by
    simpa [prefixWord, tailWord_5891637, baseEnd_5891637] using wordTrace_append hprefix tailTrace_5891637
  have hstable : (prefixWord ++ tailWord_5891637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891637).length < 2 ^ (prefixWord ++ tailWord_5891637).sum := by decide
  have hdescent : baseEnd_5891637 < baseStart_5891637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891654 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_5891654 : Nat := 118140960795 + 5891654 * 2 ^ 59
def prefixEnd_5891654 : Nat := 4983230072969 + 3 ^ 40 * 5891654 * 2
def baseEnd_5891654 : Nat := 1008416783994865703443261

theorem tailTrace_5891654 : CollatzResearch.WordTrace tailWord_5891654 prefixEnd_5891654 1008416783994865703443261 := by
  unfold tailWord_5891654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715196093673476476234063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143257516665034164826326677 6715196093673476476234063)
  ·
    refine ⟨10072794140510214714351095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6715196093673476476234063 10072794140510214714351095)
    ·
      refine ⟨15109191210765322071526643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10072794140510214714351095 15109191210765322071526643)
      ·
        refine ⟨22663786816147983107289965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15109191210765322071526643 22663786816147983107289965)
        ·
          refine ⟨8498920056055493665233737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22663786816147983107289965 8498920056055493665233737)
          ·
            refine ⟨6374190042041620248925303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8498920056055493665233737 6374190042041620248925303)
            ·
              refine ⟨9561285063062430373387955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374190042041620248925303 9561285063062430373387955)
              ·
                refine ⟨14341927594593645560081933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9561285063062430373387955 14341927594593645560081933)
                ·
                  refine ⟨5378222847972617085030725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14341927594593645560081933 5378222847972617085030725)
                  ·
                    refine ⟨1008416783994865703443261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378222847972617085030725 1008416783994865703443261)
                    ·
                      rfl

theorem cell23_5891654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_5891654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891654 prefixEnd_5891654 := by exact prefixLift 5891654
  have htrace : WordTrace (prefixWord ++ tailWord_5891654) baseStart_5891654 baseEnd_5891654 := by
    simpa [prefixWord, tailWord_5891654, baseEnd_5891654] using wordTrace_append hprefix tailTrace_5891654
  have hstable : (prefixWord ++ tailWord_5891654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891654).length < 2 ^ (prefixWord ++ tailWord_5891654).sum := by decide
  have hdescent : baseEnd_5891654 < baseStart_5891654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891660 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_5891660 : Nat := 118140960795 + 5891660 * 2 ^ 59
def prefixEnd_5891660 : Nat := 4983230072969 + 3 ^ 40 * 5891660 * 2
def baseEnd_5891660 : Nat := 3025253432868524086854755

theorem tailTrace_5891660 : CollatzResearch.WordTrace tailWord_5891660 prefixEnd_5891660 3025253432868524086854755 := by
  unfold tailWord_5891660
  simp only [CollatzResearch.WordTrace]
  refine ⟨107443246917764755132104217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143257662557019673509472289 107443246917764755132104217)
  ·
    refine ⟨80582435188323566349078163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107443246917764755132104217 80582435188323566349078163)
    ·
      refine ⟨120873652782485349523617245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80582435188323566349078163 120873652782485349523617245)
      ·
        refine ⟨45327619793432006071356467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120873652782485349523617245 45327619793432006071356467)
        ·
          refine ⟨67991429690148009107034701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45327619793432006071356467 67991429690148009107034701)
          ·
            refine ⟨25496786133805503415138013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67991429690148009107034701 25496786133805503415138013)
            ·
              refine ⟨9561294800177063780676755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25496786133805503415138013 9561294800177063780676755)
              ·
                refine ⟨14341942200265595671015133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9561294800177063780676755 14341942200265595671015133)
                ·
                  refine ⟨5378228325099598376630675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14341942200265595671015133 5378228325099598376630675)
                  ·
                    refine ⟨8067342487649397564946013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5378228325099598376630675 8067342487649397564946013)
                    ·
                      refine ⟨3025253432868524086854755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8067342487649397564946013 3025253432868524086854755)
                      ·
                        rfl

theorem cell23_5891660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_5891660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891660 prefixEnd_5891660 := by exact prefixLift 5891660
  have htrace : WordTrace (prefixWord ++ tailWord_5891660) baseStart_5891660 baseEnd_5891660 := by
    simpa [prefixWord, tailWord_5891660, baseEnd_5891660] using wordTrace_append hprefix tailTrace_5891660
  have hstable : (prefixWord ++ tailWord_5891660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891660).length < 2 ^ (prefixWord ++ tailWord_5891660).sum := by decide
  have hdescent : baseEnd_5891660 < baseStart_5891660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891683 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5891683 : Nat := 118140960795 + 5891683 * 2 ^ 59
def prefixEnd_5891683 : Nat := 4983230072969 + 3 ^ 40 * 5891683 * 2
def baseEnd_5891683 : Nat := 3025265242923577496867149

theorem tailTrace_5891683 : CollatzResearch.WordTrace tailWord_5891683 prefixEnd_5891683 3025265242923577496867149 := by
  unfold tailWord_5891683
  simp only [CollatzResearch.WordTrace]
  refine ⟨214887332714446185192295703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143258221809630790128197135 214887332714446185192295703)
  ·
    refine ⟨322330999071669277788443555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214887332714446185192295703 322330999071669277788443555)
    ·
      refine ⟨483496498607503916682665333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322330999071669277788443555 483496498607503916682665333)
      ·
        refine ⟨45327796744453492188999875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 483496498607503916682665333 45327796744453492188999875)
        ·
          refine ⟨67991695116680238283499813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45327796744453492188999875 67991695116680238283499813)
          ·
            refine ⟨12748442834377544678156215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67991695116680238283499813 12748442834377544678156215)
            ·
              refine ⟨19122664251566317017234323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12748442834377544678156215 19122664251566317017234323)
              ·
                refine ⟨28683996377349475525851485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19122664251566317017234323 28683996377349475525851485)
                ·
                  refine ⟨10756498641506053322194307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28683996377349475525851485 10756498641506053322194307)
                  ·
                    refine ⟨16134747962259079983291461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10756498641506053322194307 16134747962259079983291461)
                    ·
                      refine ⟨3025265242923577496867149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16134747962259079983291461 3025265242923577496867149)
                      ·
                        rfl

theorem cell23_5891683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5891683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891683 prefixEnd_5891683 := by exact prefixLift 5891683
  have htrace : WordTrace (prefixWord ++ tailWord_5891683) baseStart_5891683 baseEnd_5891683 := by
    simpa [prefixWord, tailWord_5891683, baseEnd_5891683] using wordTrace_append hprefix tailTrace_5891683
  have hstable : (prefixWord ++ tailWord_5891683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891683).length < 2 ^ (prefixWord ++ tailWord_5891683).sum := by decide
  have hdescent : baseEnd_5891683 < baseStart_5891683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891740 : List Nat := [2, 2, 3, 2, 3, 1, 3, 7]
def baseStart_5891740 : Nat := 118140960795 + 5891740 * 2 ^ 59
def prefixEnd_5891740 : Nat := 4983230072969 + 3 ^ 40 * 5891740 * 2
def baseEnd_5891740 : Nat := 112047944863736436068681

theorem tailTrace_5891740 : CollatzResearch.WordTrace tailWord_5891740 prefixEnd_5891740 112047944863736436068681 := by
  unfold tailWord_5891740
  simp only [CollatzResearch.WordTrace]
  refine ⟨107444705837619841963560337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143259607783493122618080449 107444705837619841963560337)
  ·
    refine ⟨80583529378214881472670253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107444705837619841963560337 80583529378214881472670253)
    ·
      refine ⟨30218823516830580552251345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80583529378214881472670253 30218823516830580552251345)
      ·
        refine ⟨22664117637622935414188509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30218823516830580552251345 22664117637622935414188509)
        ·
          refine ⟨8499044114108600780320691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22664117637622935414188509 8499044114108600780320691)
          ·
            refine ⟨12748566171162901170481037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499044114108600780320691 12748566171162901170481037)
            ·
              refine ⟨4780712314186087938930389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12748566171162901170481037 4780712314186087938930389)
              ·
                refine ⟨112047944863736436068681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4780712314186087938930389 112047944863736436068681)
                ·
                  rfl

theorem cell23_5891740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 7].length) (baseStart_5891740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891740 prefixEnd_5891740 := by exact prefixLift 5891740
  have htrace : WordTrace (prefixWord ++ tailWord_5891740) baseStart_5891740 baseEnd_5891740 := by
    simpa [prefixWord, tailWord_5891740, baseEnd_5891740] using wordTrace_append hprefix tailTrace_5891740
  have hstable : (prefixWord ++ tailWord_5891740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891740).length < 2 ^ (prefixWord ++ tailWord_5891740).sum := by decide
  have hdescent : baseEnd_5891740 < baseStart_5891740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891767 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_5891767 : Nat := 118140960795 + 5891767 * 2 ^ 59
def prefixEnd_5891767 : Nat := 4983230072969 + 3 ^ 40 * 5891767 * 2
def baseEnd_5891767 : Nat := 3025308375298555168216763

theorem tailTrace_5891767 : CollatzResearch.WordTrace tailWord_5891767 prefixEnd_5891767 3025308375298555168216763 := by
  unfold tailWord_5891767
  simp only [CollatzResearch.WordTrace]
  refine ⟨214890396446141867538353555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143260264297427911692235703 214890396446141867538353555)
  ·
    refine ⟨322335594669212801307530333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214890396446141867538353555 322335594669212801307530333)
    ·
      refine ⟨120875848000954800490323875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322335594669212801307530333 120875848000954800490323875)
      ·
        refine ⟨181313772001432200735485813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120875848000954800490323875 181313772001432200735485813)
        ·
          refine ⟨16998166125134268818951795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181313772001432200735485813 16998166125134268818951795)
          ·
            refine ⟨25497249187701403228427693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16998166125134268818951795 25497249187701403228427693)
            ·
              refine ⟨9561468445388026210660385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25497249187701403228427693 9561468445388026210660385)
              ·
                refine ⟨7171101334041019657995289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9561468445388026210660385 7171101334041019657995289)
                ·
                  refine ⟨5378326000530764743496467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7171101334041019657995289 5378326000530764743496467)
                  ·
                    refine ⟨8067489000796147115244701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5378326000530764743496467 8067489000796147115244701)
                    ·
                      refine ⟨3025308375298555168216763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8067489000796147115244701 3025308375298555168216763)
                      ·
                        rfl

theorem cell23_5891767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_5891767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891767 prefixEnd_5891767 := by exact prefixLift 5891767
  have htrace : WordTrace (prefixWord ++ tailWord_5891767) baseStart_5891767 baseEnd_5891767 := by
    simpa [prefixWord, tailWord_5891767, baseEnd_5891767] using wordTrace_append hprefix tailTrace_5891767
  have hstable : (prefixWord ++ tailWord_5891767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891767).length < 2 ^ (prefixWord ++ tailWord_5891767).sum := by decide
  have hdescent : baseEnd_5891767 < baseStart_5891767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891778 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5891778 : Nat := 118140960795 + 5891778 * 2 ^ 59
def prefixEnd_5891778 : Nat := 4983230072969 + 3 ^ 40 * 5891778 * 2
def baseEnd_5891778 : Nat := 1008438007861918208393071

theorem tailTrace_5891778 : CollatzResearch.WordTrace tailWord_5891778 prefixEnd_5891778 1008438007861918208393071 := by
  unfold tailWord_5891778
  simp only [CollatzResearch.WordTrace]
  refine ⟨53722699412275504104250997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143260531766068010944669325 53722699412275504104250997)
  ·
    refine ⟨5036503069900828509773531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53722699412275504104250997 5036503069900828509773531)
    ·
      refine ⟨7554754604851242764660297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5036503069900828509773531 7554754604851242764660297)
      ·
        refine ⟨5666065953638432073495223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7554754604851242764660297 5666065953638432073495223)
        ·
          refine ⟨8499098930457648110242835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5666065953638432073495223 8499098930457648110242835)
          ·
            refine ⟨12748648395686472165364253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499098930457648110242835 12748648395686472165364253)
            ·
              refine ⟨4780743148382427062011595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12748648395686472165364253 4780743148382427062011595)
              ·
                refine ⟨7171114722573640593017393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780743148382427062011595 7171114722573640593017393)
                ·
                  refine ⟨5378336041930230444763045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7171114722573640593017393 5378336041930230444763045)
                  ·
                    refine ⟨1008438007861918208393071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378336041930230444763045 1008438007861918208393071)
                    ·
                      rfl

theorem cell23_5891778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5891778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891778 prefixEnd_5891778 := by exact prefixLift 5891778
  have htrace : WordTrace (prefixWord ++ tailWord_5891778) baseStart_5891778 baseEnd_5891778 := by
    simpa [prefixWord, tailWord_5891778, baseEnd_5891778] using wordTrace_append hprefix tailTrace_5891778
  have hstable : (prefixWord ++ tailWord_5891778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891778).length < 2 ^ (prefixWord ++ tailWord_5891778).sum := by decide
  have hdescent : baseEnd_5891778 < baseStart_5891778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891794 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_5891794 : Nat := 118140960795 + 5891794 * 2 ^ 59
def prefixEnd_5891794 : Nat := 4983230072969 + 3 ^ 40 * 5891794 * 2
def baseEnd_5891794 : Nat := 3025322239276226562579139

theorem tailTrace_5891794 : CollatzResearch.WordTrace tailWord_5891794 prefixEnd_5891794 3025322239276226562579139 := by
  unfold tailWord_5891794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53722845304261012787396609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143260920811362700766390957 53722845304261012787396609)
  ·
    refine ⟨40292133978195759590547457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53722845304261012787396609 40292133978195759590547457)
    ·
      refine ⟨30219100483646819692910593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40292133978195759590547457 30219100483646819692910593)
      ·
        refine ⟨22664325362735114769682945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30219100483646819692910593 22664325362735114769682945)
        ·
          refine ⟨16998244022051336077262209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22664325362735114769682945 16998244022051336077262209)
          ·
            refine ⟨12748683016538502057946657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16998244022051336077262209 12748683016538502057946657)
            ·
              refine ⟨9561512262403876543459993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12748683016538502057946657 9561512262403876543459993)
              ·
                refine ⟨7171134196802907407594995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9561512262403876543459993 7171134196802907407594995)
                ·
                  refine ⟨10756701295204361111392493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7171134196802907407594995 10756701295204361111392493)
                  ·
                    refine ⟨4033762985701635416772185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10756701295204361111392493 4033762985701635416772185)
                    ·
                      refine ⟨3025322239276226562579139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033762985701635416772185 3025322239276226562579139)
                      ·
                        rfl

theorem cell23_5891794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_5891794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891794 prefixEnd_5891794 := by exact prefixLift 5891794
  have htrace : WordTrace (prefixWord ++ tailWord_5891794) baseStart_5891794 baseEnd_5891794 := by
    simpa [prefixWord, tailWord_5891794, baseEnd_5891794] using wordTrace_append hprefix tailTrace_5891794
  have hstable : (prefixWord ++ tailWord_5891794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891794).length < 2 ^ (prefixWord ++ tailWord_5891794).sum := by decide
  have hdescent : baseEnd_5891794 < baseStart_5891794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891830 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_5891830 : Nat := 118140960795 + 5891830 * 2 ^ 59
def prefixEnd_5891830 : Nat := 4983230072969 + 3 ^ 40 * 5891830 * 2
def baseEnd_5891830 : Nat := 336148969397754269080997

theorem tailTrace_5891830 : CollatzResearch.WordTrace tailWord_5891830 prefixEnd_5891830 336148969397754269080997 := by
  unfold tailWord_5891830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13430793390307101831118559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143261796163275752865264629 13430793390307101831118559)
  ·
    refine ⟨20146190085460652746677839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13430793390307101831118559 20146190085460652746677839)
    ·
      refine ⟨30219285128190979120016759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20146190085460652746677839 30219285128190979120016759)
      ·
        refine ⟨45328927692286468680025139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30219285128190979120016759 45328927692286468680025139)
        ·
          refine ⟨67993391538429703020037709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45328927692286468680025139 67993391538429703020037709)
          ·
            refine ⟨25497521826911138632514141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67993391538429703020037709 25497521826911138632514141)
            ·
              refine ⟨9561570685091676987192803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25497521826911138632514141 9561570685091676987192803)
              ·
                refine ⟨14342356027637515480789205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9561570685091676987192803 14342356027637515480789205)
                ·
                  refine ⟨336148969397754269080997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14342356027637515480789205 336148969397754269080997)
                  ·
                    rfl

theorem cell23_5891830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_5891830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891830 prefixEnd_5891830 := by exact prefixLift 5891830
  have htrace : WordTrace (prefixWord ++ tailWord_5891830) baseStart_5891830 baseEnd_5891830 := by
    simpa [prefixWord, tailWord_5891830, baseEnd_5891830] using wordTrace_append hprefix tailTrace_5891830
  have hstable : (prefixWord ++ tailWord_5891830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891830).length < 2 ^ (prefixWord ++ tailWord_5891830).sum := by decide
  have hdescent : baseEnd_5891830 < baseStart_5891830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891900 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_5891900 : Nat := 118140960795 + 5891900 * 2 ^ 59
def prefixEnd_5891900 : Nat := 4983230072969 + 3 ^ 40 * 5891900 * 2
def baseEnd_5891900 : Nat := 3025376668225603147853651

theorem tailTrace_5891900 : CollatzResearch.WordTrace tailWord_5891900 prefixEnd_5891900 3025376668225603147853651 := by
  unfold tailWord_5891900
  simp only [CollatzResearch.WordTrace]
  refine ⟨107447623677330015626472577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143263498236440020835296769 107447623677330015626472577)
  ·
    refine ⟨80585717757997511719854433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107447623677330015626472577 80585717757997511719854433)
    ·
      refine ⟨60439288318498133789890825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80585717757997511719854433 60439288318498133789890825)
      ·
        refine ⟨45329466238873600342418119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60439288318498133789890825 45329466238873600342418119)
        ·
          refine ⟨67994199358310400513627179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45329466238873600342418119 67994199358310400513627179)
          ·
            refine ⟨101991299037465600770440769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67994199358310400513627179 101991299037465600770440769)
            ·
              refine ⟨76493474278099200577830577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101991299037465600770440769 76493474278099200577830577)
              ·
                refine ⟨57370105708574400433372933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76493474278099200577830577 57370105708574400433372933)
                ·
                  refine ⟨10756894820357700081257425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57370105708574400433372933 10756894820357700081257425)
                  ·
                    refine ⟨8067671115268275060943069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10756894820357700081257425 8067671115268275060943069)
                    ·
                      refine ⟨3025376668225603147853651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8067671115268275060943069 3025376668225603147853651)
                      ·
                        rfl

theorem cell23_5891900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_5891900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891900 prefixEnd_5891900 := by exact prefixLift 5891900
  have htrace : WordTrace (prefixWord ++ tailWord_5891900) baseStart_5891900 baseEnd_5891900 := by
    simpa [prefixWord, tailWord_5891900, baseEnd_5891900] using wordTrace_append hprefix tailTrace_5891900
  have hstable : (prefixWord ++ tailWord_5891900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891900).length < 2 ^ (prefixWord ++ tailWord_5891900).sum := by decide
  have hdescent : baseEnd_5891900 < baseStart_5891900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891924 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_5891924 : Nat := 118140960795 + 5891924 * 2 ^ 59
def prefixEnd_5891924 : Nat := 4983230072969 + 3 ^ 40 * 5891924 * 2
def baseEnd_5891924 : Nat := 1008462997253770351317847

theorem tailTrace_5891924 : CollatzResearch.WordTrace tailWord_5891924 prefixEnd_5891924 1008462997253770351317847 := by
  unfold tailWord_5891924
  simp only [CollatzResearch.WordTrace]
  refine ⟨107448061353286541675909413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143264081804382055567879217 107448061353286541675909413)
  ·
    refine ⟨20146511503741226564233015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107448061353286541675909413 20146511503741226564233015)
    ·
      refine ⟨30219767255611839846349523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20146511503741226564233015 30219767255611839846349523)
      ·
        refine ⟨45329650883417759769524285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30219767255611839846349523 45329650883417759769524285)
        ·
          refine ⟨16998619081281659913571607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45329650883417759769524285 16998619081281659913571607)
          ·
            refine ⟨25497928621922489870357411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16998619081281659913571607 25497928621922489870357411)
            ·
              refine ⟨38246892932883734805536117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25497928621922489870357411 38246892932883734805536117)
              ·
                refine ⟨3585646212457850138019011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38246892932883734805536117 3585646212457850138019011)
                ·
                  refine ⟨5378469318686775207028517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585646212457850138019011 5378469318686775207028517)
                  ·
                    refine ⟨1008462997253770351317847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378469318686775207028517 1008462997253770351317847)
                    ·
                      rfl

theorem cell23_5891924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_5891924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891924 prefixEnd_5891924 := by exact prefixLift 5891924
  have htrace : WordTrace (prefixWord ++ tailWord_5891924) baseStart_5891924 baseEnd_5891924 := by
    simpa [prefixWord, tailWord_5891924, baseEnd_5891924] using wordTrace_append hprefix tailTrace_5891924
  have hstable : (prefixWord ++ tailWord_5891924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891924).length < 2 ^ (prefixWord ++ tailWord_5891924).sum := by decide
  have hdescent : baseEnd_5891924 < baseStart_5891924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891957 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_5891957 : Nat := 118140960795 + 5891957 * 2 ^ 59
def prefixEnd_5891957 : Nat := 4983230072969 + 3 ^ 40 * 5891957 * 2
def baseEnd_5891957 : Nat := 3025405936622909424840889

theorem tailTrace_5891957 : CollatzResearch.WordTrace tailWord_5891957 prefixEnd_5891957 3025405936622909424840889 := by
  unfold tailWord_5891957
  simp only [CollatzResearch.WordTrace]
  refine ⟨214897326315453529987770125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143264884210302353325180083 214897326315453529987770125)
  ·
    refine ⟨80586497368295073745413797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214897326315453529987770125 80586497368295073745413797)
    ·
      refine ⟨15109968256555326327265087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80586497368295073745413797 15109968256555326327265087)
      ·
        refine ⟨22664952384832989490897631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15109968256555326327265087 22664952384832989490897631)
        ·
          refine ⟨33997428577249484236346447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22664952384832989490897631 33997428577249484236346447)
          ·
            refine ⟨50996142865874226354519671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33997428577249484236346447 50996142865874226354519671)
            ·
              refine ⟨76494214298811339531779507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50996142865874226354519671 76494214298811339531779507)
              ·
                refine ⟨114741321448217009297669261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76494214298811339531779507 114741321448217009297669261)
                ·
                  refine ⟨43027995543081378486625973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114741321448217009297669261 43027995543081378486625973)
                  ·
                    refine ⟨4033874582163879233121185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43027995543081378486625973 4033874582163879233121185)
                    ·
                      refine ⟨3025405936622909424840889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033874582163879233121185 3025405936622909424840889)
                      ·
                        rfl

theorem cell23_5891957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_5891957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891957 prefixEnd_5891957 := by exact prefixLift 5891957
  have htrace : WordTrace (prefixWord ++ tailWord_5891957) baseStart_5891957 baseEnd_5891957 := by
    simpa [prefixWord, tailWord_5891957, baseEnd_5891957] using wordTrace_append hprefix tailTrace_5891957
  have hstable : (prefixWord ++ tailWord_5891957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891957).length < 2 ^ (prefixWord ++ tailWord_5891957).sum := by decide
  have hdescent : baseEnd_5891957 < baseStart_5891957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891993 : List Nat := [1, 2, 1, 2, 1, 3, 13]
def baseStart_5891993 : Nat := 118140960795 + 5891993 * 2 ^ 59
def prefixEnd_5891993 : Nat := 4983230072969 + 3 ^ 40 * 5891993 * 2
def baseEnd_5891993 : Nat := 37350918789215694864083

theorem tailTrace_5891993 : CollatzResearch.WordTrace tailWord_5891993 prefixEnd_5891993 37350918789215694864083 := by
  unfold tailWord_5891993
  simp only [CollatzResearch.WordTrace]
  refine ⟨214898639343323108136080633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143265759562215405424053755 214898639343323108136080633)
  ·
    refine ⟨161173979507492331102060475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214898639343323108136080633 161173979507492331102060475)
    ·
      refine ⟨241760969261238496653090713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161173979507492331102060475 241760969261238496653090713)
      ·
        refine ⟨181320726945928872489818035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241760969261238496653090713 181320726945928872489818035)
        ·
          refine ⟨271981090418893308734727053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181320726945928872489818035 271981090418893308734727053)
          ·
            refine ⟨101992908907084990775522645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271981090418893308734727053 101992908907084990775522645)
            ·
              refine ⟨37350918789215694864083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 101992908907084990775522645 37350918789215694864083)
              ·
                rfl

theorem cell23_5891993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 13].length) (baseStart_5891993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891993 prefixEnd_5891993 := by exact prefixLift 5891993
  have htrace : WordTrace (prefixWord ++ tailWord_5891993) baseStart_5891993 baseEnd_5891993 := by
    simpa [prefixWord, tailWord_5891993, baseEnd_5891993] using wordTrace_append hprefix tailTrace_5891993
  have hstable : (prefixWord ++ tailWord_5891993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891993).length < 2 ^ (prefixWord ++ tailWord_5891993).sum := by decide
  have hdescent : baseEnd_5891993 < baseStart_5891993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891997 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_5891997 : Nat := 118140960795 + 5891997 * 2 ^ 59
def prefixEnd_5891997 : Nat := 4983230072969 + 3 ^ 40 * 5891997 * 2
def baseEnd_5891997 : Nat := 1008475491949696422780235

theorem tailTrace_5891997 : CollatzResearch.WordTrace tailWord_5891997 prefixEnd_5891997 1008475491949696422780235 := by
  unfold tailWord_5891997
  simp only [CollatzResearch.WordTrace]
  refine ⟨214898785235308616819226245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143265856823539077879484163 214898785235308616819226245)
  ·
    refine ⟨40293522231620365653604921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214898785235308616819226245 40293522231620365653604921)
    ·
      refine ⟨30220141673715274240203691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40293522231620365653604921 30220141673715274240203691)
      ·
        refine ⟨45330212510572911360305537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30220141673715274240203691 45330212510572911360305537)
        ·
          refine ⟨33997659382929683520229153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45330212510572911360305537 33997659382929683520229153)
          ·
            refine ⟨25498244537197262640171865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33997659382929683520229153 25498244537197262640171865)
            ·
              refine ⟨19123683402897946980128899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25498244537197262640171865 19123683402897946980128899)
              ·
                refine ⟨28685525104346920470193349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19123683402897946980128899 28685525104346920470193349)
                ·
                  refine ⟨5378535957065047588161253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28685525104346920470193349 5378535957065047588161253)
                  ·
                    refine ⟨1008475491949696422780235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378535957065047588161253 1008475491949696422780235)
                    ·
                      rfl

theorem cell23_5891997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_5891997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891997 prefixEnd_5891997 := by exact prefixLift 5891997
  have htrace : WordTrace (prefixWord ++ tailWord_5891997) baseStart_5891997 baseEnd_5891997 := by
    simpa [prefixWord, tailWord_5891997, baseEnd_5891997] using wordTrace_append hprefix tailTrace_5891997
  have hstable : (prefixWord ++ tailWord_5891997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891997).length < 2 ^ (prefixWord ++ tailWord_5891997).sum := by decide
  have hdescent : baseEnd_5891997 < baseStart_5891997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892007 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5892007 : Nat := 118140960795 + 5892007 * 2 ^ 59
def prefixEnd_5892007 : Nat := 4983230072969 + 3 ^ 40 * 5892007 * 2
def baseEnd_5892007 : Nat := 3025431610655634229215659

theorem tailTrace_5892007 : CollatzResearch.WordTrace tailWord_5892007 prefixEnd_5892007 3025431610655634229215659 := by
  unfold tailWord_5892007
  simp only [CollatzResearch.WordTrace]
  refine ⟨214899149965272388527090275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143266099976848259018060183 214899149965272388527090275)
  ·
    refine ⟨322348724947908582790635413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214899149965272388527090275 322348724947908582790635413)
    ·
      refine ⟨15110096481933214818311035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 322348724947908582790635413 15110096481933214818311035)
      ·
        refine ⟨22665144722899822227466553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15110096481933214818311035 22665144722899822227466553)
        ·
          refine ⟨16998858542174866670599915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22665144722899822227466553 16998858542174866670599915)
          ·
            refine ⟨25498287813262300005899873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16998858542174866670599915 25498287813262300005899873)
            ·
              refine ⟨19123715859946725004424905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25498287813262300005899873 19123715859946725004424905)
              ·
                refine ⟨14342786894960043753318679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19123715859946725004424905 14342786894960043753318679)
                ·
                  refine ⟨21514180342440065629978019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14342786894960043753318679 21514180342440065629978019)
                  ·
                    refine ⟨32271270513660098444967029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21514180342440065629978019 32271270513660098444967029)
                    ·
                      refine ⟨3025431610655634229215659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32271270513660098444967029 3025431610655634229215659)
                      ·
                        rfl

theorem cell23_5892007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5892007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892007 prefixEnd_5892007 := by exact prefixLift 5892007
  have htrace : WordTrace (prefixWord ++ tailWord_5892007) baseStart_5892007 baseEnd_5892007 := by
    simpa [prefixWord, tailWord_5892007, baseEnd_5892007] using wordTrace_append hprefix tailTrace_5892007
  have hstable : (prefixWord ++ tailWord_5892007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892007).length < 2 ^ (prefixWord ++ tailWord_5892007).sum := by decide
  have hdescent : baseEnd_5892007 < baseStart_5892007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892037 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_5892037 : Nat := 118140960795 + 5892037 * 2 ^ 59
def prefixEnd_5892037 : Nat := 4983230072969 + 3 ^ 40 * 5892037 * 2
def baseEnd_5892037 : Nat := 3025447015075269111840521

theorem tailTrace_5892037 : CollatzResearch.WordTrace tailWord_5892037 prefixEnd_5892037 3025447015075269111840521 := by
  unfold tailWord_5892037
  simp only [CollatzResearch.WordTrace]
  refine ⟨214900244155163703650682365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143266829436775802433788243 214900244155163703650682365)
  ·
    refine ⟨80587591558186388869005887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214900244155163703650682365 80587591558186388869005887)
    ·
      refine ⟨120881387337279583303508831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80587591558186388869005887 120881387337279583303508831)
      ·
        refine ⟨181322081005919374955263247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120881387337279583303508831 181322081005919374955263247)
        ·
          refine ⟨271983121508879062432894871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181322081005919374955263247 271983121508879062432894871)
          ·
            refine ⟨407974682263318593649342307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271983121508879062432894871 407974682263318593649342307)
            ·
              refine ⟨611962023394977890474013461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407974682263318593649342307 611962023394977890474013461)
              ·
                refine ⟨28685719846639588615969381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 611962023394977890474013461 28685719846639588615969381)
                ·
                  refine ⟨5378572471244922865494259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28685719846639588615969381 5378572471244922865494259)
                  ·
                    refine ⟨8067858706867384298241389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5378572471244922865494259 8067858706867384298241389)
                    ·
                      refine ⟨3025447015075269111840521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8067858706867384298241389 3025447015075269111840521)
                      ·
                        rfl

theorem cell23_5892037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_5892037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892037 prefixEnd_5892037 := by exact prefixLift 5892037
  have htrace : WordTrace (prefixWord ++ tailWord_5892037) baseStart_5892037 baseEnd_5892037 := by
    simpa [prefixWord, tailWord_5892037, baseEnd_5892037] using wordTrace_append hprefix tailTrace_5892037
  have hstable : (prefixWord ++ tailWord_5892037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892037).length < 2 ^ (prefixWord ++ tailWord_5892037).sum := by decide
  have hdescent : baseEnd_5892037 < baseStart_5892037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892080 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_5892080 : Nat := 118140960795 + 5892080 * 2 ^ 59
def prefixEnd_5892080 : Nat := 4983230072969 + 3 ^ 40 * 5892080 * 2
def baseEnd_5892080 : Nat := 3025469094743412443602823

theorem tailTrace_5892080 : CollatzResearch.WordTrace tailWord_5892080 prefixEnd_5892080 3025469094743412443602823 := by
  unfold tailWord_5892080
  simp only [CollatzResearch.WordTrace]
  refine ⟨107450906247003960997248847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143267874996005281329665129 107450906247003960997248847)
  ·
    refine ⟨161176359370505941495873271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107450906247003960997248847 161176359370505941495873271)
    ·
      refine ⟨241764539055758912243809907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161176359370505941495873271 241764539055758912243809907)
      ·
        refine ⟨362646808583638368365714861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241764539055758912243809907 362646808583638368365714861)
        ·
          refine ⟨135992553218864388137143073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362646808583638368365714861 135992553218864388137143073)
          ·
            refine ⟨101994414914148291102857305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135992553218864388137143073 101994414914148291102857305)
            ·
              refine ⟨76495811185611218327142979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101994414914148291102857305 76495811185611218327142979)
              ·
                refine ⟨114743716778416827490714469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76495811185611218327142979 114743716778416827490714469)
                ·
                  refine ⟨21514446895953155154508963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114743716778416827490714469 21514446895953155154508963)
                  ·
                    refine ⟨32271670343929732731763445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21514446895953155154508963 32271670343929732731763445)
                    ·
                      refine ⟨3025469094743412443602823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32271670343929732731763445 3025469094743412443602823)
                      ·
                        rfl

theorem cell23_5892080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_5892080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892080 prefixEnd_5892080 := by exact prefixLift 5892080
  have htrace : WordTrace (prefixWord ++ tailWord_5892080) baseStart_5892080 baseEnd_5892080 := by
    simpa [prefixWord, tailWord_5892080, baseEnd_5892080] using wordTrace_append hprefix tailTrace_5892080
  have hstable : (prefixWord ++ tailWord_5892080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892080).length < 2 ^ (prefixWord ++ tailWord_5892080).sum := by decide
  have hdescent : baseEnd_5892080 < baseStart_5892080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892127 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_5892127 : Nat := 118140960795 + 5892127 * 2 ^ 59
def prefixEnd_5892127 : Nat := 4983230072969 + 3 ^ 40 * 5892127 * 2
def baseEnd_5892127 : Nat := 3025493228334173759715107

theorem tailTrace_5892127 : CollatzResearch.WordTrace tailWord_5892127 prefixEnd_5892127 3025493228334173759715107 := by
  unfold tailWord_5892127
  simp only [CollatzResearch.WordTrace]
  refine ⟨214903526724837649021458635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143269017816558432680972423 214903526724837649021458635)
  ·
    refine ⟨322355290087256473532187953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214903526724837649021458635 322355290087256473532187953)
    ·
      refine ⟨241766467565442355149140965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322355290087256473532187953 241766467565442355149140965)
      ·
        refine ⟨45331212668520441590463931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241766467565442355149140965 45331212668520441590463931)
        ·
          refine ⟨67996819002780662385695897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45331212668520441590463931 67996819002780662385695897)
          ·
            refine ⟨50997614252085496789271923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67996819002780662385695897 50997614252085496789271923)
            ·
              refine ⟨76496421378128245183907885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50997614252085496789271923 76496421378128245183907885)
              ·
                refine ⟨28686158016798091943965457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76496421378128245183907885 28686158016798091943965457)
                ·
                  refine ⟨21514618512598568957974093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28686158016798091943965457 21514618512598568957974093)
                  ·
                    refine ⟨8067981942224463359240285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21514618512598568957974093 8067981942224463359240285)
                    ·
                      refine ⟨3025493228334173759715107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8067981942224463359240285 3025493228334173759715107)
                      ·
                        rfl

theorem cell23_5892127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_5892127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892127 prefixEnd_5892127 := by exact prefixLift 5892127
  have htrace : WordTrace (prefixWord ++ tailWord_5892127) baseStart_5892127 baseEnd_5892127 := by
    simpa [prefixWord, tailWord_5892127, baseEnd_5892127] using wordTrace_append hprefix tailTrace_5892127
  have hstable : (prefixWord ++ tailWord_5892127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892127).length < 2 ^ (prefixWord ++ tailWord_5892127).sum := by decide
  have hdescent : baseEnd_5892127 < baseStart_5892127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892137 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 7, 2]
def baseStart_5892137 : Nat := 118140960795 + 5892137 * 2 ^ 59
def prefixEnd_5892137 : Nat := 4983230072969 + 3 ^ 40 * 5892137 * 2
def baseEnd_5892137 : Nat := 3025498363140718720590061

theorem tailTrace_5892137 : CollatzResearch.WordTrace tailWord_5892137 prefixEnd_5892137 3025498363140718720590061 := by
  unfold tailWord_5892137
  simp only [CollatzResearch.WordTrace]
  refine ⟨214903891454801420729322665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143269260969867613819548443 214903891454801420729322665)
  ·
    refine ⟨161177918591101065546991999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214903891454801420729322665 161177918591101065546991999)
    ·
      refine ⟨241766877886651598320487999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161177918591101065546991999 241766877886651598320487999)
      ·
        refine ⟨362650316829977397480731999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241766877886651598320487999 362650316829977397480731999)
        ·
          refine ⟨543975475244966096221097999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362650316829977397480731999 543975475244966096221097999)
          ·
            refine ⟨815963212867449144331646999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543975475244966096221097999 815963212867449144331646999)
            ·
              refine ⟨1223944819301173716497470499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815963212867449144331646999 1223944819301173716497470499)
              ·
                refine ⟨1835917228951760574746205749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223944819301173716497470499 1835917228951760574746205749)
                ·
                  refine ⟨172117240214227553882456789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1835917228951760574746205749 172117240214227553882456789)
                  ·
                    refine ⟨4033997817520958294120081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 172117240214227553882456789 4033997817520958294120081)
                    ·
                      refine ⟨3025498363140718720590061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033997817520958294120081 3025498363140718720590061)
                      ·
                        rfl

theorem cell23_5892137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 7, 2].length) (baseStart_5892137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892137 prefixEnd_5892137 := by exact prefixLift 5892137
  have htrace : WordTrace (prefixWord ++ tailWord_5892137) baseStart_5892137 baseEnd_5892137 := by
    simpa [prefixWord, tailWord_5892137, baseEnd_5892137] using wordTrace_append hprefix tailTrace_5892137
  have hstable : (prefixWord ++ tailWord_5892137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892137).length < 2 ^ (prefixWord ++ tailWord_5892137).sum := by decide
  have hdescent : baseEnd_5892137 < baseStart_5892137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892140 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_5892140 : Nat := 118140960795 + 5892140 * 2 ^ 59
def prefixEnd_5892140 : Nat := 4983230072969 + 3 ^ 40 * 5892140 * 2
def baseEnd_5892140 : Nat := 3025499903582682208852547

theorem tailTrace_5892140 : CollatzResearch.WordTrace tailWord_5892140 prefixEnd_5892140 3025499903582682208852547 := by
  unfold tailWord_5892140
  simp only [CollatzResearch.WordTrace]
  refine ⟨107452000436895276120840937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143269333915860368161121249 107452000436895276120840937)
  ·
    refine ⟨80589000327671457090630703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107452000436895276120840937 80589000327671457090630703)
    ·
      refine ⟨120883500491507185635946055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80589000327671457090630703 120883500491507185635946055)
      ·
        refine ⟨181325250737260778453919083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120883500491507185635946055 181325250737260778453919083)
        ·
          refine ⟨271987876105891167680878625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181325250737260778453919083 271987876105891167680878625)
          ·
            refine ⟨203990907079418375760658969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271987876105891167680878625 203990907079418375760658969)
            ·
              refine ⟨152993180309563781820494227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203990907079418375760658969 152993180309563781820494227)
              ·
                refine ⟨229489770464345672730741341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152993180309563781820494227 229489770464345672730741341)
                ·
                  refine ⟨86058663924129627274028003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229489770464345672730741341 86058663924129627274028003)
                  ·
                    refine ⟨129087995886194440911042005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86058663924129627274028003 129087995886194440911042005)
                    ·
                      refine ⟨3025499903582682208852547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129087995886194440911042005 3025499903582682208852547)
                      ·
                        rfl

theorem cell23_5892140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_5892140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892140 prefixEnd_5892140 := by exact prefixLift 5892140
  have htrace : WordTrace (prefixWord ++ tailWord_5892140) baseStart_5892140 baseEnd_5892140 := by
    simpa [prefixWord, tailWord_5892140, baseEnd_5892140] using wordTrace_append hprefix tailTrace_5892140
  have hstable : (prefixWord ++ tailWord_5892140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892140).length < 2 ^ (prefixWord ++ tailWord_5892140).sum := by decide
  have hdescent : baseEnd_5892140 < baseStart_5892140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892157 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5892157 : Nat := 118140960795 + 5892157 * 2 ^ 59
def prefixEnd_5892157 : Nat := 4983230072969 + 3 ^ 40 * 5892157 * 2
def baseEnd_5892157 : Nat := 3025508632753808642339969

theorem tailTrace_5892157 : CollatzResearch.WordTrace tailWord_5892157 prefixEnd_5892157 3025508632753808642339969 := by
  unfold tailWord_5892157
  simp only [CollatzResearch.WordTrace]
  refine ⟨214904620914728964145050725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143269747276485976096700483 214904620914728964145050725)
  ·
    refine ⟨40294616421511680777197011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214904620914728964145050725 40294616421511680777197011)
    ·
      refine ⟨60441924632267521165795517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40294616421511680777197011 60441924632267521165795517)
      ·
        refine ⟨22665721737100320437173319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60441924632267521165795517 22665721737100320437173319)
        ·
          refine ⟨33998582605650480655759979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22665721737100320437173319 33998582605650480655759979)
          ·
            refine ⟨50997873908475720983639969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33998582605650480655759979 50997873908475720983639969)
            ·
              refine ⟨38248405431356790737729977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50997873908475720983639969 38248405431356790737729977)
              ·
                refine ⟨28686304073517593053297483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38248405431356790737729977 28686304073517593053297483)
                ·
                  refine ⟨43029456110276389579946225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28686304073517593053297483 43029456110276389579946225)
                  ·
                    refine ⟨32272092082707292184959669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43029456110276389579946225 32272092082707292184959669)
                    ·
                      refine ⟨3025508632753808642339969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32272092082707292184959669 3025508632753808642339969)
                      ·
                        rfl

theorem cell23_5892157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5892157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892157 prefixEnd_5892157 := by exact prefixLift 5892157
  have htrace : WordTrace (prefixWord ++ tailWord_5892157) baseStart_5892157 baseEnd_5892157 := by
    simpa [prefixWord, tailWord_5892157, baseEnd_5892157] using wordTrace_append hprefix tailTrace_5892157
  have hstable : (prefixWord ++ tailWord_5892157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892157).length < 2 ^ (prefixWord ++ tailWord_5892157).sum := by decide
  have hdescent : baseEnd_5892157 < baseStart_5892157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892204 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_5892204 : Nat := 118140960795 + 5892204 * 2 ^ 59
def prefixEnd_5892204 : Nat := 4983230072969 + 3 ^ 40 * 5892204 * 2
def baseEnd_5892204 : Nat := 3025532766344569958452253

theorem tailTrace_5892204 : CollatzResearch.WordTrace tailWord_5892204 prefixEnd_5892204 3025532766344569958452253 := by
  unfold tailWord_5892204
  simp only [CollatzResearch.WordTrace]
  refine ⟨107453167572779345586005833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143270890097039127448007777 107453167572779345586005833)
  ·
    refine ⟨80589875679584509189504375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107453167572779345586005833 80589875679584509189504375)
    ·
      refine ⟨120884813519376763784256563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80589875679584509189504375 120884813519376763784256563)
      ·
        refine ⟨181327220279065145676384845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120884813519376763784256563 181327220279065145676384845)
        ·
          refine ⟨67997707604649429628644317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181327220279065145676384845 67997707604649429628644317)
          ·
            refine ⟨25499140351743536110741619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67997707604649429628644317 25499140351743536110741619)
            ·
              refine ⟨38248710527615304166112429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25499140351743536110741619 38248710527615304166112429)
              ·
                refine ⟨14343266447855739062292161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38248710527615304166112429 14343266447855739062292161)
                ·
                  refine ⟨10757449835891804296719121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14343266447855739062292161 10757449835891804296719121)
                  ·
                    refine ⟨8068087376918853222539341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10757449835891804296719121 8068087376918853222539341)
                    ·
                      refine ⟨3025532766344569958452253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8068087376918853222539341 3025532766344569958452253)
                      ·
                        rfl

theorem cell23_5892204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_5892204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892204 prefixEnd_5892204 := by exact prefixLift 5892204
  have htrace : WordTrace (prefixWord ++ tailWord_5892204) baseStart_5892204 baseEnd_5892204 := by
    simpa [prefixWord, tailWord_5892204, baseEnd_5892204] using wordTrace_append hprefix tailTrace_5892204
  have hstable : (prefixWord ++ tailWord_5892204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892204).length < 2 ^ (prefixWord ++ tailWord_5892204).sum := by decide
  have hdescent : baseEnd_5892204 < baseStart_5892204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892287 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_5892287 : Nat := 118140960795 + 5892287 * 2 ^ 59
def prefixEnd_5892287 : Nat := 4983230072969 + 3 ^ 40 * 5892287 * 2
def baseEnd_5892287 : Nat := 3025575385238893133714371

theorem tailTrace_5892287 : CollatzResearch.WordTrace tailWord_5892287 prefixEnd_5892287 3025575385238893133714371 := by
  unfold tailWord_5892287
  simp only [CollatzResearch.WordTrace]
  refine ⟨214909362404257996347283115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143272908269505330898188743 214909362404257996347283115)
  ·
    refine ⟨322364043606386994520924673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214909362404257996347283115 322364043606386994520924673)
    ·
      refine ⟨241773032704790245890693505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322364043606386994520924673 241773032704790245890693505)
      ·
        refine ⟨181329774528592684418020129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241773032704790245890693505 181329774528592684418020129)
        ·
          refine ⟨135997330896444513313515097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181329774528592684418020129 135997330896444513313515097)
          ·
            refine ⟨101997998172333384985136323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135997330896444513313515097 101997998172333384985136323)
            ·
              refine ⟨152996997258500077477704485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101997998172333384985136323 152996997258500077477704485)
              ·
                refine ⟨28686936985968764527069591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152996997258500077477704485 28686936985968764527069591)
                ·
                  refine ⟨43030405478953146790604387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28686936985968764527069591 43030405478953146790604387)
                  ·
                    refine ⟨64545608218429720185906581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43030405478953146790604387 64545608218429720185906581)
                    ·
                      refine ⟨3025575385238893133714371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64545608218429720185906581 3025575385238893133714371)
                      ·
                        rfl

theorem cell23_5892287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_5892287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892287 prefixEnd_5892287 := by exact prefixLift 5892287
  have htrace : WordTrace (prefixWord ++ tailWord_5892287) baseStart_5892287 baseEnd_5892287 := by
    simpa [prefixWord, tailWord_5892287, baseEnd_5892287] using wordTrace_append hprefix tailTrace_5892287
  have hstable : (prefixWord ++ tailWord_5892287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892287).length < 2 ^ (prefixWord ++ tailWord_5892287).sum := by decide
  have hdescent : baseEnd_5892287 < baseStart_5892287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892314 : List Nat := [3, 1, 1, 2, 2, 1, 6, 7]
def baseStart_5892314 : Nat := 118140960795 + 5892314 * 2 ^ 59
def prefixEnd_5892314 : Nat := 4983230072969 + 3 ^ 40 * 5892314 * 2
def baseEnd_5892314 : Nat := 112058861082094982521361

theorem tailTrace_5892314 : CollatzResearch.WordTrace tailWord_5892314 prefixEnd_5892314 112058861082094982521361 := by
  unfold tailWord_5892314
  simp only [CollatzResearch.WordTrace]
  refine ⟨53727586793790044989628999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143273564783440119972343997 53727586793790044989628999)
  ·
    refine ⟨80591380190685067484443499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53727586793790044989628999 80591380190685067484443499)
    ·
      refine ⟨120887070286027601226665249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80591380190685067484443499 120887070286027601226665249)
      ·
        refine ⟨90665302714520700919998937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120887070286027601226665249 90665302714520700919998937)
        ·
          refine ⟨67998977035890525689999203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90665302714520700919998937 67998977035890525689999203)
          ·
            refine ⟨101998465553835788534998805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67998977035890525689999203 101998465553835788534998805)
            ·
              refine ⟨4781178072836052587578069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101998465553835788534998805 4781178072836052587578069)
              ·
                refine ⟨112058861082094982521361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4781178072836052587578069 112058861082094982521361)
                ·
                  rfl

theorem cell23_5892314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_5892314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892314 prefixEnd_5892314 := by exact prefixLift 5892314
  have htrace : WordTrace (prefixWord ++ tailWord_5892314) baseStart_5892314 baseEnd_5892314 := by
    simpa [prefixWord, tailWord_5892314, baseEnd_5892314] using wordTrace_append hprefix tailTrace_5892314
  have hstable : (prefixWord ++ tailWord_5892314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892314).length < 2 ^ (prefixWord ++ tailWord_5892314).sum := by decide
  have hdescent : baseEnd_5892314 < baseStart_5892314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892324 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_5892324 : Nat := 118140960795 + 5892324 * 2 ^ 59
def prefixEnd_5892324 : Nat := 4983230072969 + 3 ^ 40 * 5892324 * 2
def baseEnd_5892324 : Nat := 3025594384023109488951701

theorem tailTrace_5892324 : CollatzResearch.WordTrace tailWord_5892324 prefixEnd_5892324 3025594384023109488951701 := by
  unfold tailWord_5892324
  simp only [CollatzResearch.WordTrace]
  refine ⟨107455355952561975833190013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143273807936749301110920017 107455355952561975833190013)
  ·
    refine ⟨40295758482210740937446255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107455355952561975833190013 40295758482210740937446255)
    ·
      refine ⟨60443637723316111406169383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40295758482210740937446255 60443637723316111406169383)
      ·
        refine ⟨90665456584974167109254075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60443637723316111406169383 90665456584974167109254075)
        ·
          refine ⟨135998184877461250663881113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90665456584974167109254075 135998184877461250663881113)
          ·
            refine ⟨101998638658095937997910835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135998184877461250663881113 101998638658095937997910835)
            ·
              refine ⟨152997957987143906996866253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101998638658095937997910835 152997957987143906996866253)
              ·
                refine ⟨57374234245178965123824845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152997957987143906996866253 57374234245178965123824845)
                ·
                  refine ⟨21515337841942111921434317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57374234245178965123824845 21515337841942111921434317)
                  ·
                    refine ⟨8068251690728291970537869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21515337841942111921434317 8068251690728291970537869)
                    ·
                      refine ⟨3025594384023109488951701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8068251690728291970537869 3025594384023109488951701)
                      ·
                        rfl

theorem cell23_5892324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_5892324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892324 prefixEnd_5892324 := by exact prefixLift 5892324
  have htrace : WordTrace (prefixWord ++ tailWord_5892324) baseStart_5892324 baseEnd_5892324 := by
    simpa [prefixWord, tailWord_5892324, baseEnd_5892324] using wordTrace_append hprefix tailTrace_5892324
  have hstable : (prefixWord ++ tailWord_5892324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892324).length < 2 ^ (prefixWord ++ tailWord_5892324).sum := by decide
  have hdescent : baseEnd_5892324 < baseStart_5892324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892351 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 3, 3, 2]
def baseStart_5892351 : Nat := 118140960795 + 5892351 * 2 ^ 59
def prefixEnd_5892351 : Nat := 4983230072969 + 3 ^ 40 * 5892351 * 2
def baseEnd_5892351 : Nat := 3025608248000780883314077

theorem tailTrace_5892351 : CollatzResearch.WordTrace tailWord_5892351 prefixEnd_5892351 3025608248000780883314077 := by
  unfold tailWord_5892351
  simp only [CollatzResearch.WordTrace]
  refine ⟨214911696676026135277612907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143274464450684090185075271 214911696676026135277612907)
  ·
    refine ⟨322367545014039202916419361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214911696676026135277612907 322367545014039202916419361)
    ·
      refine ⟨241775658760529402187314521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322367545014039202916419361 241775658760529402187314521)
      ·
        refine ⟨181331744070397051640485891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241775658760529402187314521 181331744070397051640485891)
        ·
          refine ⟨271997616105595577460728837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181331744070397051640485891 271997616105595577460728837)
          ·
            refine ⟨50999553019799170773886657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271997616105595577460728837 50999553019799170773886657)
            ·
              refine ⟨38249664764849378080414993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50999553019799170773886657 38249664764849378080414993)
              ·
                refine ⟨28687248573637033560311245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38249664764849378080414993 28687248573637033560311245)
                ·
                  refine ⟨10757718215113887585116717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28687248573637033560311245 10757718215113887585116717)
                  ·
                    refine ⟨4034144330667707844418769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10757718215113887585116717 4034144330667707844418769)
                    ·
                      refine ⟨3025608248000780883314077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034144330667707844418769 3025608248000780883314077)
                      ·
                        rfl

theorem cell23_5892351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_5892351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892351 prefixEnd_5892351 := by exact prefixLift 5892351
  have htrace : WordTrace (prefixWord ++ tailWord_5892351) baseStart_5892351 baseEnd_5892351 := by
    simpa [prefixWord, tailWord_5892351, baseEnd_5892351] using wordTrace_append hprefix tailTrace_5892351
  have hstable : (prefixWord ++ tailWord_5892351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892351).length < 2 ^ (prefixWord ++ tailWord_5892351).sum := by decide
  have hdescent : baseEnd_5892351 < baseStart_5892351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892471 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 6, 2]
def baseStart_5892471 : Nat := 118140960795 + 5892471 * 2 ^ 59
def prefixEnd_5892471 : Nat := 4983230072969 + 3 ^ 40 * 5892471 * 2
def baseEnd_5892471 : Nat := 3025669865679320413813525

theorem tailTrace_5892471 : CollatzResearch.WordTrace tailWord_5892471 prefixEnd_5892471 3025669865679320413813525 := by
  unfold tailWord_5892471
  simp only [CollatzResearch.WordTrace]
  refine ⟨214916073435591395771981267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143277382290394263847987511 214916073435591395771981267)
  ·
    refine ⟨322374110153387093657971901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214916073435591395771981267 322374110153387093657971901)
    ·
      refine ⟨120890291307520160121739463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322374110153387093657971901 120890291307520160121739463)
      ·
        refine ⟨181335436961280240182609195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120890291307520160121739463 181335436961280240182609195)
        ·
          refine ⟨272003155441920360273913793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181335436961280240182609195 272003155441920360273913793)
          ·
            refine ⟨204002366581440270205435345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272003155441920360273913793 204002366581440270205435345)
            ·
              refine ⟨153001774936080202654076509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204002366581440270205435345 153001774936080202654076509)
              ·
                refine ⟨57375665601030075995278691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153001774936080202654076509 57375665601030075995278691)
                ·
                  refine ⟨86063498401545113992918037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57375665601030075995278691 86063498401545113992918037)
                  ·
                    refine ⟨4034226487572427218418033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86063498401545113992918037 4034226487572427218418033)
                    ·
                      refine ⟨3025669865679320413813525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034226487572427218418033 3025669865679320413813525)
                      ·
                        rfl

theorem cell23_5892471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_5892471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892471 prefixEnd_5892471 := by exact prefixLift 5892471
  have htrace : WordTrace (prefixWord ++ tailWord_5892471) baseStart_5892471 baseEnd_5892471 := by
    simpa [prefixWord, tailWord_5892471, baseEnd_5892471] using wordTrace_append hprefix tailTrace_5892471
  have hstable : (prefixWord ++ tailWord_5892471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892471).length < 2 ^ (prefixWord ++ tailWord_5892471).sum := by decide
  have hdescent : baseEnd_5892471 < baseStart_5892471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892491 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 3]
def baseStart_5892491 : Nat := 118140960795 + 5892491 * 2 ^ 59
def prefixEnd_5892491 : Nat := 4983230072969 + 3 ^ 40 * 5892491 * 2
def baseEnd_5892491 : Nat := 3025680135292410335563433

theorem tailTrace_5892491 : CollatzResearch.WordTrace tailWord_5892491 prefixEnd_5892491 3025680135292410335563433 := by
  unfold tailWord_5892491
  simp only [CollatzResearch.WordTrace]
  refine ⟨214916802895518939187709327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143277868597012626125139551 214916802895518939187709327)
  ·
    refine ⟨322375204343278408781563991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214916802895518939187709327 322375204343278408781563991)
    ·
      refine ⟨483562806514917613172345987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322375204343278408781563991 483562806514917613172345987)
      ·
        refine ⟨725344209772376419758518981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483562806514917613172345987 725344209772376419758518981)
        ·
          refine ⟨136002039332320578704722309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 725344209772376419758518981 136002039332320578704722309)
          ·
            refine ⟨25500382374810108507135433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136002039332320578704722309 25500382374810108507135433)
            ·
              refine ⟨19125286781107581380351575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25500382374810108507135433 19125286781107581380351575)
              ·
                refine ⟨28687930171661372070527363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19125286781107581380351575 28687930171661372070527363)
                ·
                  refine ⟨43031895257492058105791045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28687930171661372070527363 43031895257492058105791045)
                  ·
                    refine ⟨8068480360779760894835821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43031895257492058105791045 8068480360779760894835821)
                    ·
                      refine ⟨3025680135292410335563433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8068480360779760894835821 3025680135292410335563433)
                      ·
                        rfl

theorem cell23_5892491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 3].length) (baseStart_5892491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892491 prefixEnd_5892491 := by exact prefixLift 5892491
  have htrace : WordTrace (prefixWord ++ tailWord_5892491) baseStart_5892491 baseEnd_5892491 := by
    simpa [prefixWord, tailWord_5892491, baseEnd_5892491] using wordTrace_append hprefix tailTrace_5892491
  have hstable : (prefixWord ++ tailWord_5892491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892491).length < 2 ^ (prefixWord ++ tailWord_5892491).sum := by decide
  have hdescent : baseEnd_5892491 < baseStart_5892491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892511 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 6]
def baseStart_5892511 : Nat := 118140960795 + 5892511 * 2 ^ 59
def prefixEnd_5892511 : Nat := 4983230072969 + 3 ^ 40 * 5892511 * 2
def baseEnd_5892511 : Nat := 336187822767277806368149

theorem tailTrace_5892511 : CollatzResearch.WordTrace tailWord_5892511 prefixEnd_5892511 336187822767277806368149 := by
  unfold tailWord_5892511
  simp only [CollatzResearch.WordTrace]
  refine ⟨214917532355446482603437387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143278354903630988402291591 214917532355446482603437387)
  ·
    refine ⟨322376298533169723905156081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214917532355446482603437387 322376298533169723905156081)
    ·
      refine ⟨241782223899877292928867061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322376298533169723905156081 241782223899877292928867061)
      ·
        refine ⟨22667083490613496212081287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241782223899877292928867061 22667083490613496212081287)
        ·
          refine ⟨34000625235920244318121931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22667083490613496212081287 34000625235920244318121931)
          ·
            refine ⟨51000937853880366477182897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34000625235920244318121931 51000937853880366477182897)
            ·
              refine ⟨38250703390410274857887173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51000937853880366477182897 38250703390410274857887173)
              ·
                refine ⟨7172006885701926535853845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38250703390410274857887173 7172006885701926535853845)
                ·
                  refine ⟨336187822767277806368149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7172006885701926535853845 336187822767277806368149)
                  ·
                    rfl

theorem cell23_5892511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 6].length) (baseStart_5892511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892511 prefixEnd_5892511 := by exact prefixLift 5892511
  have htrace : WordTrace (prefixWord ++ tailWord_5892511) baseStart_5892511 baseEnd_5892511 := by
    simpa [prefixWord, tailWord_5892511, baseEnd_5892511] using wordTrace_append hprefix tailTrace_5892511
  have hstable : (prefixWord ++ tailWord_5892511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892511).length < 2 ^ (prefixWord ++ tailWord_5892511).sum := by decide
  have hdescent : baseEnd_5892511 < baseStart_5892511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892524 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_5892524 : Nat := 118140960795 + 5892524 * 2 ^ 59
def prefixEnd_5892524 : Nat := 4983230072969 + 3 ^ 40 * 5892524 * 2
def baseEnd_5892524 : Nat := 1008565693384669568816927

theorem tailTrace_5892524 : CollatzResearch.WordTrace tailWord_5892524 prefixEnd_5892524 1008565693384669568816927 := by
  unfold tailWord_5892524
  simp only [CollatzResearch.WordTrace]
  refine ⟨107459003252199692911830313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143278671002932923882440417 107459003252199692911830313)
  ·
    refine ⟨80594252439149769683872735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107459003252199692911830313 80594252439149769683872735)
    ·
      refine ⟨120891378658724654525809103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80594252439149769683872735 120891378658724654525809103)
      ·
        refine ⟨181337067988086981788713655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120891378658724654525809103 181337067988086981788713655)
        ·
          refine ⟨272005601982130472683070483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181337067988086981788713655 272005601982130472683070483)
          ·
            refine ⟨408008402973195709024605725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272005601982130472683070483 408008402973195709024605725)
            ·
              refine ⟨153003151114948390884227147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408008402973195709024605725 153003151114948390884227147)
              ·
                refine ⟨229504726672422586326340721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153003151114948390884227147 229504726672422586326340721)
                ·
                  refine ⟨172128545004316939744755541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229504726672422586326340721 172128545004316939744755541)
                  ·
                    refine ⟨1008565693384669568816927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 172128545004316939744755541 1008565693384669568816927)
                    ·
                      rfl

theorem cell23_5892524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_5892524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892524 prefixEnd_5892524 := by exact prefixLift 5892524
  have htrace : WordTrace (prefixWord ++ tailWord_5892524) baseStart_5892524 baseEnd_5892524 := by
    simpa [prefixWord, tailWord_5892524, baseEnd_5892524] using wordTrace_append hprefix tailTrace_5892524
  have hstable : (prefixWord ++ tailWord_5892524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892524).length < 2 ^ (prefixWord ++ tailWord_5892524).sum := by decide
  have hdescent : baseEnd_5892524 < baseStart_5892524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892538 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_5892538 : Nat := 118140960795 + 5892538 * 2 ^ 59
def prefixEnd_5892538 : Nat := 4983230072969 + 3 ^ 40 * 5892538 * 2
def baseEnd_5892538 : Nat := 3025704268883171651675717

theorem tailTrace_5892538 : CollatzResearch.WordTrace tailWord_5892538 prefixEnd_5892538 3025704268883171651675717 := by
  unfold tailWord_5892538
  simp only [CollatzResearch.WordTrace]
  refine ⟨53729629281587166553667567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143279011417565777476446845 53729629281587166553667567)
  ·
    refine ⟨80594443922380749830501351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53729629281587166553667567 80594443922380749830501351)
    ·
      refine ⟨120891665883571124745752027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80594443922380749830501351 120891665883571124745752027)
      ·
        refine ⟨181337498825356687118628041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120891665883571124745752027 181337498825356687118628041)
        ·
          refine ⟨136003124119017515338971031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181337498825356687118628041 136003124119017515338971031)
          ·
            refine ⟨204004686178526273008456547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136003124119017515338971031 204004686178526273008456547)
            ·
              refine ⟨306007029267789409512684821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204004686178526273008456547 306007029267789409512684821)
              ·
                refine ⟨14344079496927628570907101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 306007029267789409512684821 14344079496927628570907101)
                ·
                  refine ⟨5379029811347860714090163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14344079496927628570907101 5379029811347860714090163)
                  ·
                    refine ⟨8068544717021791071135245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379029811347860714090163 8068544717021791071135245)
                    ·
                      refine ⟨3025704268883171651675717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8068544717021791071135245 3025704268883171651675717)
                      ·
                        rfl

theorem cell23_5892538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_5892538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892538 prefixEnd_5892538 := by exact prefixLift 5892538
  have htrace : WordTrace (prefixWord ++ tailWord_5892538) baseStart_5892538 baseEnd_5892538 := by
    simpa [prefixWord, tailWord_5892538, baseEnd_5892538] using wordTrace_append hprefix tailTrace_5892538
  have hstable : (prefixWord ++ tailWord_5892538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892538).length < 2 ^ (prefixWord ++ tailWord_5892538).sum := by decide
  have hdescent : baseEnd_5892538 < baseStart_5892538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892555 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 1, 1, 3]
def baseStart_5892555 : Nat := 118140960795 + 5892555 * 2 ^ 59
def prefixEnd_5892555 : Nat := 4983230072969 + 3 ^ 40 * 5892555 * 2
def baseEnd_5892555 : Nat := 3025712998054298085163139

theorem tailTrace_5892555 : CollatzResearch.WordTrace tailWord_5892555 prefixEnd_5892555 3025712998054298085163139 := by
  unfold tailWord_5892555
  simp only [CollatzResearch.WordTrace]
  refine ⟨214919137167287078118039119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143279424778191385412026079 214919137167287078118039119)
  ·
    refine ⟨322378705750930617177058679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214919137167287078118039119 322378705750930617177058679)
    ·
      refine ⟨483568058626395925765588019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322378705750930617177058679 483568058626395925765588019)
      ·
        refine ⟨725352087939593888648382029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483568058626395925765588019 725352087939593888648382029)
        ·
          refine ⟨272007032977347708243143261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 725352087939593888648382029 272007032977347708243143261)
          ·
            refine ⟨102002637366505390591178723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272007032977347708243143261 102002637366505390591178723)
            ·
              refine ⟨153003956049758085886768085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102002637366505390591178723 153003956049758085886768085)
              ·
                refine ⟨3586030219916205137971127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153003956049758085886768085 3586030219916205137971127)
                ·
                  refine ⟨5379045329874307706956691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586030219916205137971127 5379045329874307706956691)
                  ·
                    refine ⟨8068567994811461560435037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379045329874307706956691 8068567994811461560435037)
                    ·
                      refine ⟨3025712998054298085163139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8068567994811461560435037 3025712998054298085163139)
                      ·
                        rfl

theorem cell23_5892555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 1, 3].length) (baseStart_5892555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892555 prefixEnd_5892555 := by exact prefixLift 5892555
  have htrace : WordTrace (prefixWord ++ tailWord_5892555) baseStart_5892555 baseEnd_5892555 := by
    simpa [prefixWord, tailWord_5892555, baseEnd_5892555] using wordTrace_append hprefix tailTrace_5892555
  have hstable : (prefixWord ++ tailWord_5892555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892555).length < 2 ^ (prefixWord ++ tailWord_5892555).sum := by decide
  have hdescent : baseEnd_5892555 < baseStart_5892555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892565 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5892565 : Nat := 118140960795 + 5892565 * 2 ^ 59
def prefixEnd_5892565 : Nat := 4983230072969 + 3 ^ 40 * 5892565 * 2
def baseEnd_5892565 : Nat := 3025718132860843046038093

theorem tailTrace_5892565 : CollatzResearch.WordTrace tailWord_5892565 prefixEnd_5892565 3025718132860843046038093 := by
  unfold tailWord_5892565
  simp only [CollatzResearch.WordTrace]
  refine ⟨214919501897250849825903149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143279667931500566550602099 214919501897250849825903149)
  ·
    refine ⟨80594813211469068684713681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214919501897250849825903149 80594813211469068684713681)
    ·
      refine ⟨60446109908601801513535261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80594813211469068684713681 60446109908601801513535261)
      ·
        refine ⟨22667291215725675567575723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60446109908601801513535261 22667291215725675567575723)
        ·
          refine ⟨34000936823588513351363585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22667291215725675567575723 34000936823588513351363585)
          ·
            refine ⟨25500702617691385013522689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34000936823588513351363585 25500702617691385013522689)
            ·
              refine ⟨19125526963268538760142017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25500702617691385013522689 19125526963268538760142017)
              ·
                refine ⟨14344145222451404070106513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19125526963268538760142017 14344145222451404070106513)
                ·
                  refine ⟨10758108916838553052579885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14344145222451404070106513 10758108916838553052579885)
                  ·
                    refine ⟨4034290843814457394717457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10758108916838553052579885 4034290843814457394717457)
                    ·
                      refine ⟨3025718132860843046038093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034290843814457394717457 3025718132860843046038093)
                      ·
                        rfl

theorem cell23_5892565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5892565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892565 prefixEnd_5892565 := by exact prefixLift 5892565
  have htrace : WordTrace (prefixWord ++ tailWord_5892565) baseStart_5892565 baseEnd_5892565 := by
    simpa [prefixWord, tailWord_5892565, baseEnd_5892565] using wordTrace_append hprefix tailTrace_5892565
  have hstable : (prefixWord ++ tailWord_5892565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892565).length < 2 ^ (prefixWord ++ tailWord_5892565).sum := by decide
  have hdescent : baseEnd_5892565 < baseStart_5892565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892588 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_5892588 : Nat := 118140960795 + 5892588 * 2 ^ 59
def prefixEnd_5892588 : Nat := 4983230072969 + 3 ^ 40 * 5892588 * 2
def baseEnd_5892588 : Nat := 1008576647638632152016829

theorem tailTrace_5892588 : CollatzResearch.WordTrace tailWord_5892588 prefixEnd_5892588 1008576647638632152016829 := by
  unfold tailWord_5892588
  simp only [CollatzResearch.WordTrace]
  refine ⟨107460170388083762376995209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143280227184111683169326945 107460170388083762376995209)
  ·
    refine ⟨80595127791062821782746407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107460170388083762376995209 80595127791062821782746407)
    ·
      refine ⟨120892691686594232674119611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80595127791062821782746407 120892691686594232674119611)
      ·
        refine ⟨181339037529891349011179417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120892691686594232674119611 181339037529891349011179417)
        ·
          refine ⟨136004278147418511758384563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181339037529891349011179417 136004278147418511758384563)
          ·
            refine ⟨204006417221127767637576845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136004278147418511758384563 204006417221127767637576845)
            ·
              refine ⟨76502406457922912864091317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204006417221127767637576845 76502406457922912864091317)
              ·
                refine ⟨7172100605430273081008561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76502406457922912864091317 7172100605430273081008561)
                ·
                  refine ⟨5379075454072704810756421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7172100605430273081008561 5379075454072704810756421)
                  ·
                    refine ⟨1008576647638632152016829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379075454072704810756421 1008576647638632152016829)
                    ·
                      rfl

theorem cell23_5892588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_5892588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892588 prefixEnd_5892588 := by exact prefixLift 5892588
  have htrace : WordTrace (prefixWord ++ tailWord_5892588) baseStart_5892588 baseEnd_5892588 := by
    simpa [prefixWord, tailWord_5892588, baseEnd_5892588] using wordTrace_append hprefix tailTrace_5892588
  have hstable : (prefixWord ++ tailWord_5892588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892588).length < 2 ^ (prefixWord ++ tailWord_5892588).sum := by decide
  have hdescent : baseEnd_5892588 < baseStart_5892588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892595 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 3, 2, 2]
def baseStart_5892595 : Nat := 118140960795 + 5892595 * 2 ^ 59
def prefixEnd_5892595 : Nat := 4983230072969 + 3 ^ 40 * 5892595 * 2
def baseEnd_5892595 : Nat := 3025733537280477928662955

theorem tailTrace_5892595 : CollatzResearch.WordTrace tailWord_5892595 prefixEnd_5892595 3025733537280477928662955 := by
  unfold tailWord_5892595
  simp only [CollatzResearch.WordTrace]
  refine ⟨214920596087142164949495239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143280397391428109966330159 214920596087142164949495239)
  ·
    refine ⟨322380894130713247424242859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214920596087142164949495239 322380894130713247424242859)
    ·
      refine ⟨483571341196069871136364289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322380894130713247424242859 483571341196069871136364289)
      ·
        refine ⟨362678505897052403352273217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483571341196069871136364289 362678505897052403352273217)
        ·
          refine ⟨272008879422789302514204913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362678505897052403352273217 272008879422789302514204913)
          ·
            refine ⟨204006659567091976885653685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272008879422789302514204913 204006659567091976885653685)
            ·
              refine ⟨19125624334414872833030033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204006659567091976885653685 19125624334414872833030033)
              ·
                refine ⟨14344218250811154624772525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19125624334414872833030033 14344218250811154624772525)
                ·
                  refine ⟨5379081844054182984289697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14344218250811154624772525 5379081844054182984289697)
                  ·
                    refine ⟨4034311383040637238217273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5379081844054182984289697 4034311383040637238217273)
                    ·
                      refine ⟨3025733537280477928662955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034311383040637238217273 3025733537280477928662955)
                      ·
                        rfl

theorem cell23_5892595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 2, 2].length) (baseStart_5892595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892595 prefixEnd_5892595 := by exact prefixLift 5892595
  have htrace : WordTrace (prefixWord ++ tailWord_5892595) baseStart_5892595 baseEnd_5892595 := by
    simpa [prefixWord, tailWord_5892595, baseEnd_5892595] using wordTrace_append hprefix tailTrace_5892595
  have hstable : (prefixWord ++ tailWord_5892595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892595).length < 2 ^ (prefixWord ++ tailWord_5892595).sum := by decide
  have hdescent : baseEnd_5892595 < baseStart_5892595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892612 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5892612 : Nat := 118140960795 + 5892612 * 2 ^ 59
def prefixEnd_5892612 : Nat := 4983230072969 + 3 ^ 40 * 5892612 * 2
def baseEnd_5892612 : Nat := 3025742266451604362150377

theorem tailTrace_5892612 : CollatzResearch.WordTrace tailWord_5892612 prefixEnd_5892612 3025742266451604362150377 := by
  unfold tailWord_5892612
  simp only [CollatzResearch.WordTrace]
  refine ⟨107460608064040288426432045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143280810752053717901909393 107460608064040288426432045)
  ·
    refine ⟨40297728024015108159912017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107460608064040288426432045 40297728024015108159912017)
    ·
      refine ⟨30223296018011331119934013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40297728024015108159912017 30223296018011331119934013)
      ·
        refine ⟨11333736006754249169975255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30223296018011331119934013 11333736006754249169975255)
        ·
          refine ⟨17000604010131373754962883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11333736006754249169975255 17000604010131373754962883)
          ·
            refine ⟨25500906015197060632444325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17000604010131373754962883 25500906015197060632444325)
            ·
              refine ⟨4781419877849448868583311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25500906015197060632444325 4781419877849448868583311)
              ·
                refine ⟨7172129816774173302874967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781419877849448868583311 7172129816774173302874967)
                ·
                  refine ⟨10758194725161259954312451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7172129816774173302874967 10758194725161259954312451)
                  ·
                    refine ⟨16137292087741889931468677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10758194725161259954312451 16137292087741889931468677)
                    ·
                      refine ⟨3025742266451604362150377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16137292087741889931468677 3025742266451604362150377)
                      ·
                        rfl

theorem cell23_5892612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5892612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892612 prefixEnd_5892612 := by exact prefixLift 5892612
  have htrace : WordTrace (prefixWord ++ tailWord_5892612) baseStart_5892612 baseEnd_5892612 := by
    simpa [prefixWord, tailWord_5892612, baseEnd_5892612] using wordTrace_append hprefix tailTrace_5892612
  have hstable : (prefixWord ++ tailWord_5892612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892612).length < 2 ^ (prefixWord ++ tailWord_5892612).sum := by decide
  have hdescent : baseEnd_5892612 < baseStart_5892612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892622 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_5892622 : Nat := 118140960795 + 5892622 * 2 ^ 59
def prefixEnd_5892622 : Nat := 4983230072969 + 3 ^ 40 * 5892622 * 2
def baseEnd_5892622 : Nat := 1008582467086049774341777

theorem tailTrace_5892622 : CollatzResearch.WordTrace tailWord_5892622 prefixEnd_5892622 1008582467086049774341777 := by
  unfold tailWord_5892622
  simp only [CollatzResearch.WordTrace]
  refine ⟨26865197607255543570091015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143281053905362899040485413 26865197607255543570091015)
  ·
    refine ⟨40297796410883315355136523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26865197607255543570091015 40297796410883315355136523)
    ·
      refine ⟨60446694616324973032704785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40297796410883315355136523 60446694616324973032704785)
      ·
        refine ⟨45335020962243729774528589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60446694616324973032704785 45335020962243729774528589)
        ·
          refine ⟨17000632860841398665448221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45335020962243729774528589 17000632860841398665448221)
          ·
            refine ⟨6375237322815524499543083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17000632860841398665448221 6375237322815524499543083)
            ·
              refine ⟨9562855984223286749314625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375237322815524499543083 9562855984223286749314625)
              ·
                refine ⟨7172141988167465061985969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9562855984223286749314625 7172141988167465061985969)
                ·
                  refine ⟨5379106491125598796489477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7172141988167465061985969 5379106491125598796489477)
                  ·
                    refine ⟨1008582467086049774341777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379106491125598796489477 1008582467086049774341777)
                    ·
                      rfl

theorem cell23_5892622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_5892622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892622 prefixEnd_5892622 := by exact prefixLift 5892622
  have htrace : WordTrace (prefixWord ++ tailWord_5892622) baseStart_5892622 baseEnd_5892622 := by
    simpa [prefixWord, tailWord_5892622, baseEnd_5892622] using wordTrace_append hprefix tailTrace_5892622
  have hstable : (prefixWord ++ tailWord_5892622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892622).length < 2 ^ (prefixWord ++ tailWord_5892622).sum := by decide
  have hdescent : baseEnd_5892622 < baseStart_5892622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892645 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_5892645 : Nat := 118140960795 + 5892645 * 2 ^ 59
def prefixEnd_5892645 : Nat := 4983230072969 + 3 ^ 40 * 5892645 * 2
def baseEnd_5892645 : Nat := 3025759211313202733037725

theorem tailTrace_5892645 : CollatzResearch.WordTrace tailWord_5892645 prefixEnd_5892645 3025759211313202733037725 := by
  unfold tailWord_5892645
  simp only [CollatzResearch.WordTrace]
  refine ⟨214922419736961023488815389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143281613157974015659210259 214922419736961023488815389)
  ·
    refine ⟨80595907401360383808305771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214922419736961023488815389 80595907401360383808305771)
    ·
      refine ⟨120893861102040575712458657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80595907401360383808305771 120893861102040575712458657)
      ·
        refine ⟨90670395826530431784343993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120893861102040575712458657 90670395826530431784343993)
        ·
          refine ⟨68002796869897823838257995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90670395826530431784343993 68002796869897823838257995)
          ·
            refine ⟨102004195304846735757386993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68002796869897823838257995 102004195304846735757386993)
            ·
              refine ⟨76503146478635051818040245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102004195304846735757386993 76503146478635051818040245)
              ·
                refine ⟨7172169982372036107941273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76503146478635051818040245 7172169982372036107941273)
                ·
                  refine ⟨5379127486779027080955955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7172169982372036107941273 5379127486779027080955955)
                  ·
                    refine ⟨8068691230168540621433933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379127486779027080955955 8068691230168540621433933)
                    ·
                      refine ⟨3025759211313202733037725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8068691230168540621433933 3025759211313202733037725)
                      ·
                        rfl

theorem cell23_5892645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_5892645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892645 prefixEnd_5892645 := by exact prefixLift 5892645
  have htrace : WordTrace (prefixWord ++ tailWord_5892645) baseStart_5892645 baseEnd_5892645 := by
    simpa [prefixWord, tailWord_5892645, baseEnd_5892645] using wordTrace_append hprefix tailTrace_5892645
  have hstable : (prefixWord ++ tailWord_5892645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892645).length < 2 ^ (prefixWord ++ tailWord_5892645).sum := by decide
  have hdescent : baseEnd_5892645 < baseStart_5892645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892651 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4]
def baseStart_5892651 : Nat := 118140960795 + 5892651 * 2 ^ 59
def prefixEnd_5892651 : Nat := 4983230072969 + 3 ^ 40 * 5892651 * 2
def baseEnd_5892651 : Nat := 3025762292197129709562697

theorem tailTrace_5892651 : CollatzResearch.WordTrace tailWord_5892651 prefixEnd_5892651 3025762292197129709562697 := by
  unfold tailWord_5892651
  simp only [CollatzResearch.WordTrace]
  refine ⟨214922638574939286513533807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143281759049959524342355871 214922638574939286513533807)
  ·
    refine ⟨322383957862408929770300711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214922638574939286513533807 322383957862408929770300711)
    ·
      refine ⟨483575936793613394655451067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322383957862408929770300711 483575936793613394655451067)
      ·
        refine ⟨725363905190420091983176601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483575936793613394655451067 725363905190420091983176601)
        ·
          refine ⟨544022928892815068987382451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725363905190420091983176601 544022928892815068987382451)
          ·
            refine ⟨816034393339222603481073677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544022928892815068987382451 816034393339222603481073677)
            ·
              refine ⟨306012897502208476305402629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 816034393339222603481073677 306012897502208476305402629)
              ·
                refine ⟨57377418281664089307262993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306012897502208476305402629 57377418281664089307262993)
                ·
                  refine ⟨43033063711248066980447245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57377418281664089307262993 43033063711248066980447245)
                  ·
                    refine ⟨16137398891718025117667717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43033063711248066980447245 16137398891718025117667717)
                    ·
                      refine ⟨3025762292197129709562697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16137398891718025117667717 3025762292197129709562697)
                      ·
                        rfl

theorem cell23_5892651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_5892651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892651 prefixEnd_5892651 := by exact prefixLift 5892651
  have htrace : WordTrace (prefixWord ++ tailWord_5892651) baseStart_5892651 baseEnd_5892651 := by
    simpa [prefixWord, tailWord_5892651, baseEnd_5892651] using wordTrace_append hprefix tailTrace_5892651
  have hstable : (prefixWord ++ tailWord_5892651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892651).length < 2 ^ (prefixWord ++ tailWord_5892651).sum := by decide
  have hdescent : baseEnd_5892651 < baseStart_5892651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892662 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_5892662 : Nat := 118140960795 + 5892662 * 2 ^ 59
def prefixEnd_5892662 : Nat := 4983230072969 + 3 ^ 40 * 5892662 * 2
def baseEnd_5892662 : Nat := 3025767940484329166525147

theorem tailTrace_5892662 : CollatzResearch.WordTrace tailWord_5892662 prefixEnd_5892662 3025767940484329166525147 := by
  unfold tailWord_5892662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432689986118714712011515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143282026518599623594789493 13432689986118714712011515)
  ·
    refine ⟨20149034979178072068017273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13432689986118714712011515 20149034979178072068017273)
    ·
      refine ⟨15111776234383554051012955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20149034979178072068017273 15111776234383554051012955)
      ·
        refine ⟨22667664351575331076519433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15111776234383554051012955 22667664351575331076519433)
        ·
          refine ⟨17000748263681498307389575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22667664351575331076519433 17000748263681498307389575)
          ·
            refine ⟨25501122395522247461084363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17000748263681498307389575 25501122395522247461084363)
            ·
              refine ⟨38251683593283371191626545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25501122395522247461084363 38251683593283371191626545)
              ·
                refine ⟨28688762694962528393719909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38251683593283371191626545 28688762694962528393719909)
                ·
                  refine ⟨5379143005305474073822483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28688762694962528393719909 5379143005305474073822483)
                  ·
                    refine ⟨8068714507958211110733725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379143005305474073822483 8068714507958211110733725)
                    ·
                      refine ⟨3025767940484329166525147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8068714507958211110733725 3025767940484329166525147)
                      ·
                        rfl

theorem cell23_5892662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_5892662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892662 prefixEnd_5892662 := by exact prefixLift 5892662
  have htrace : WordTrace (prefixWord ++ tailWord_5892662) baseStart_5892662 baseEnd_5892662 := by
    simpa [prefixWord, tailWord_5892662, baseEnd_5892662] using wordTrace_append hprefix tailTrace_5892662
  have hstable : (prefixWord ++ tailWord_5892662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892662).length < 2 ^ (prefixWord ++ tailWord_5892662).sum := by decide
  have hdescent : baseEnd_5892662 < baseStart_5892662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892853 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5892853 : Nat := 118140960795 + 5892853 * 2 ^ 59
def prefixEnd_5892853 : Nat := 4983230072969 + 3 ^ 40 * 5892853 * 2
def baseEnd_5892853 : Nat := 1008622005096445973078923

theorem tailTrace_5892853 : CollatzResearch.WordTrace tailWord_5892853 prefixEnd_5892853 1008622005096445973078923 := by
  unfold tailWord_5892853
  simp only [CollatzResearch.WordTrace]
  refine ⟨214930006120207475012387213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143286670746804983341591475 214930006120207475012387213)
  ·
    refine ⟨80598752295077803129645205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214930006120207475012387213 80598752295077803129645205)
    ·
      refine ⟨3778066513831772021702119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80598752295077803129645205 3778066513831772021702119)
      ·
        refine ⟨5667099770747658032553179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778066513831772021702119 5667099770747658032553179)
        ·
          refine ⟨8500649656121487048829769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5667099770747658032553179 8500649656121487048829769)
          ·
            refine ⟨6375487242091115286622327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8500649656121487048829769 6375487242091115286622327)
            ·
              refine ⟨9563230863136672929933491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375487242091115286622327 9563230863136672929933491)
              ·
                refine ⟨14344846294705009394900237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563230863136672929933491 14344846294705009394900237)
                ·
                  refine ⟨5379317360514378523087589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14344846294705009394900237 5379317360514378523087589)
                  ·
                    refine ⟨1008622005096445973078923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379317360514378523087589 1008622005096445973078923)
                    ·
                      rfl

theorem cell23_5892853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5892853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892853 prefixEnd_5892853 := by exact prefixLift 5892853
  have htrace : WordTrace (prefixWord ++ tailWord_5892853) baseStart_5892853 baseEnd_5892853 := by
    simpa [prefixWord, tailWord_5892853, baseEnd_5892853] using wordTrace_append hprefix tailTrace_5892853
  have hstable : (prefixWord ++ tailWord_5892853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892853).length < 2 ^ (prefixWord ++ tailWord_5892853).sum := by decide
  have hdescent : baseEnd_5892853 < baseStart_5892853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892865 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_5892865 : Nat := 118140960795 + 5892865 * 2 ^ 59
def prefixEnd_5892865 : Nat := 4983230072969 + 3 ^ 40 * 5892865 * 2
def baseEnd_5892865 : Nat := 3025872177057191872286713

theorem tailTrace_5892865 : CollatzResearch.WordTrace tailWord_5892865 prefixEnd_5892865 3025872177057191872286713 := by
  unfold tailWord_5892865
  simp only [CollatzResearch.WordTrace]
  refine ⟨214930443796164001061824049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143286962530776000707882699 214930443796164001061824049)
  ·
    refine ⟨161197832847123000796368037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214930443796164001061824049 161197832847123000796368037)
    ·
      refine ⟨30224593658835562649319007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161197832847123000796368037 30224593658835562649319007)
      ·
        refine ⟨45336890488253343973978511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30224593658835562649319007 45336890488253343973978511)
        ·
          refine ⟨68005335732380015960967767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45336890488253343973978511 68005335732380015960967767)
          ·
            refine ⟨102008003598570023941451651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68005335732380015960967767 102008003598570023941451651)
            ·
              refine ⟨153012005397855035912177477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102008003598570023941451651 153012005397855035912177477)
              ·
                refine ⟨28689751012097819233533277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153012005397855035912177477 28689751012097819233533277)
                ·
                  refine ⟨10758656629536682212574979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28689751012097819233533277 10758656629536682212574979)
                  ·
                    refine ⟨16137984944305023318862469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10758656629536682212574979 16137984944305023318862469)
                    ·
                      refine ⟨3025872177057191872286713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16137984944305023318862469 3025872177057191872286713)
                      ·
                        rfl

theorem cell23_5892865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_5892865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892865 prefixEnd_5892865 := by exact prefixLift 5892865
  have htrace : WordTrace (prefixWord ++ tailWord_5892865) baseStart_5892865 baseEnd_5892865 := by
    simpa [prefixWord, tailWord_5892865, baseEnd_5892865] using wordTrace_append hprefix tailTrace_5892865
  have hstable : (prefixWord ++ tailWord_5892865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892865).length < 2 ^ (prefixWord ++ tailWord_5892865).sum := by decide
  have hdescent : baseEnd_5892865 < baseStart_5892865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892895 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_5892895 : Nat := 118140960795 + 5892895 * 2 ^ 59
def prefixEnd_5892895 : Nat := 4983230072969 + 3 ^ 40 * 5892895 * 2
def baseEnd_5892895 : Nat := 3025887581476826754911575

theorem tailTrace_5892895 : CollatzResearch.WordTrace tailWord_5892895 prefixEnd_5892895 3025887581476826754911575 := by
  unfold tailWord_5892895
  simp only [CollatzResearch.WordTrace]
  refine ⟨214931537986055316185416139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143287691990703544123610759 214931537986055316185416139)
  ·
    refine ⟨322397306979082974278124209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214931537986055316185416139 322397306979082974278124209)
    ·
      refine ⟨241797980234312230708593157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322397306979082974278124209 241797980234312230708593157)
      ·
        refine ⟨45337121293933543257861217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241797980234312230708593157 45337121293933543257861217)
        ·
          refine ⟨34002840970450157443395913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45337121293933543257861217 34002840970450157443395913)
          ·
            refine ⟨25502130727837618082546935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34002840970450157443395913 25502130727837618082546935)
            ·
              refine ⟨38253196091756427123820403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25502130727837618082546935 38253196091756427123820403)
              ·
                refine ⟨57379794137634640685730605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38253196091756427123820403 57379794137634640685730605)
                ·
                  refine ⟨21517422801612990257148977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57379794137634640685730605 21517422801612990257148977)
                  ·
                    refine ⟨16138067101209742692861733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21517422801612990257148977 16138067101209742692861733)
                    ·
                      refine ⟨3025887581476826754911575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16138067101209742692861733 3025887581476826754911575)
                      ·
                        rfl

theorem cell23_5892895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_5892895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892895 prefixEnd_5892895 := by exact prefixLift 5892895
  have htrace : WordTrace (prefixWord ++ tailWord_5892895) baseStart_5892895 baseEnd_5892895 := by
    simpa [prefixWord, tailWord_5892895, baseEnd_5892895] using wordTrace_append hprefix tailTrace_5892895
  have hstable : (prefixWord ++ tailWord_5892895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892895).length < 2 ^ (prefixWord ++ tailWord_5892895).sum := by decide
  have hdescent : baseEnd_5892895 < baseStart_5892895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892910 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5892910 : Nat := 118140960795 + 5892910 * 2 ^ 59
def prefixEnd_5892910 : Nat := 4983230072969 + 3 ^ 40 * 5892910 * 2
def baseEnd_5892910 : Nat := 3025895283686644196224007

theorem tailTrace_5892910 : CollatzResearch.WordTrace tailWord_5892910 prefixEnd_5892910 3025895283686644196224007 := by
  unfold tailWord_5892910
  simp only [CollatzResearch.WordTrace]
  refine ⟨26866510635125121718401523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143288056720667315831474789 26866510635125121718401523)
  ·
    refine ⟨40299765952687682577602285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26866510635125121718401523 40299765952687682577602285)
    ·
      refine ⟨15112412232257880966600857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40299765952687682577602285 15112412232257880966600857)
      ·
        refine ⟨11334309174193410724950643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15112412232257880966600857 11334309174193410724950643)
        ·
          refine ⟨17001463761290116087425965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11334309174193410724950643 17001463761290116087425965)
          ·
            refine ⟨6375548910483793532784737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17001463761290116087425965 6375548910483793532784737)
            ·
              refine ⟨4781661682862845149588553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6375548910483793532784737 4781661682862845149588553)
              ·
                refine ⟨3586246262147133862191415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781661682862845149588553 3586246262147133862191415)
                ·
                  refine ⟨5379369393220700793287123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586246262147133862191415 5379369393220700793287123)
                  ·
                    refine ⟨8069054089831051189930685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379369393220700793287123 8069054089831051189930685)
                    ·
                      refine ⟨3025895283686644196224007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069054089831051189930685 3025895283686644196224007)
                      ·
                        rfl

theorem cell23_5892910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5892910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892910 prefixEnd_5892910 := by exact prefixLift 5892910
  have htrace : WordTrace (prefixWord ++ tailWord_5892910) baseStart_5892910 baseEnd_5892910 := by
    simpa [prefixWord, tailWord_5892910, baseEnd_5892910] using wordTrace_append hprefix tailTrace_5892910
  have hstable : (prefixWord ++ tailWord_5892910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892910).length < 2 ^ (prefixWord ++ tailWord_5892910).sum := by decide
  have hdescent : baseEnd_5892910 < baseStart_5892910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892922 : List Nat := [3, 1, 1, 1, 6, 2, 1, 8]
def baseStart_5892922 : Nat := 118140960795 + 5892922 * 2 ^ 59
def prefixEnd_5892922 : Nat := 4983230072969 + 3 ^ 40 * 5892922 * 2
def baseEnd_5892922 : Nat := 112070423905722153676813

theorem tailTrace_5892922 : CollatzResearch.WordTrace tailWord_5892922 prefixEnd_5892922 112070423905722153676813 := by
  unfold tailWord_5892922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53733130689239374949162255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143288348504638333197766013 53733130689239374949162255)
  ·
    refine ⟨80599696033859062423743383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53733130689239374949162255 80599696033859062423743383)
    ·
      refine ⟨120899544050788593635615075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80599696033859062423743383 120899544050788593635615075)
      ·
        refine ⟨181349316076182890453422613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120899544050788593635615075 181349316076182890453422613)
        ·
          refine ⟨8500749191071072990004185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181349316076182890453422613 8500749191071072990004185)
          ·
            refine ⟨6375561893303304742503139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8500749191071072990004185 6375561893303304742503139)
            ·
              refine ⟨9563342839954957113754709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375561893303304742503139 9563342839954957113754709)
              ·
                refine ⟨112070423905722153676813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9563342839954957113754709 112070423905722153676813)
                ·
                  rfl

theorem cell23_5892922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_5892922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892922 prefixEnd_5892922 := by exact prefixLift 5892922
  have htrace : WordTrace (prefixWord ++ tailWord_5892922) baseStart_5892922 baseEnd_5892922 := by
    simpa [prefixWord, tailWord_5892922, baseEnd_5892922] using wordTrace_append hprefix tailTrace_5892922
  have hstable : (prefixWord ++ tailWord_5892922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892922).length < 2 ^ (prefixWord ++ tailWord_5892922).sum := by decide
  have hdescent : baseEnd_5892922 < baseStart_5892922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892959 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 1, 3, 2]
def baseStart_5892959 : Nat := 118140960795 + 5892959 * 2 ^ 59
def prefixEnd_5892959 : Nat := 4983230072969 + 3 ^ 40 * 5892959 * 2
def baseEnd_5892959 : Nat := 3025920444238714504511281

theorem tailTrace_5892959 : CollatzResearch.WordTrace tailWord_5892959 prefixEnd_5892959 3025920444238714504511281 := by
  unfold tailWord_5892959
  simp only [CollatzResearch.WordTrace]
  refine ⟨214933872257823455115745931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143289248171882303410497287 214933872257823455115745931)
  ·
    refine ⟨322400808386735182673618897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214933872257823455115745931 322400808386735182673618897)
    ·
      refine ⟨241800606290051387005214173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322400808386735182673618897 241800606290051387005214173)
      ·
        refine ⟨90675227358769270126955315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241800606290051387005214173 90675227358769270126955315)
        ·
          refine ⟨136012841038153905190432973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90675227358769270126955315 136012841038153905190432973)
          ·
            refine ⟨51004815389307714446412365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136012841038153905190432973 51004815389307714446412365)
            ·
              refine ⟨19126805770990392917404637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51004815389307714446412365 19126805770990392917404637)
              ·
                refine ⟨7172552164121397344026739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19126805770990392917404637 7172552164121397344026739)
                ·
                  refine ⟨10758828246182096016040109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7172552164121397344026739 10758828246182096016040109)
                  ·
                    refine ⟨4034560592318286006015041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10758828246182096016040109 4034560592318286006015041)
                    ·
                      refine ⟨3025920444238714504511281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034560592318286006015041 3025920444238714504511281)
                      ·
                        rfl

theorem cell23_5892959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_5892959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892959 prefixEnd_5892959 := by exact prefixLift 5892959
  have htrace : WordTrace (prefixWord ++ tailWord_5892959) baseStart_5892959 baseEnd_5892959 := by
    simpa [prefixWord, tailWord_5892959, baseEnd_5892959] using wordTrace_append hprefix tailTrace_5892959
  have hstable : (prefixWord ++ tailWord_5892959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892959).length < 2 ^ (prefixWord ++ tailWord_5892959).sum := by decide
  have hdescent : baseEnd_5892959 < baseStart_5892959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892965 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_5892965 : Nat := 118140960795 + 5892965 * 2 ^ 59
def prefixEnd_5892965 : Nat := 4983230072969 + 3 ^ 40 * 5892965 * 2
def baseEnd_5892965 : Nat := 1008641175040880493678751

theorem tailTrace_5892965 : CollatzResearch.WordTrace tailWord_5892965 prefixEnd_5892965 1008641175040880493678751 := by
  unfold tailWord_5892965
  simp only [CollatzResearch.WordTrace]
  refine ⟨214934091095801718140464349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143289394063867812093642899 214934091095801718140464349)
  ·
    refine ⟨80600284160925644302674131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214934091095801718140464349 80600284160925644302674131)
    ·
      refine ⟨120900426241388466454011197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80600284160925644302674131 120900426241388466454011197)
      ·
        refine ⟨45337659840520674920254199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120900426241388466454011197 45337659840520674920254199)
        ·
          refine ⟨68006489760781012380381299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45337659840520674920254199 68006489760781012380381299)
          ·
            refine ⟨102009734641171518570571949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68006489760781012380381299 102009734641171518570571949)
            ·
              refine ⟨38253650490439319463964481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102009734641171518570571949 38253650490439319463964481)
              ·
                refine ⟨28690237867829489597973361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38253650490439319463964481 28690237867829489597973361)
                ·
                  refine ⟨21517678400872117198480021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28690237867829489597973361 21517678400872117198480021)
                  ·
                    refine ⟨1008641175040880493678751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21517678400872117198480021 1008641175040880493678751)
                    ·
                      rfl

theorem cell23_5892965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_5892965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892965 prefixEnd_5892965 := by exact prefixLift 5892965
  have htrace : WordTrace (prefixWord ++ tailWord_5892965) baseStart_5892965 baseEnd_5892965 := by
    simpa [prefixWord, tailWord_5892965, baseEnd_5892965] using wordTrace_append hprefix tailTrace_5892965
  have hstable : (prefixWord ++ tailWord_5892965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892965).length < 2 ^ (prefixWord ++ tailWord_5892965).sum := by decide
  have hdescent : baseEnd_5892965 < baseStart_5892965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892975 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_5892975 : Nat := 118140960795 + 5892975 * 2 ^ 59
def prefixEnd_5892975 : Nat := 4983230072969 + 3 ^ 40 * 5892975 * 2
def baseEnd_5892975 : Nat := 3025928659929186441911207

theorem tailTrace_5892975 : CollatzResearch.WordTrace tailWord_5892975 prefixEnd_5892975 3025928659929186441911207 := by
  unfold tailWord_5892975
  simp only [CollatzResearch.WordTrace]
  refine ⟨214934455825765489848328379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143289637217176993232218919 214934455825765489848328379)
  ·
    refine ⟨322401683738648234772492569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214934455825765489848328379 322401683738648234772492569)
    ·
      refine ⟨241801262803986176079369427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322401683738648234772492569 241801262803986176079369427)
      ·
        refine ⟨362701894205979264119054141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241801262803986176079369427 362701894205979264119054141)
        ·
          refine ⟨136013210327242224044645303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362701894205979264119054141 136013210327242224044645303)
          ·
            refine ⟨204019815490863336066967955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136013210327242224044645303 204019815490863336066967955)
            ·
              refine ⟨306029723236295004100451933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204019815490863336066967955 306029723236295004100451933)
              ·
                refine ⟨114761146213610626537669475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306029723236295004100451933 114761146213610626537669475)
                ·
                  refine ⟨172141719320415939806504213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114761146213610626537669475 172141719320415939806504213)
                  ·
                    refine ⟨8069143093144497178429885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172141719320415939806504213 8069143093144497178429885)
                    ·
                      refine ⟨3025928659929186441911207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069143093144497178429885 3025928659929186441911207)
                      ·
                        rfl

theorem cell23_5892975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_5892975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892975 prefixEnd_5892975 := by exact prefixLift 5892975
  have htrace : WordTrace (prefixWord ++ tailWord_5892975) baseStart_5892975 baseEnd_5892975 := by
    simpa [prefixWord, tailWord_5892975, baseEnd_5892975] using wordTrace_append hprefix tailTrace_5892975
  have hstable : (prefixWord ++ tailWord_5892975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892975).length < 2 ^ (prefixWord ++ tailWord_5892975).sum := by decide
  have hdescent : baseEnd_5892975 < baseStart_5892975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892989 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_5892989 : Nat := 118140960795 + 5892989 * 2 ^ 59
def prefixEnd_5892989 : Nat := 4983230072969 + 3 ^ 40 * 5892989 * 2
def baseEnd_5892989 : Nat := 3025935848658349387136143

theorem tailTrace_5892989 : CollatzResearch.WordTrace tailWord_5892989 prefixEnd_5892989 3025935848658349387136143 := by
  unfold tailWord_5892989
  simp only [CollatzResearch.WordTrace]
  refine ⟨214934966447714770239338021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143289977631809846826225347 214934966447714770239338021)
  ·
    refine ⟨40300306208946519419875879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214934966447714770239338021 40300306208946519419875879)
    ·
      refine ⟨60450459313419779129813819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40300306208946519419875879 60450459313419779129813819)
      ·
        refine ⟨90675688970129668694720729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60450459313419779129813819 90675688970129668694720729)
        ·
          refine ⟨68006766727597251521040547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90675688970129668694720729 68006766727597251521040547)
          ·
            refine ⟨102010150091395877281560821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68006766727597251521040547 102010150091395877281560821)
            ·
              refine ⟨9563451571068363495146327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102010150091395877281560821 9563451571068363495146327)
              ·
                refine ⟨14345177356602545242719491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563451571068363495146327 14345177356602545242719491)
                ·
                  refine ⟨21517766034903817864079237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14345177356602545242719491 21517766034903817864079237)
                  ·
                    refine ⟨4034581131544465849514857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21517766034903817864079237 4034581131544465849514857)
                    ·
                      refine ⟨3025935848658349387136143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034581131544465849514857 3025935848658349387136143)
                      ·
                        rfl

theorem cell23_5892989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_5892989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892989 prefixEnd_5892989 := by exact prefixLift 5892989
  have htrace : WordTrace (prefixWord ++ tailWord_5892989) baseStart_5892989 baseEnd_5892989 := by
    simpa [prefixWord, tailWord_5892989, baseEnd_5892989] using wordTrace_append hprefix tailTrace_5892989
  have hstable : (prefixWord ++ tailWord_5892989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892989).length < 2 ^ (prefixWord ++ tailWord_5892989).sum := by decide
  have hdescent : baseEnd_5892989 < baseStart_5892989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5892995 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 7]
def baseStart_5892995 : Nat := 118140960795 + 5892995 * 2 ^ 59
def prefixEnd_5892995 : Nat := 4983230072969 + 3 ^ 40 * 5892995 * 2
def baseEnd_5892995 : Nat := 336215436615808484851235

theorem tailTrace_5892995 : CollatzResearch.WordTrace tailWord_5892995 prefixEnd_5892995 336215436615808484851235 := by
  unfold tailWord_5892995
  simp only [CollatzResearch.WordTrace]
  refine ⟨214935185285693033264056439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143290123523795355509370959 214935185285693033264056439)
  ·
    refine ⟨322402777928539549896084659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214935185285693033264056439 322402777928539549896084659)
    ·
      refine ⟨483604166892809324844126989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322402777928539549896084659 483604166892809324844126989)
      ·
        refine ⟨181351562584803496816547621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483604166892809324844126989 181351562584803496816547621)
        ·
          refine ⟨34003417984650655653102679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181351562584803496816547621 34003417984650655653102679)
          ·
            refine ⟨51005126976975983479654019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34003417984650655653102679 51005126976975983479654019)
            ·
              refine ⟨76507690465463975219481029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51005126976975983479654019 76507690465463975219481029)
              ·
                refine ⟨14345191962274495353652693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76507690465463975219481029 14345191962274495353652693)
                ·
                  refine ⟨336215436615808484851235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14345191962274495353652693 336215436615808484851235)
                  ·
                    rfl

theorem cell23_5892995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 7].length) (baseStart_5892995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5892995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5892995 prefixEnd_5892995 := by exact prefixLift 5892995
  have htrace : WordTrace (prefixWord ++ tailWord_5892995) baseStart_5892995 baseEnd_5892995 := by
    simpa [prefixWord, tailWord_5892995, baseEnd_5892995] using wordTrace_append hprefix tailTrace_5892995
  have hstable : (prefixWord ++ tailWord_5892995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5892995).length < 2 ^ (prefixWord ++ tailWord_5892995).sum := by decide
  have hdescent : baseEnd_5892995 < baseStart_5892995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5892995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893035 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5]
def baseStart_5893035 : Nat := 118140960795 + 5893035 * 2 ^ 59
def prefixEnd_5893035 : Nat := 4983230072969 + 3 ^ 40 * 5893035 * 2
def baseEnd_5893035 : Nat := 3025959468768456207160931

theorem tailTrace_5893035 : CollatzResearch.WordTrace tailWord_5893035 prefixEnd_5893035 3025959468768456207160931 := by
  unfold tailWord_5893035
  simp only [CollatzResearch.WordTrace]
  refine ⟨214936644205548120095512559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143291096137032080063675039 214936644205548120095512559)
  ·
    refine ⟨322404966308322180143268839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214936644205548120095512559 322404966308322180143268839)
    ·
      refine ⟨483607449462483270214903259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322404966308322180143268839 483607449462483270214903259)
      ·
        refine ⟨725411174193724905322354889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483607449462483270214903259 725411174193724905322354889)
        ·
          refine ⟨544058380645293678991766167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725411174193724905322354889 544058380645293678991766167)
          ·
            refine ⟨816087570967940518487649251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544058380645293678991766167 816087570967940518487649251)
            ·
              refine ⟨1224131356451910777731473877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816087570967940518487649251 1224131356451910777731473877)
              ·
                refine ⟨28690578666841658853081419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1224131356451910777731473877 28690578666841658853081419)
                ·
                  refine ⟨43035868000262488279622129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28690578666841658853081419 43035868000262488279622129)
                  ·
                    refine ⟨32276901000196866209716597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43035868000262488279622129 32276901000196866209716597)
                    ·
                      refine ⟨3025959468768456207160931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32276901000196866209716597 3025959468768456207160931)
                      ·
                        rfl

theorem cell23_5893035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_5893035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893035 prefixEnd_5893035 := by exact prefixLift 5893035
  have htrace : WordTrace (prefixWord ++ tailWord_5893035) baseStart_5893035 baseEnd_5893035 := by
    simpa [prefixWord, tailWord_5893035, baseEnd_5893035] using wordTrace_append hprefix tailTrace_5893035
  have hstable : (prefixWord ++ tailWord_5893035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893035).length < 2 ^ (prefixWord ++ tailWord_5893035).sum := by decide
  have hdescent : baseEnd_5893035 < baseStart_5893035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893065 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_5893065 : Nat := 118140960795 + 5893065 * 2 ^ 59
def prefixEnd_5893065 : Nat := 4983230072969 + 3 ^ 40 * 5893065 * 2
def baseEnd_5893065 : Nat := 3025974873188091089785793

theorem tailTrace_5893065 : CollatzResearch.WordTrace tailWord_5893065 prefixEnd_5893065 3025974873188091089785793 := by
  unfold tailWord_5893065
  simp only [CollatzResearch.WordTrace]
  refine ⟨214937738395439435219104649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143291825596959623479403099 214937738395439435219104649)
  ·
    refine ⟨161203303796579576414328487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214937738395439435219104649 161203303796579576414328487)
    ·
      refine ⟨241804955694869364621492731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161203303796579576414328487 241804955694869364621492731)
      ·
        refine ⟨362707433542304046932239097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241804955694869364621492731 362707433542304046932239097)
        ·
          refine ⟨272030575156728035199179323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362707433542304046932239097 272030575156728035199179323)
          ·
            refine ⟨408045862735092052798768985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272030575156728035199179323 408045862735092052798768985)
            ·
              refine ⟨306034397051319039599076739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408045862735092052798768985 306034397051319039599076739)
              ·
                refine ⟨459051595576978559398615109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306034397051319039599076739 459051595576978559398615109)
                ·
                  refine ⟨86072174170683479887240333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459051595576978559398615109 86072174170683479887240333)
                  ·
                    refine ⟨32277065314006304957715125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86072174170683479887240333 32277065314006304957715125)
                    ·
                      refine ⟨3025974873188091089785793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32277065314006304957715125 3025974873188091089785793)
                      ·
                        rfl

theorem cell23_5893065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_5893065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893065 prefixEnd_5893065 := by exact prefixLift 5893065
  have htrace : WordTrace (prefixWord ++ tailWord_5893065) baseStart_5893065 baseEnd_5893065 := by
    simpa [prefixWord, tailWord_5893065, baseEnd_5893065] using wordTrace_append hprefix tailTrace_5893065
  have hstable : (prefixWord ++ tailWord_5893065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893065).length < 2 ^ (prefixWord ++ tailWord_5893065).sum := by decide
  have hdescent : baseEnd_5893065 < baseStart_5893065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893116 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_5893116 : Nat := 118140960795 + 5893116 * 2 ^ 59
def prefixEnd_5893116 : Nat := 4983230072969 + 3 ^ 40 * 5893116 * 2
def baseEnd_5893116 : Nat := 3026001060701470390248059

theorem tailTrace_5893116 : CollatzResearch.WordTrace tailWord_5893116 prefixEnd_5893116 3026001060701470390248059 := by
  unfold tailWord_5893116
  simp only [CollatzResearch.WordTrace]
  refine ⟨107469799259127335464605601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143293065678836447286140801 107469799259127335464605601)
  ·
    refine ⟨80602349444345501598454201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107469799259127335464605601 80602349444345501598454201)
    ·
      refine ⟨60451762083259126198840651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80602349444345501598454201 60451762083259126198840651)
      ·
        refine ⟨90677643124888689298260977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60451762083259126198840651 90677643124888689298260977)
        ·
          refine ⟨68008232343666516973695733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90677643124888689298260977 68008232343666516973695733)
          ·
            refine ⟨6375771782218735966283975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68008232343666516973695733 6375771782218735966283975)
            ·
              refine ⟨9563657673328103949425963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375771782218735966283975 9563657673328103949425963)
              ·
                refine ⟨14345486509992155924138945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563657673328103949425963 14345486509992155924138945)
                ·
                  refine ⟨10759114882494116943104209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14345486509992155924138945 10759114882494116943104209)
                  ·
                    refine ⟨8069336161870587707328157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10759114882494116943104209 8069336161870587707328157)
                    ·
                      refine ⟨3026001060701470390248059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069336161870587707328157 3026001060701470390248059)
                      ·
                        rfl

theorem cell23_5893116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_5893116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893116 prefixEnd_5893116 := by exact prefixLift 5893116
  have htrace : WordTrace (prefixWord ++ tailWord_5893116) baseStart_5893116 baseEnd_5893116 := by
    simpa [prefixWord, tailWord_5893116, baseEnd_5893116] using wordTrace_append hprefix tailTrace_5893116
  have hstable : (prefixWord ++ tailWord_5893116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893116).length < 2 ^ (prefixWord ++ tailWord_5893116).sum := by decide
  have hdescent : baseEnd_5893116 < baseStart_5893116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893139 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 4, 3, 2]
def baseStart_5893139 : Nat := 118140960795 + 5893139 * 2 ^ 59
def prefixEnd_5893139 : Nat := 4983230072969 + 3 ^ 40 * 5893139 * 2
def baseEnd_5893139 : Nat := 3026012870756523800260453

theorem tailTrace_5893139 : CollatzResearch.WordTrace tailWord_5893139 prefixEnd_5893139 3026012870756523800260453 := by
  unfold tailWord_5893139
  simp only [CollatzResearch.WordTrace]
  refine ⟨214940437397171345857298471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143293624931447563904865647 214940437397171345857298471)
  ·
    refine ⟨322410656095757018785947707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214940437397171345857298471 322410656095757018785947707)
    ·
      refine ⟨483615984143635528178921561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322410656095757018785947707 483615984143635528178921561)
      ·
        refine ⟨362711988107726646134191171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483615984143635528178921561 362711988107726646134191171)
        ·
          refine ⟨544067982161589969201286757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362711988107726646134191171 544067982161589969201286757)
          ·
            refine ⟨102012746655298119225241267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 544067982161589969201286757 102012746655298119225241267)
            ·
              refine ⟨153019119982947178837861901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102012746655298119225241267 153019119982947178837861901)
              ·
                refine ⟨57382169993605192064198213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153019119982947178837861901 57382169993605192064198213)
                ·
                  refine ⟨10759156873800973512037165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57382169993605192064198213 10759156873800973512037165)
                  ·
                    refine ⟨4034683827675365067013937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10759156873800973512037165 4034683827675365067013937)
                    ·
                      refine ⟨3026012870756523800260453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034683827675365067013937 3026012870756523800260453)
                      ·
                        rfl

theorem cell23_5893139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3, 2].length) (baseStart_5893139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893139 prefixEnd_5893139 := by exact prefixLift 5893139
  have htrace : WordTrace (prefixWord ++ tailWord_5893139) baseStart_5893139 baseEnd_5893139 := by
    simpa [prefixWord, tailWord_5893139, baseEnd_5893139] using wordTrace_append hprefix tailTrace_5893139
  have hstable : (prefixWord ++ tailWord_5893139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893139).length < 2 ^ (prefixWord ++ tailWord_5893139).sum := by decide
  have hdescent : baseEnd_5893139 < baseStart_5893139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893146 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_5893146 : Nat := 118140960795 + 5893146 * 2 ^ 59
def prefixEnd_5893146 : Nat := 4983230072969 + 3 ^ 40 * 5893146 * 2
def baseEnd_5893146 : Nat := 3026016465121105272872921

theorem tailTrace_5893146 : CollatzResearch.WordTrace tailWord_5893146 prefixEnd_5893146 3026016465121105272872921 := by
  unfold tailWord_5893146
  simp only [CollatzResearch.WordTrace]
  refine ⟨53735173177036496513200823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143293795138763990701868861 53735173177036496513200823)
  ·
    refine ⟨80602759765554744769801235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53735173177036496513200823 80602759765554744769801235)
    ·
      refine ⟨120904139648332117154701853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80602759765554744769801235 120904139648332117154701853)
      ·
        refine ⟨45339052368124543933013195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120904139648332117154701853 45339052368124543933013195)
        ·
          refine ⟨68008578552186815899519793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45339052368124543933013195 68008578552186815899519793)
          ·
            refine ⟨51006433914140111924639845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68008578552186815899519793 51006433914140111924639845)
            ·
              refine ⟨9563706358901270985869971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51006433914140111924639845 9563706358901270985869971)
              ·
                refine ⟨14345559538351906478804957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563706358901270985869971 14345559538351906478804957)
                ·
                  refine ⟨5379584826881964929551859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14345559538351906478804957 5379584826881964929551859)
                  ·
                    refine ⟨8069377240322947394327789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379584826881964929551859 8069377240322947394327789)
                    ·
                      refine ⟨3026016465121105272872921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069377240322947394327789 3026016465121105272872921)
                      ·
                        rfl

theorem cell23_5893146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_5893146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893146 prefixEnd_5893146 := by exact prefixLift 5893146
  have htrace : WordTrace (prefixWord ++ tailWord_5893146) baseStart_5893146 baseEnd_5893146 := by
    simpa [prefixWord, tailWord_5893146, baseEnd_5893146] using wordTrace_append hprefix tailTrace_5893146
  have hstable : (prefixWord ++ tailWord_5893146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893146).length < 2 ^ (prefixWord ++ tailWord_5893146).sum := by decide
  have hdescent : baseEnd_5893146 < baseStart_5893146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893156 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5893156 : Nat := 118140960795 + 5893156 * 2 ^ 59
def prefixEnd_5893156 : Nat := 4983230072969 + 3 ^ 40 * 5893156 * 2
def baseEnd_5893156 : Nat := 3026021599927650233747875

theorem tailTrace_5893156 : CollatzResearch.WordTrace tailWord_5893156 prefixEnd_5893156 3026021599927650233747875 := by
  unfold tailWord_5893156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107470528719054878880333661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143294038292073171840444881 107470528719054878880333661)
  ·
    refine ⟨40301448269645579580125123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107470528719054878880333661 40301448269645579580125123)
    ·
      refine ⟨60452172404468369370187685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40301448269645579580125123 60452172404468369370187685)
      ·
        refine ⟨11334782325837819256910191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60452172404468369370187685 11334782325837819256910191)
        ·
          refine ⟨17002173488756728885365287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11334782325837819256910191 17002173488756728885365287)
          ·
            refine ⟨25503260233135093328047931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17002173488756728885365287 25503260233135093328047931)
            ·
              refine ⟨38254890349702639992071897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25503260233135093328047931 38254890349702639992071897)
              ·
                refine ⟨28691167762276979994053923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38254890349702639992071897 28691167762276979994053923)
                ·
                  refine ⟨43036751643415469991080885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28691167762276979994053923 43036751643415469991080885)
                  ·
                    refine ⟨4034695466570200311663833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43036751643415469991080885 4034695466570200311663833)
                    ·
                      refine ⟨3026021599927650233747875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034695466570200311663833 3026021599927650233747875)
                      ·
                        rfl

theorem cell23_5893156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5893156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893156 prefixEnd_5893156 := by exact prefixLift 5893156
  have htrace : WordTrace (prefixWord ++ tailWord_5893156) baseStart_5893156 baseEnd_5893156 := by
    simpa [prefixWord, tailWord_5893156, baseEnd_5893156] using wordTrace_append hprefix tailTrace_5893156
  have hstable : (prefixWord ++ tailWord_5893156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893156).length < 2 ^ (prefixWord ++ tailWord_5893156).sum := by decide
  have hdescent : baseEnd_5893156 < baseStart_5893156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893166 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_5893166 : Nat := 118140960795 + 5893166 * 2 ^ 59
def prefixEnd_5893166 : Nat := 4983230072969 + 3 ^ 40 * 5893166 * 2
def baseEnd_5893166 : Nat := 1008675578244731731540943

theorem tailTrace_5893166 : CollatzResearch.WordTrace tailWord_5893166 prefixEnd_5893166 1008675578244731731540943 := by
  unfold tailWord_5893166
  simp only [CollatzResearch.WordTrace]
  refine ⟨26867677771009191183566419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143294281445382352979020901 26867677771009191183566419)
  ·
    refine ⟨40301516656513786775349629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26867677771009191183566419 40301516656513786775349629)
    ·
      refine ⟨15113068746192670040756111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40301516656513786775349629 15113068746192670040756111)
      ·
        refine ⟨22669603119289005061134167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15113068746192670040756111 22669603119289005061134167)
        ·
          refine ⟨34004404678933507591701251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22669603119289005061134167 34004404678933507591701251)
          ·
            refine ⟨51006607018400261387551877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34004404678933507591701251 51006607018400261387551877)
            ·
              refine ⟨9563738815950049010165977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51006607018400261387551877 9563738815950049010165977)
              ·
                refine ⟨7172804111962536757624483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9563738815950049010165977 7172804111962536757624483)
                ·
                  refine ⟨10759206167943805136436725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7172804111962536757624483 10759206167943805136436725)
                  ·
                    refine ⟨1008675578244731731540943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10759206167943805136436725 1008675578244731731540943)
                    ·
                      rfl

theorem cell23_5893166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_5893166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893166 prefixEnd_5893166 := by exact prefixLift 5893166
  have htrace : WordTrace (prefixWord ++ tailWord_5893166) baseStart_5893166 baseEnd_5893166 := by
    simpa [prefixWord, tailWord_5893166, baseEnd_5893166] using wordTrace_append hprefix tailTrace_5893166
  have hstable : (prefixWord ++ tailWord_5893166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893166).length < 2 ^ (prefixWord ++ tailWord_5893166).sum := by decide
  have hdescent : baseEnd_5893166 < baseStart_5893166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893169 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 6, 2]
def baseStart_5893169 : Nat := 118140960795 + 5893169 * 2 ^ 59
def prefixEnd_5893169 : Nat := 4983230072969 + 3 ^ 40 * 5893169 * 2
def baseEnd_5893169 : Nat := 3026028275176158682885315

theorem tailTrace_5893169 : CollatzResearch.WordTrace tailWord_5893169 prefixEnd_5893169 3026028275176158682885315 := by
  unfold tailWord_5893169
  simp only [CollatzResearch.WordTrace]
  refine ⟨214941531587062660980890561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143294354391375107320593707 214941531587062660980890561)
  ·
    refine ⟨161206148690296995735667921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214941531587062660980890561 161206148690296995735667921)
    ·
      refine ⟨120904611517722746801750941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161206148690296995735667921 120904611517722746801750941)
      ·
        refine ⟨45339229319146030050656603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120904611517722746801750941 45339229319146030050656603)
        ·
          refine ⟨68008843978719045075984905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45339229319146030050656603 68008843978719045075984905)
          ·
            refine ⟨51006632984039283806988679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68008843978719045075984905 51006632984039283806988679)
            ·
              refine ⟨76509949476058925710483019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51006632984039283806988679 76509949476058925710483019)
              ·
                refine ⟨114764924214088388565724529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76509949476058925710483019 114764924214088388565724529)
                ·
                  refine ⟨86073693160566291424293397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114764924214088388565724529 86073693160566291424293397)
                  ·
                    refine ⟨4034704366901544910513753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86073693160566291424293397 4034704366901544910513753)
                    ·
                      refine ⟨3026028275176158682885315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034704366901544910513753 3026028275176158682885315)
                      ·
                        rfl

theorem cell23_5893169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_5893169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893169 prefixEnd_5893169 := by exact prefixLift 5893169
  have htrace : WordTrace (prefixWord ++ tailWord_5893169) baseStart_5893169 baseEnd_5893169 := by
    simpa [prefixWord, tailWord_5893169, baseEnd_5893169] using wordTrace_append hprefix tailTrace_5893169
  have hstable : (prefixWord ++ tailWord_5893169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893169).length < 2 ^ (prefixWord ++ tailWord_5893169).sum := by decide
  have hdescent : baseEnd_5893169 < baseStart_5893169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893180 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_5893180 : Nat := 118140960795 + 5893180 * 2 ^ 59
def prefixEnd_5893180 : Nat := 4983230072969 + 3 ^ 40 * 5893180 * 2
def baseEnd_5893180 : Nat := 3026033923463358139847765

theorem tailTrace_5893180 : CollatzResearch.WordTrace tailWord_5893180 prefixEnd_5893180 3026033923463358139847765 := by
  unfold tailWord_5893180
  simp only [CollatzResearch.WordTrace]
  refine ⟨107470966395011404929770497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143294621860015206573027329 107470966395011404929770497)
  ·
    refine ⟨80603224796258553697327873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107470966395011404929770497 80603224796258553697327873)
    ·
      refine ⟨60452418597193915272995905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80603224796258553697327873 60452418597193915272995905)
      ·
        refine ⟨45339313947895436454746929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60452418597193915272995905 45339313947895436454746929)
        ·
          refine ⟨34004485460921577341060197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45339313947895436454746929 34004485460921577341060197)
          ·
            refine ⟨6375841023922795751448787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34004485460921577341060197 6375841023922795751448787)
            ·
              refine ⟨9563761535884193627173181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375841023922795751448787 9563761535884193627173181)
              ·
                refine ⟨3586410575956572610189943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9563761535884193627173181 3586410575956572610189943)
                ·
                  refine ⟨5379615863934858915284915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586410575956572610189943 5379615863934858915284915)
                  ·
                    refine ⟨8069423795902288372927373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379615863934858915284915 8069423795902288372927373)
                    ·
                      refine ⟨3026033923463358139847765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069423795902288372927373 3026033923463358139847765)
                      ·
                        rfl

theorem cell23_5893180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_5893180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893180 prefixEnd_5893180 := by exact prefixLift 5893180
  have htrace : WordTrace (prefixWord ++ tailWord_5893180) baseStart_5893180 baseEnd_5893180 := by
    simpa [prefixWord, tailWord_5893180, baseEnd_5893180] using wordTrace_append hprefix tailTrace_5893180
  have hstable : (prefixWord ++ tailWord_5893180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893180).length < 2 ^ (prefixWord ++ tailWord_5893180).sum := by decide
  have hdescent : baseEnd_5893180 < baseStart_5893180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893190 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5893190 : Nat := 118140960795 + 5893190 * 2 ^ 59
def prefixEnd_5893190 : Nat := 4983230072969 + 3 ^ 40 * 5893190 * 2
def baseEnd_5893190 : Nat := 3026039058269903100722719

theorem tailTrace_5893190 : CollatzResearch.WordTrace tailWord_5893190 prefixEnd_5893190 3026039058269903100722719 := by
  unfold tailWord_5893190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716946797499580673981407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143294865013324387711603349 6716946797499580673981407)
  ·
    refine ⟨10075420196249371010972111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6716946797499580673981407 10075420196249371010972111)
    ·
      refine ⟨15113130294374056516458167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075420196249371010972111 15113130294374056516458167)
      ·
        refine ⟨22669695441561084774687251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15113130294374056516458167 22669695441561084774687251)
        ·
          refine ⟨34004543162341627162030877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22669695441561084774687251 34004543162341627162030877)
          ·
            refine ⟨12751703685878110185761579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34004543162341627162030877 12751703685878110185761579)
            ·
              refine ⟨19127555528817165278642369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12751703685878110185761579 19127555528817165278642369)
              ·
                refine ⟨14345666646612873958981777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19127555528817165278642369 14345666646612873958981777)
                ·
                  refine ⟨10759249984959655469236333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14345666646612873958981777 10759249984959655469236333)
                  ·
                    refine ⟨4034718744359870800963625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10759249984959655469236333 4034718744359870800963625)
                    ·
                      refine ⟨3026039058269903100722719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034718744359870800963625 3026039058269903100722719)
                      ·
                        rfl

theorem cell23_5893190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5893190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893190 prefixEnd_5893190 := by exact prefixLift 5893190
  have htrace : WordTrace (prefixWord ++ tailWord_5893190) baseStart_5893190 baseEnd_5893190 := by
    simpa [prefixWord, tailWord_5893190, baseEnd_5893190] using wordTrace_append hprefix tailTrace_5893190
  have hstable : (prefixWord ++ tailWord_5893190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893190).length < 2 ^ (prefixWord ++ tailWord_5893190).sum := by decide
  have hdescent : baseEnd_5893190 < baseStart_5893190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893197 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_5893197 : Nat := 118140960795 + 5893197 * 2 ^ 59
def prefixEnd_5893197 : Nat := 4983230072969 + 3 ^ 40 * 5893197 * 2
def baseEnd_5893197 : Nat := 3026042652634484573335187

theorem tailTrace_5893197 : CollatzResearch.WordTrace tailWord_5893197 prefixEnd_5893197 3026042652634484573335187 := by
  unfold tailWord_5893197
  simp only [CollatzResearch.WordTrace]
  refine ⟨214942552830961221762909845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143295035220640814508606563 214942552830961221762909845)
  ·
    refine ⟨10075432163951307270136399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214942552830961221762909845 10075432163951307270136399)
    ·
      refine ⟨15113148245926960905204599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075432163951307270136399 15113148245926960905204599)
      ·
        refine ⟨22669722368890441357806899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15113148245926960905204599 22669722368890441357806899)
        ·
          refine ⟨34004583553335662036710349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22669722368890441357806899 34004583553335662036710349)
          ·
            refine ⟨12751718832500873263766381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34004583553335662036710349 12751718832500873263766381)
            ·
              refine ⟨4781894562187827473912393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12751718832500873263766381 4781894562187827473912393)
              ·
                refine ⟨3586420921640870605434295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781894562187827473912393 3586420921640870605434295)
                ·
                  refine ⟨5379631382461305908151443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586420921640870605434295 5379631382461305908151443)
                  ·
                    refine ⟨8069447073691958862227165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379631382461305908151443 8069447073691958862227165)
                    ·
                      refine ⟨3026042652634484573335187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069447073691958862227165 3026042652634484573335187)
                      ·
                        rfl

theorem cell23_5893197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_5893197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893197 prefixEnd_5893197 := by exact prefixLift 5893197
  have htrace : WordTrace (prefixWord ++ tailWord_5893197) baseStart_5893197 baseEnd_5893197 := by
    simpa [prefixWord, tailWord_5893197, baseEnd_5893197] using wordTrace_append hprefix tailTrace_5893197
  have hstable : (prefixWord ++ tailWord_5893197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893197).length < 2 ^ (prefixWord ++ tailWord_5893197).sum := by decide
  have hdescent : baseEnd_5893197 < baseStart_5893197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893219 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 3]
def baseStart_5893219 : Nat := 118140960795 + 5893219 * 2 ^ 59
def prefixEnd_5893219 : Nat := 4983230072969 + 3 ^ 40 * 5893219 * 2
def baseEnd_5893219 : Nat := 3026053949208883487260085

theorem tailTrace_5893219 : CollatzResearch.WordTrace tailWord_5893219 prefixEnd_5893219 3026053949208883487260085 := by
  unfold tailWord_5893219
  simp only [CollatzResearch.WordTrace]
  refine ⟨214943355236881519520210711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143295570157921013013473807 214943355236881519520210711)
  ·
    refine ⟨322415032855322279280316067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214943355236881519520210711 322415032855322279280316067)
    ·
      refine ⟨483622549282983418920474101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322415032855322279280316067 483622549282983418920474101)
      ·
        refine ⟨45339613995279695523794447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 483622549282983418920474101 45339613995279695523794447)
        ·
          refine ⟨68009420992919543285691671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45339613995279695523794447 68009420992919543285691671)
          ·
            refine ⟨102014131489379314928537507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68009420992919543285691671 102014131489379314928537507)
            ·
              refine ⟨153021197234068972392806261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102014131489379314928537507 153021197234068972392806261)
              ·
                refine ⟨14345737240693966161825587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153021197234068972392806261 14345737240693966161825587)
                ·
                  refine ⟨21518605861040949242738381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14345737240693966161825587 21518605861040949242738381)
                  ·
                    refine ⟨8069477197890355966026893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21518605861040949242738381 8069477197890355966026893)
                    ·
                      refine ⟨3026053949208883487260085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069477197890355966026893 3026053949208883487260085)
                      ·
                        rfl

theorem cell23_5893219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_5893219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893219 prefixEnd_5893219 := by exact prefixLift 5893219
  have htrace : WordTrace (prefixWord ++ tailWord_5893219) baseStart_5893219 baseEnd_5893219 := by
    simpa [prefixWord, tailWord_5893219, baseEnd_5893219] using wordTrace_append hprefix tailTrace_5893219
  have hstable : (prefixWord ++ tailWord_5893219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893219).length < 2 ^ (prefixWord ++ tailWord_5893219).sum := by decide
  have hdescent : baseEnd_5893219 < baseStart_5893219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893223 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_5893223 : Nat := 118140960795 + 5893223 * 2 ^ 59
def prefixEnd_5893223 : Nat := 4983230072969 + 3 ^ 40 * 5893223 * 2
def baseEnd_5893223 : Nat := 3026056003131501471610067

theorem tailTrace_5893223 : CollatzResearch.WordTrace tailWord_5893223 prefixEnd_5893223 3026056003131501471610067 := by
  unfold tailWord_5893223
  simp only [CollatzResearch.WordTrace]
  refine ⟨214943501128867028203356323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143295667419244685468904215 214943501128867028203356323)
  ·
    refine ⟨322415251693300542305034485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214943501128867028203356323 322415251693300542305034485)
    ·
      refine ⟨30226429846246925841096983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 322415251693300542305034485 30226429846246925841096983)
      ·
        refine ⟨45339644769370388761645475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30226429846246925841096983 45339644769370388761645475)
        ·
          refine ⟨68009467154055583142468213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45339644769370388761645475 68009467154055583142468213)
          ·
            refine ⟨6375887545692710919606395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68009467154055583142468213 6375887545692710919606395)
            ·
              refine ⟨9563831318539066379409593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375887545692710919606395 9563831318539066379409593)
              ·
                refine ⟨7172873488904299784557195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9563831318539066379409593 7172873488904299784557195)
                ·
                  refine ⟨10759310233356449676835793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7172873488904299784557195 10759310233356449676835793)
                  ·
                    refine ⟨8069482675017337257626845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10759310233356449676835793 8069482675017337257626845)
                    ·
                      refine ⟨3026056003131501471610067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069482675017337257626845 3026056003131501471610067)
                      ·
                        rfl

theorem cell23_5893223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_5893223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893223 prefixEnd_5893223 := by exact prefixLift 5893223
  have htrace : WordTrace (prefixWord ++ tailWord_5893223) baseStart_5893223 baseEnd_5893223 := by
    simpa [prefixWord, tailWord_5893223, baseEnd_5893223] using wordTrace_append hprefix tailTrace_5893223
  have hstable : (prefixWord ++ tailWord_5893223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893223).length < 2 ^ (prefixWord ++ tailWord_5893223).sum := by decide
  have hdescent : baseEnd_5893223 < baseStart_5893223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893297 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5893297 : Nat := 118140960795 + 5893297 * 2 ^ 59
def prefixEnd_5893297 : Nat := 4983230072969 + 3 ^ 40 * 5893297 * 2
def baseEnd_5893297 : Nat := 3026094000699934182084727

theorem tailTrace_5893297 : CollatzResearch.WordTrace tailWord_5893297 prefixEnd_5893297 3026094000699934182084727 := by
  unfold tailWord_5893297
  simp only [CollatzResearch.WordTrace]
  refine ⟨214946200130598938841550145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143297466753732625894366763 214946200130598938841550145)
  ·
    refine ⟨161209650097949204131162609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214946200130598938841550145 161209650097949204131162609)
    ·
      refine ⟨120907237573461903098371957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161209650097949204131162609 120907237573461903098371957)
      ·
        refine ⟨11335053522512053415472371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120907237573461903098371957 11335053522512053415472371)
        ·
          refine ⟨17002580283768080123208557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11335053522512053415472371 17002580283768080123208557)
          ·
            refine ⟨6375967606413030046203209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17002580283768080123208557 6375967606413030046203209)
            ·
              refine ⟨4781975704809772534652407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6375967606413030046203209 4781975704809772534652407)
              ·
                refine ⟨7172963557214658801978611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781975704809772534652407 7172963557214658801978611)
                ·
                  refine ⟨10759445335821988202967917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7172963557214658801978611 10759445335821988202967917)
                  ·
                    refine ⟨4034792000933245576112969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10759445335821988202967917 4034792000933245576112969)
                    ·
                      refine ⟨3026094000699934182084727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034792000933245576112969 3026094000699934182084727)
                      ·
                        rfl

theorem cell23_5893297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5893297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893297 prefixEnd_5893297 := by exact prefixLift 5893297
  have htrace : WordTrace (prefixWord ++ tailWord_5893297) baseStart_5893297 baseEnd_5893297 := by
    simpa [prefixWord, tailWord_5893297, baseEnd_5893297] using wordTrace_append hprefix tailTrace_5893297
  have hstable : (prefixWord ++ tailWord_5893297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893297).length < 2 ^ (prefixWord ++ tailWord_5893297).sum := by decide
  have hdescent : baseEnd_5893297 < baseStart_5893297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893310 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_5893310 : Nat := 118140960795 + 5893310 * 2 ^ 59
def prefixEnd_5893310 : Nat := 4983230072969 + 3 ^ 40 * 5893310 * 2
def baseEnd_5893310 : Nat := 3026100675948442631222167

theorem tailTrace_5893310 : CollatzResearch.WordTrace tailWord_5893310 prefixEnd_5893310 3026100675948442631222167 := by
  unfold tailWord_5893310
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868334284943980257721673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143297782853034561374515589 26868334284943980257721673)
  ·
    refine ⟨20151250713707985193291255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26868334284943980257721673 20151250713707985193291255)
    ·
      refine ⟨30226876070561977789936883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20151250713707985193291255 30226876070561977789936883)
      ·
        refine ⟨45340314105842966684905325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30226876070561977789936883 45340314105842966684905325)
        ·
          refine ⟨17002617789691112506839497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45340314105842966684905325 17002617789691112506839497)
          ·
            refine ⟨12751963342268334380129623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17002617789691112506839497 12751963342268334380129623)
            ·
              refine ⟨19127945013402501570194435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12751963342268334380129623 19127945013402501570194435)
              ·
                refine ⟨28691917520103752355291653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19127945013402501570194435 28691917520103752355291653)
                ·
                  refine ⟨5379734535019453566617185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28691917520103752355291653 5379734535019453566617185)
                  ·
                    refine ⟨4034800901264590174962889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5379734535019453566617185 4034800901264590174962889)
                    ·
                      refine ⟨3026100675948442631222167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034800901264590174962889 3026100675948442631222167)
                      ·
                        rfl

theorem cell23_5893310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_5893310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893310 prefixEnd_5893310 := by exact prefixLift 5893310
  have htrace : WordTrace (prefixWord ++ tailWord_5893310) baseStart_5893310 baseEnd_5893310 := by
    simpa [prefixWord, tailWord_5893310, baseEnd_5893310] using wordTrace_append hprefix tailTrace_5893310
  have hstable : (prefixWord ++ tailWord_5893310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893310).length < 2 ^ (prefixWord ++ tailWord_5893310).sum := by decide
  have hdescent : baseEnd_5893310 < baseStart_5893310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893386 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_5893386 : Nat := 118140960795 + 5893386 * 2 ^ 59
def prefixEnd_5893386 : Nat := 4983230072969 + 3 ^ 40 * 5893386 * 2
def baseEnd_5893386 : Nat := 3026139700478184333871817

theorem tailTrace_5893386 : CollatzResearch.WordTrace tailWord_5893386 prefixEnd_5893386 3026139700478184333871817 := by
  unfold tailWord_5893386
  simp only [CollatzResearch.WordTrace]
  refine ⟨53737361556819126760385003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143299630818184338027693341 53737361556819126760385003)
  ·
    refine ⟨80606042335228690140577505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53737361556819126760385003 80606042335228690140577505)
    ·
      refine ⟨60454531751421517605433129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80606042335228690140577505 60454531751421517605433129)
      ·
        refine ⟨45340898813566138204074847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60454531751421517605433129 45340898813566138204074847)
        ·
          refine ⟨68011348220349207306112271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45340898813566138204074847 68011348220349207306112271)
          ·
            refine ⟨102017022330523810959168407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68011348220349207306112271 102017022330523810959168407)
            ·
              refine ⟨153025533495785716438752611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102017022330523810959168407 153025533495785716438752611)
              ·
                refine ⟨229538300243678574658128917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153025533495785716438752611 229538300243678574658128917)
                ·
                  refine ⟨10759607823922433187099793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 229538300243678574658128917 10759607823922433187099793)
                  ·
                    refine ⟨8069705867941824890324845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10759607823922433187099793 8069705867941824890324845)
                    ·
                      refine ⟨3026139700478184333871817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069705867941824890324845 3026139700478184333871817)
                      ·
                        rfl

theorem cell23_5893386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_5893386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893386 prefixEnd_5893386 := by exact prefixLift 5893386
  have htrace : WordTrace (prefixWord ++ tailWord_5893386) baseStart_5893386 baseEnd_5893386 := by
    simpa [prefixWord, tailWord_5893386, baseEnd_5893386] using wordTrace_append hprefix tailTrace_5893386
  have hstable : (prefixWord ++ tailWord_5893386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893386).length < 2 ^ (prefixWord ++ tailWord_5893386).sum := by decide
  have hdescent : baseEnd_5893386 < baseStart_5893386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893409 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5893409 : Nat := 118140960795 + 5893409 * 2 ^ 59
def prefixEnd_5893409 : Nat := 4983230072969 + 3 ^ 40 * 5893409 * 2
def baseEnd_5893409 : Nat := 3026151510533237743884211

theorem tailTrace_5893409 : CollatzResearch.WordTrace tailWord_5893409 prefixEnd_5893409 3026151510533237743884211 := by
  unfold tailWord_5893409
  simp only [CollatzResearch.WordTrace]
  refine ⟨214950285106193181969627281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143300190070795454646418187 214950285106193181969627281)
  ·
    refine ⟨161212713829644886477220461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214950285106193181969627281 161212713829644886477220461)
    ·
      refine ⟨60454767686116832428957673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161212713829644886477220461 60454767686116832428957673)
      ·
        refine ⟨45341075764587624321718255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60454767686116832428957673 45341075764587624321718255)
        ·
          refine ⟨68011613646881436482577383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45341075764587624321718255 68011613646881436482577383)
          ·
            refine ⟨102017420470322154723866075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68011613646881436482577383 102017420470322154723866075)
            ·
              refine ⟨153026130705483232085799113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102017420470322154723866075 153026130705483232085799113)
              ·
                refine ⟨114769598029112424064349335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153026130705483232085799113 114769598029112424064349335)
                ·
                  refine ⟨172154397043668636096524003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114769598029112424064349335 172154397043668636096524003)
                  ·
                    refine ⟨258231595565502954144786005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172154397043668636096524003 258231595565502954144786005)
                    ·
                      refine ⟨3026151510533237743884211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 258231595565502954144786005 3026151510533237743884211)
                      ·
                        rfl

theorem cell23_5893409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5893409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893409 prefixEnd_5893409 := by exact prefixLift 5893409
  have htrace : WordTrace (prefixWord ++ tailWord_5893409) baseStart_5893409 baseEnd_5893409 := by
    simpa [prefixWord, tailWord_5893409, baseEnd_5893409] using wordTrace_append hprefix tailTrace_5893409
  have hstable : (prefixWord ++ tailWord_5893409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893409).length < 2 ^ (prefixWord ++ tailWord_5893409).sum := by decide
  have hdescent : baseEnd_5893409 < baseStart_5893409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893427 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 1, 4]
def baseStart_5893427 : Nat := 118140960795 + 5893427 * 2 ^ 59
def prefixEnd_5893427 : Nat := 4983230072969 + 3 ^ 40 * 5893427 * 2
def baseEnd_5893427 : Nat := 1008720251061672891153043

theorem tailTrace_5893427 : CollatzResearch.WordTrace tailWord_5893427 prefixEnd_5893427 1008720251061672891153043 := by
  unfold tailWord_5893427
  simp only [CollatzResearch.WordTrace]
  refine ⟨214950941620127971043782535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143300627746751980695855023 214950941620127971043782535)
  ·
    refine ⟨322426412430191956565673803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214950941620127971043782535 322426412430191956565673803)
    ·
      refine ⟨483639618645287934848510705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322426412430191956565673803 483639618645287934848510705)
      ·
        refine ⟨362729713983965951136383029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483639618645287934848510705 362729713983965951136383029)
        ·
          refine ⟨34005910685996807919035909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 362729713983965951136383029 34005910685996807919035909)
          ·
            refine ⟨6376108253624401484819233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34005910685996807919035909 6376108253624401484819233)
            ·
              refine ⟨4782081190218301113614425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6376108253624401484819233 4782081190218301113614425)
              ·
                refine ⟨3586560892663725835210819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4782081190218301113614425 3586560892663725835210819)
                ·
                  refine ⟨5379841338995588752816229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586560892663725835210819 5379841338995588752816229)
                  ·
                    refine ⟨1008720251061672891153043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379841338995588752816229 1008720251061672891153043)
                    ·
                      rfl

theorem cell23_5893427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 4].length) (baseStart_5893427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893427 prefixEnd_5893427 := by exact prefixLift 5893427
  have htrace : WordTrace (prefixWord ++ tailWord_5893427) baseStart_5893427 baseEnd_5893427 := by
    simpa [prefixWord, tailWord_5893427, baseEnd_5893427] using wordTrace_append hprefix tailTrace_5893427
  have hstable : (prefixWord ++ tailWord_5893427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893427).length < 2 ^ (prefixWord ++ tailWord_5893427).sum := by decide
  have hdescent : baseEnd_5893427 < baseStart_5893427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893436 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_5893436 : Nat := 118140960795 + 5893436 * 2 ^ 59
def prefixEnd_5893436 : Nat := 4983230072969 + 3 ^ 40 * 5893436 * 2
def baseEnd_5893436 : Nat := 1008721791503636379415529

theorem tailTrace_5893436 : CollatzResearch.WordTrace tailWord_5893436 prefixEnd_5893436 1008721791503636379415529 := by
  unfold tailWord_5893436
  simp only [CollatzResearch.WordTrace]
  refine ⟨107475634938547682790430081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143300846584730243720573441 107475634938547682790430081)
  ·
    refine ⟨80606726203910762092822561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107475634938547682790430081 80606726203910762092822561)
    ·
      refine ⟨60455044652933071569616921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80606726203910762092822561 60455044652933071569616921)
      ·
        refine ⟨45341283489699803677212691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60455044652933071569616921 45341283489699803677212691)
        ·
          refine ⟨68011925234549705515819037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45341283489699803677212691 68011925234549705515819037)
          ·
            refine ⟨25504471962956139568432139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68011925234549705515819037 25504471962956139568432139)
            ·
              refine ⟨38256707944434209352648209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25504471962956139568432139 38256707944434209352648209)
              ·
                refine ⟨28692530958325657014486157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38256707944434209352648209 28692530958325657014486157)
                ·
                  refine ⟨10759699109372121380432309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28692530958325657014486157 10759699109372121380432309)
                  ·
                    refine ⟨1008721791503636379415529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10759699109372121380432309 1008721791503636379415529)
                    ·
                      rfl

theorem cell23_5893436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_5893436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893436 prefixEnd_5893436 := by exact prefixLift 5893436
  have htrace : WordTrace (prefixWord ++ tailWord_5893436) baseStart_5893436 baseEnd_5893436 := by
    simpa [prefixWord, tailWord_5893436, baseEnd_5893436] using wordTrace_append hprefix tailTrace_5893436
  have hstable : (prefixWord ++ tailWord_5893436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893436).length < 2 ^ (prefixWord ++ tailWord_5893436).sum := by decide
  have hdescent : baseEnd_5893436 < baseStart_5893436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893456 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_5893456 : Nat := 118140960795 + 5893456 * 2 ^ 59
def prefixEnd_5893456 : Nat := 4983230072969 + 3 ^ 40 * 5893456 * 2
def baseEnd_5893456 : Nat := 3026175644123999059996495

theorem tailTrace_5893456 : CollatzResearch.WordTrace tailWord_5893456 prefixEnd_5893456 3026175644123999059996495 := by
  unfold tailWord_5893456
  simp only [CollatzResearch.WordTrace]
  refine ⟨107475999668511454498294111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143301332891348605997725481 107475999668511454498294111)
  ·
    refine ⟨161213999502767181747441167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107475999668511454498294111 161213999502767181747441167)
    ·
      refine ⟨241820999254150772621161751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161213999502767181747441167 241820999254150772621161751)
      ·
        refine ⟨362731498881226158931742627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241820999254150772621161751 362731498881226158931742627)
        ·
          refine ⟨544097248321839238397613941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362731498881226158931742627 544097248321839238397613941)
          ·
            refine ⟨51009117030172428599776307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 544097248321839238397613941 51009117030172428599776307)
            ·
              refine ⟨76513675545258642899664461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51009117030172428599776307 76513675545258642899664461)
              ·
                refine ⟨28692628329471991087374173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76513675545258642899664461 28692628329471991087374173)
                ·
                  refine ⟨10759735623551996657765315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28692628329471991087374173 10759735623551996657765315)
                  ·
                    refine ⟨16139603435327994986647973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10759735623551996657765315 16139603435327994986647973)
                    ·
                      refine ⟨3026175644123999059996495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16139603435327994986647973 3026175644123999059996495)
                      ·
                        rfl

theorem cell23_5893456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_5893456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893456 prefixEnd_5893456 := by exact prefixLift 5893456
  have htrace : WordTrace (prefixWord ++ tailWord_5893456) baseStart_5893456 baseEnd_5893456 := by
    simpa [prefixWord, tailWord_5893456, baseEnd_5893456] using wordTrace_append hprefix tailTrace_5893456
  have hstable : (prefixWord ++ tailWord_5893456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893456).length < 2 ^ (prefixWord ++ tailWord_5893456).sum := by decide
  have hdescent : baseEnd_5893456 < baseStart_5893456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893466 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_5893466 : Nat := 118140960795 + 5893466 * 2 ^ 59
def prefixEnd_5893466 : Nat := 4983230072969 + 3 ^ 40 * 5893466 * 2
def baseEnd_5893466 : Nat := 1008726926310181340290483

theorem tailTrace_5893466 : CollatzResearch.WordTrace tailWord_5893466 prefixEnd_5893466 1008726926310181340290483 := by
  unfold tailWord_5893466
  simp only [CollatzResearch.WordTrace]
  refine ⟨53738091016746670176113063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143301576044657787136301501 53738091016746670176113063)
  ·
    refine ⟨80607136525120005264169595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53738091016746670176113063 80607136525120005264169595)
    ·
      refine ⟨120910704787680007896254393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80607136525120005264169595 120910704787680007896254393)
      ·
        refine ⟨90683028590760005922190795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120910704787680007896254393 90683028590760005922190795)
        ·
          refine ⟨136024542886140008883286193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90683028590760005922190795 136024542886140008883286193)
          ·
            refine ⟨102018407164605006662464645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136024542886140008883286193 102018407164605006662464645)
            ·
              refine ⟨19128451343363438749212121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102018407164605006662464645 19128451343363438749212121)
              ·
                refine ⟨14346338507522579061909091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19128451343363438749212121 14346338507522579061909091)
                ·
                  refine ⟨21519507761283868592863637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14346338507522579061909091 21519507761283868592863637)
                  ·
                    refine ⟨1008726926310181340290483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21519507761283868592863637 1008726926310181340290483)
                    ·
                      rfl

theorem cell23_5893466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_5893466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893466 prefixEnd_5893466 := by exact prefixLift 5893466
  have htrace : WordTrace (prefixWord ++ tailWord_5893466) baseStart_5893466 baseEnd_5893466 := by
    simpa [prefixWord, tailWord_5893466, baseEnd_5893466] using wordTrace_append hprefix tailTrace_5893466
  have hstable : (prefixWord ++ tailWord_5893466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893466).length < 2 ^ (prefixWord ++ tailWord_5893466).sum := by decide
  have hdescent : baseEnd_5893466 < baseStart_5893466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893500 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_5893500 : Nat := 118140960795 + 5893500 * 2 ^ 59
def prefixEnd_5893500 : Nat := 4983230072969 + 3 ^ 40 * 5893500 * 2
def baseEnd_5893500 : Nat := 1008732745757598962615431

theorem tailTrace_5893500 : CollatzResearch.WordTrace tailWord_5893500 prefixEnd_5893500 1008732745757598962615431 := by
  unfold tailWord_5893500
  simp only [CollatzResearch.WordTrace]
  refine ⟨107476802074431752255594977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143302402765909003007459969 107476802074431752255594977)
  ·
    refine ⟨80607601555823814191696233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107476802074431752255594977 80607601555823814191696233)
    ·
      refine ⟨60455701166867860643772175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80607601555823814191696233 60455701166867860643772175)
      ·
        refine ⟨90683551750301790965658263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60455701166867860643772175 90683551750301790965658263)
        ·
          refine ⟨136025327625452686448487395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90683551750301790965658263 136025327625452686448487395)
          ·
            refine ⟨204037991438179029672731093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136025327625452686448487395 204037991438179029672731093)
            ·
              refine ⟨4782140424332321007954635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 204037991438179029672731093 4782140424332321007954635)
              ·
                refine ⟨7173210636498481511931953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782140424332321007954635 7173210636498481511931953)
                ·
                  refine ⟨5379907977373861133948965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7173210636498481511931953 5379907977373861133948965)
                  ·
                    refine ⟨1008732745757598962615431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379907977373861133948965 1008732745757598962615431)
                    ·
                      rfl

theorem cell23_5893500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_5893500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893500 prefixEnd_5893500 := by exact prefixLift 5893500
  have htrace : WordTrace (prefixWord ++ tailWord_5893500) baseStart_5893500 baseEnd_5893500 := by
    simpa [prefixWord, tailWord_5893500, baseEnd_5893500] using wordTrace_append hprefix tailTrace_5893500
  have hstable : (prefixWord ++ tailWord_5893500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893500).length < 2 ^ (prefixWord ++ tailWord_5893500).sum := by decide
  have hdescent : baseEnd_5893500 < baseStart_5893500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893536 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_5893536 : Nat := 118140960795 + 5893536 * 2 ^ 59
def prefixEnd_5893536 : Nat := 4983230072969 + 3 ^ 40 * 5893536 * 2
def baseEnd_5893536 : Nat := 3026216722576358746996127

theorem tailTrace_5893536 : CollatzResearch.WordTrace tailWord_5893536 prefixEnd_5893536 3026216722576358746996127 := by
  unfold tailWord_5893536
  simp only [CollatzResearch.WordTrace]
  refine ⟨107477458588366541329750231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143303278117822055106333641 107477458588366541329750231)
  ·
    refine ⟨161216187882549811994625347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107477458588366541329750231 161216187882549811994625347)
    ·
      refine ⟨241824281823824717991938021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161216187882549811994625347 241824281823824717991938021)
      ·
        refine ⟨45342052841967134623488379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241824281823824717991938021 45342052841967134623488379)
        ·
          refine ⟨68013079262950701935232569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45342052841967134623488379 68013079262950701935232569)
          ·
            refine ⟨51009809447213026451424427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68013079262950701935232569 51009809447213026451424427)
            ·
              refine ⟨76514714170819539677136641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51009809447213026451424427 76514714170819539677136641)
              ·
                refine ⟨57386035628114654757852481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76514714170819539677136641 57386035628114654757852481)
                ·
                  refine ⟨43039526721085991068389361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57386035628114654757852481 43039526721085991068389361)
                  ·
                    refine ⟨32279645040814493301292021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43039526721085991068389361 32279645040814493301292021)
                    ·
                      refine ⟨3026216722576358746996127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32279645040814493301292021 3026216722576358746996127)
                      ·
                        rfl

theorem cell23_5893536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_5893536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893536 prefixEnd_5893536 := by exact prefixLift 5893536
  have htrace : WordTrace (prefixWord ++ tailWord_5893536) baseStart_5893536 baseEnd_5893536 := by
    simpa [prefixWord, tailWord_5893536, baseEnd_5893536] using wordTrace_append hprefix tailTrace_5893536
  have hstable : (prefixWord ++ tailWord_5893536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893536).length < 2 ^ (prefixWord ++ tailWord_5893536).sum := by decide
  have hdescent : baseEnd_5893536 < baseStart_5893536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893540 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_5893540 : Nat := 118140960795 + 5893540 * 2 ^ 59
def prefixEnd_5893540 : Nat := 4983230072969 + 3 ^ 40 * 5893540 * 2
def baseEnd_5893540 : Nat := 3026218776498976731346109

theorem tailTrace_5893540 : CollatzResearch.WordTrace tailWord_5893540 prefixEnd_5893540 3026218776498976731346109 := by
  unfold tailWord_5893540
  simp only [CollatzResearch.WordTrace]
  refine ⟨107477531534359295671323037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143303375379145727561764049 107477531534359295671323037)
  ·
    refine ⟨40304074325384735876746139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107477531534359295671323037 40304074325384735876746139)
    ·
      refine ⟨60456111488077103815119209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40304074325384735876746139 60456111488077103815119209)
      ·
        refine ⟨45342083616057827861339407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60456111488077103815119209 45342083616057827861339407)
        ·
          refine ⟨68013125424086741792009111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45342083616057827861339407 68013125424086741792009111)
          ·
            refine ⟨102019688136130112688013667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68013125424086741792009111 102019688136130112688013667)
            ·
              refine ⟨153029532204195169032020501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102019688136130112688013667 153029532204195169032020501)
              ·
                refine ⟨7173259322071648548375961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153029532204195169032020501 7173259322071648548375961)
                ·
                  refine ⟨5379944491553736411281971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7173259322071648548375961 5379944491553736411281971)
                  ·
                    refine ⟨8069916737330604616922957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379944491553736411281971 8069916737330604616922957)
                    ·
                      refine ⟨3026218776498976731346109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069916737330604616922957 3026218776498976731346109)
                      ·
                        rfl

theorem cell23_5893540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_5893540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893540 prefixEnd_5893540 := by exact prefixLift 5893540
  have htrace : WordTrace (prefixWord ++ tailWord_5893540) baseStart_5893540 baseEnd_5893540 := by
    simpa [prefixWord, tailWord_5893540, baseEnd_5893540] using wordTrace_append hprefix tailTrace_5893540
  have hstable : (prefixWord ++ tailWord_5893540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893540).length < 2 ^ (prefixWord ++ tailWord_5893540).sum := by decide
  have hdescent : baseEnd_5893540 < baseStart_5893540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893557 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_5893557 : Nat := 118140960795 + 5893557 * 2 ^ 59
def prefixEnd_5893557 : Nat := 4983230072969 + 3 ^ 40 * 5893557 * 2
def baseEnd_5893557 : Nat := 3026227505670103164833531

theorem tailTrace_5893557 : CollatzResearch.WordTrace tailWord_5893557 prefixEnd_5893557 3026227505670103164833531 := by
  unfold tailWord_5893557
  simp only [CollatzResearch.WordTrace]
  refine ⟨214955683109657003246014925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143303788739771335497343283 214955683109657003246014925)
  ·
    refine ⟨80608381166121376217255597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214955683109657003246014925 80608381166121376217255597)
    ·
      refine ⟨30228142937295516081470849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80608381166121376217255597 30228142937295516081470849)
      ·
        refine ⟨22671107202971637061103137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30228142937295516081470849 22671107202971637061103137)
        ·
          refine ⟨17003330402228727795827353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22671107202971637061103137 17003330402228727795827353)
          ·
            refine ⟨12752497801671545846870515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17003330402228727795827353 12752497801671545846870515)
            ·
              refine ⟨19128746702507318770305773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12752497801671545846870515 19128746702507318770305773)
              ·
                refine ⟨7173280013440244538864665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19128746702507318770305773 7173280013440244538864665)
                ·
                  refine ⟨5379960010080183404148499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7173280013440244538864665 5379960010080183404148499)
                  ·
                    refine ⟨8069940015120275106222749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379960010080183404148499 8069940015120275106222749)
                    ·
                      refine ⟨3026227505670103164833531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8069940015120275106222749 3026227505670103164833531)
                      ·
                        rfl

theorem cell23_5893557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_5893557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893557 prefixEnd_5893557 := by exact prefixLift 5893557
  have htrace : WordTrace (prefixWord ++ tailWord_5893557) baseStart_5893557 baseEnd_5893557 := by
    simpa [prefixWord, tailWord_5893557, baseEnd_5893557] using wordTrace_append hprefix tailTrace_5893557
  have hstable : (prefixWord ++ tailWord_5893557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893557).length < 2 ^ (prefixWord ++ tailWord_5893557).sum := by decide
  have hdescent : baseEnd_5893557 < baseStart_5893557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893580 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 3, 4, 2]
def baseStart_5893580 : Nat := 118140960795 + 5893580 * 2 ^ 59
def prefixEnd_5893580 : Nat := 4983230072969 + 3 ^ 40 * 5893580 * 2
def baseEnd_5893580 : Nat := 3026239315725156574845925

theorem tailTrace_5893580 : CollatzResearch.WordTrace tailWord_5893580 prefixEnd_5893580 3026239315725156574845925 := by
  unfold tailWord_5893580
  simp only [CollatzResearch.WordTrace]
  refine ⟨107478260994286839087051097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143304347992382452116068129 107478260994286839087051097)
  ·
    refine ⟨80608695745715129315288323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107478260994286839087051097 80608695745715129315288323)
    ·
      refine ⟨120913043618572693972932485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80608695745715129315288323 120913043618572693972932485)
      ·
        refine ⟨22671195678482380119924841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120913043618572693972932485 22671195678482380119924841)
        ·
          refine ⟨17003396758861785089943631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22671195678482380119924841 17003396758861785089943631)
          ·
            refine ⟨25505095138292677634915447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17003396758861785089943631 25505095138292677634915447)
            ·
              refine ⟨38257642707439016452373171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25505095138292677634915447 38257642707439016452373171)
              ·
                refine ⟨57386464061158524678559757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38257642707439016452373171 57386464061158524678559757)
                ·
                  refine ⟨21519924022934446754459909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57386464061158524678559757 21519924022934446754459909)
                  ·
                    refine ⟨4034985754300208766461233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21519924022934446754459909 4034985754300208766461233)
                    ·
                      refine ⟨3026239315725156574845925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4034985754300208766461233 3026239315725156574845925)
                      ·
                        rfl

theorem cell23_5893580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_5893580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893580 prefixEnd_5893580 := by exact prefixLift 5893580
  have htrace : WordTrace (prefixWord ++ tailWord_5893580) baseStart_5893580 baseEnd_5893580 := by
    simpa [prefixWord, tailWord_5893580, baseEnd_5893580] using wordTrace_append hprefix tailTrace_5893580
  have hstable : (prefixWord ++ tailWord_5893580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893580).length < 2 ^ (prefixWord ++ tailWord_5893580).sum := by decide
  have hdescent : baseEnd_5893580 < baseStart_5893580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893610 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_5893610 : Nat := 118140960795 + 5893610 * 2 ^ 59
def prefixEnd_5893610 : Nat := 4983230072969 + 3 ^ 40 * 5893610 * 2
def baseEnd_5893610 : Nat := 3026254720144791457470787

theorem tailTrace_5893610 : CollatzResearch.WordTrace tailWord_5893610 prefixEnd_5893610 3026254720144791457470787 := by
  unfold tailWord_5893610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53739404044616248324423571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143305077452309995531796189 53739404044616248324423571)
  ·
    refine ⟨80609106066924372486635357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53739404044616248324423571 80609106066924372486635357)
    ·
      refine ⟨30228414775096639682488259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80609106066924372486635357 30228414775096639682488259)
      ·
        refine ⟨45342622162644959523732389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30228414775096639682488259 45342622162644959523732389)
        ·
          refine ⟨8501741655495929910699823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45342622162644959523732389 8501741655495929910699823)
          ·
            refine ⟨12752612483243894866049735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8501741655495929910699823 12752612483243894866049735)
            ·
              refine ⟨19128918724865842299074603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12752612483243894866049735 19128918724865842299074603)
              ·
                refine ⟨28693378087298763448611905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19128918724865842299074603 28693378087298763448611905)
                ·
                  refine ⟨21520033565474072586458929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28693378087298763448611905 21520033565474072586458929)
                  ·
                    refine ⟨16140025174105554439844197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21520033565474072586458929 16140025174105554439844197)
                    ·
                      refine ⟨3026254720144791457470787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16140025174105554439844197 3026254720144791457470787)
                      ·
                        rfl

theorem cell23_5893610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_5893610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893610 prefixEnd_5893610 := by exact prefixLift 5893610
  have htrace : WordTrace (prefixWord ++ tailWord_5893610) baseStart_5893610 baseEnd_5893610 := by
    simpa [prefixWord, tailWord_5893610, baseEnd_5893610] using wordTrace_append hprefix tailTrace_5893610
  have hstable : (prefixWord ++ tailWord_5893610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893610).length < 2 ^ (prefixWord ++ tailWord_5893610).sum := by decide
  have hdescent : baseEnd_5893610 < baseStart_5893610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893690 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_5893690 : Nat := 118140960795 + 5893690 * 2 ^ 59
def prefixEnd_5893690 : Nat := 4983230072969 + 3 ^ 40 * 5893690 * 2
def baseEnd_5893690 : Nat := 3026295798597151144470419

theorem tailTrace_5893690 : CollatzResearch.WordTrace tailWord_5893690 prefixEnd_5893690 3026295798597151144470419 := by
  unfold tailWord_5893690
  simp only [CollatzResearch.WordTrace]
  refine ⟨53740133504543791740151631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143307022678783444640404349 53740133504543791740151631)
  ·
    refine ⟨80610200256815687610227447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53740133504543791740151631 80610200256815687610227447)
    ·
      refine ⟨120915300385223531415341171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80610200256815687610227447 120915300385223531415341171)
      ·
        refine ⟨181372950577835297123011757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120915300385223531415341171 181372950577835297123011757)
        ·
          refine ⟨68014856466688236421129409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181372950577835297123011757 68014856466688236421129409)
          ·
            refine ⟨51011142350016177315847057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68014856466688236421129409 51011142350016177315847057)
            ·
              refine ⟨38258356762512132986885293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51011142350016177315847057 38258356762512132986885293)
              ·
                refine ⟨14346883785942049870081985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38258356762512132986885293 14346883785942049870081985)
                ·
                  refine ⟨10760162839456537402561489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14346883785942049870081985 10760162839456537402561489)
                  ·
                    refine ⟨8070122129592403051921117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10760162839456537402561489 8070122129592403051921117)
                    ·
                      refine ⟨3026295798597151144470419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8070122129592403051921117 3026295798597151144470419)
                      ·
                        rfl

theorem cell23_5893690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_5893690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893690 prefixEnd_5893690 := by exact prefixLift 5893690
  have htrace : WordTrace (prefixWord ++ tailWord_5893690) baseStart_5893690 baseEnd_5893690 := by
    simpa [prefixWord, tailWord_5893690, baseEnd_5893690] using wordTrace_append hprefix tailTrace_5893690
  have hstable : (prefixWord ++ tailWord_5893690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893690).length < 2 ^ (prefixWord ++ tailWord_5893690).sum := by decide
  have hdescent : baseEnd_5893690 < baseStart_5893690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893811 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 1, 2, 2]
def baseStart_5893811 : Nat := 118140960795 + 5893811 * 2 ^ 59
def prefixEnd_5893811 : Nat := 4983230072969 + 3 ^ 40 * 5893811 * 2
def baseEnd_5893811 : Nat := 3026357929756345171057363

theorem tailTrace_5893811 : CollatzResearch.WordTrace tailWord_5893811 prefixEnd_5893811 3026357929756345171057363 := by
  unfold tailWord_5893811
  simp only [CollatzResearch.WordTrace]
  refine ⟨214964947250736804625761287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143309964833824536417174191 214964947250736804625761287)
  ·
    refine ⟨322447420876105206938641931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214964947250736804625761287 322447420876105206938641931)
    ·
      refine ⟨483671131314157810407962897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322447420876105206938641931 483671131314157810407962897)
      ·
        refine ⟨362753348485618357805972173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483671131314157810407962897 362753348485618357805972173)
        ·
          refine ⟨136032505682106884177239565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362753348485618357805972173 136032505682106884177239565)
          ·
            refine ⟨51012189630790081566464837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136032505682106884177239565 51012189630790081566464837)
            ·
              refine ⟨9564785555773140293712157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51012189630790081566464837 9564785555773140293712157)
              ·
                refine ⟨3586794583414927610142059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9564785555773140293712157 3586794583414927610142059)
                ·
                  refine ⟨5380191875122391415213089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586794583414927610142059 5380191875122391415213089)
                  ·
                    refine ⟨4035143906341793561409817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5380191875122391415213089 4035143906341793561409817)
                    ·
                      refine ⟨3026357929756345171057363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035143906341793561409817 3026357929756345171057363)
                      ·
                        rfl

theorem cell23_5893811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 2, 2].length) (baseStart_5893811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893811 prefixEnd_5893811 := by exact prefixLift 5893811
  have htrace : WordTrace (prefixWord ++ tailWord_5893811) baseStart_5893811 baseEnd_5893811 := by
    simpa [prefixWord, tailWord_5893811, baseEnd_5893811] using wordTrace_append hprefix tailTrace_5893811
  have hstable : (prefixWord ++ tailWord_5893811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893811).length < 2 ^ (prefixWord ++ tailWord_5893811).sum := by decide
  have hdescent : baseEnd_5893811 < baseStart_5893811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893843 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 8]
def baseStart_5893843 : Nat := 118140960795 + 5893843 * 2 ^ 59
def prefixEnd_5893843 : Nat := 4983230072969 + 3 ^ 40 * 5893843 * 2
def baseEnd_5893843 : Nat := 1008791453712429681952405

theorem tailTrace_5893843 : CollatzResearch.WordTrace tailWord_5893843 prefixEnd_5893843 1008791453712429681952405 := by
  unfold tailWord_5893843
  simp only [CollatzResearch.WordTrace]
  refine ⟨214966114386620874090926183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143310742924413916060617455 214966114386620874090926183)
  ·
    refine ⟨322449171579931311136389275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214966114386620874090926183 322449171579931311136389275)
    ·
      refine ⟨483673757369896966704583913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322449171579931311136389275 483673757369896966704583913)
      ·
        refine ⟨362755318027422725028437935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483673757369896966704583913 362755318027422725028437935)
        ·
          refine ⟨544132977041134087542656903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362755318027422725028437935 544132977041134087542656903)
          ·
            refine ⟨816199465561701131313985355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544132977041134087542656903 816199465561701131313985355)
            ·
              refine ⟨1224299198342551696970978033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816199465561701131313985355 1224299198342551696970978033)
              ·
                refine ⟨918224398756913772728233525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224299198342551696970978033 918224398756913772728233525)
                ·
                  refine ⟨86083537383460666193271893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918224398756913772728233525 86083537383460666193271893)
                  ·
                    refine ⟨1008791453712429681952405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86083537383460666193271893 1008791453712429681952405)
                    ·
                      rfl

theorem cell23_5893843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_5893843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893843 prefixEnd_5893843 := by exact prefixLift 5893843
  have htrace : WordTrace (prefixWord ++ tailWord_5893843) baseStart_5893843 baseEnd_5893843 := by
    simpa [prefixWord, tailWord_5893843, baseEnd_5893843] using wordTrace_append hprefix tailTrace_5893843
  have hstable : (prefixWord ++ tailWord_5893843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893843).length < 2 ^ (prefixWord ++ tailWord_5893843).sum := by decide
  have hdescent : baseEnd_5893843 < baseStart_5893843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893844 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5893844 : Nat := 118140960795 + 5893844 * 2 ^ 59
def prefixEnd_5893844 : Nat := 4983230072969 + 3 ^ 40 * 5893844 * 2
def baseEnd_5893844 : Nat := 3026374874617943541944711

theorem tailTrace_5893844 : CollatzResearch.WordTrace tailWord_5893844 prefixEnd_5893844 3026374874617943541944711 := by
  unfold tailWord_5893844
  simp only [CollatzResearch.WordTrace]
  refine ⟨107483075429808625630856293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143310767239744834174475057 107483075429808625630856293)
  ·
    refine ⟨20153076643089117305785555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107483075429808625630856293 20153076643089117305785555)
    ·
      refine ⟨30229614964633675958678333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20153076643089117305785555 30229614964633675958678333)
      ·
        refine ⟨11336105611737628484504375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30229614964633675958678333 11336105611737628484504375)
        ·
          refine ⟨17004158417606442726756563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11336105611737628484504375 17004158417606442726756563)
          ·
            refine ⟨25506237626409664090134845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17004158417606442726756563 25506237626409664090134845)
            ·
              refine ⟨9564839109903624033800567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25506237626409664090134845 9564839109903624033800567)
              ·
                refine ⟨14347258664855436050700851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9564839109903624033800567 14347258664855436050700851)
                ·
                  refine ⟨21520887997283154076051277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14347258664855436050700851 21520887997283154076051277)
                  ·
                    refine ⟨8070332998981182778519229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21520887997283154076051277 8070332998981182778519229)
                    ·
                      refine ⟨3026374874617943541944711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8070332998981182778519229 3026374874617943541944711)
                      ·
                        rfl

theorem cell23_5893844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5893844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893844 prefixEnd_5893844 := by exact prefixLift 5893844
  have htrace : WordTrace (prefixWord ++ tailWord_5893844) baseStart_5893844 baseEnd_5893844 := by
    simpa [prefixWord, tailWord_5893844, baseEnd_5893844] using wordTrace_append hprefix tailTrace_5893844
  have hstable : (prefixWord ++ tailWord_5893844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893844).length < 2 ^ (prefixWord ++ tailWord_5893844).sum := by decide
  have hdescent : baseEnd_5893844 < baseStart_5893844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893867 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 1, 4, 2]
def baseStart_5893867 : Nat := 118140960795 + 5893867 * 2 ^ 59
def prefixEnd_5893867 : Nat := 4983230072969 + 3 ^ 40 * 5893867 * 2
def baseEnd_5893867 : Nat := 3026386684672996951957105

theorem tailTrace_5893867 : CollatzResearch.WordTrace tailWord_5893867 prefixEnd_5893867 3026386684672996951957105 := by
  unfold tailWord_5893867
  simp only [CollatzResearch.WordTrace]
  refine ⟨214966989738533926189799855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143311326492355950793199903 214966989738533926189799855)
  ·
    refine ⟨322450484607800889284699783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214966989738533926189799855 322450484607800889284699783)
    ·
      refine ⟨483675726911701333927049675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322450484607800889284699783 483675726911701333927049675)
      ·
        refine ⟨725513590367552000890574513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483675726911701333927049675 725513590367552000890574513)
        ·
          refine ⟨544135192775664000667930885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725513590367552000890574513 544135192775664000667930885)
          ·
            refine ⟨102025348645437000125237041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 544135192775664000667930885 102025348645437000125237041)
            ·
              refine ⟨76519011484077750093927781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102025348645437000125237041 76519011484077750093927781)
              ·
                refine ⟨14347314653264578142611459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76519011484077750093927781 14347314653264578142611459)
                ·
                  refine ⟨21520971979896867213917189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14347314653264578142611459 21520971979896867213917189)
                  ·
                    refine ⟨4035182246230662602609473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21520971979896867213917189 4035182246230662602609473)
                    ·
                      refine ⟨3026386684672996951957105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035182246230662602609473 3026386684672996951957105)
                      ·
                        rfl

theorem cell23_5893867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4, 2].length) (baseStart_5893867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893867 prefixEnd_5893867 := by exact prefixLift 5893867
  have htrace : WordTrace (prefixWord ++ tailWord_5893867) baseStart_5893867 baseEnd_5893867 := by
    simpa [prefixWord, tailWord_5893867, baseEnd_5893867] using wordTrace_append hprefix tailTrace_5893867
  have hstable : (prefixWord ++ tailWord_5893867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893867).length < 2 ^ (prefixWord ++ tailWord_5893867).sum := by decide
  have hdescent : baseEnd_5893867 < baseStart_5893867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893880 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_5893880 : Nat := 118140960795 + 5893880 * 2 ^ 59
def prefixEnd_5893880 : Nat := 4983230072969 + 3 ^ 40 * 5893880 * 2
def baseEnd_5893880 : Nat := 3026393359921505401094545

theorem tailTrace_5893880 : CollatzResearch.WordTrace tailWord_5893880 prefixEnd_5893880 3026393359921505401094545 := by
  unfold tailWord_5893880
  simp only [CollatzResearch.WordTrace]
  refine ⟨107483731943743414705011547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143311642591657886273348729 107483731943743414705011547)
  ·
    refine ⟨161225597915615122057517321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107483731943743414705011547 161225597915615122057517321)
    ·
      refine ⟨120919198436711341543137991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161225597915615122057517321 120919198436711341543137991)
      ·
        refine ⟨181378797655067012314706987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120919198436711341543137991 181378797655067012314706987)
        ·
          refine ⟨272068196482600518472060481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181378797655067012314706987 272068196482600518472060481)
          ·
            refine ⟨204051147361950388854045361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272068196482600518472060481 204051147361950388854045361)
            ·
              refine ⟨153038360521462791640534021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204051147361950388854045361 153038360521462791640534021)
              ·
                refine ⟨28694692597774273432600129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153038360521462791640534021 28694692597774273432600129)
                ·
                  refine ⟨21521019448330705074450097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28694692597774273432600129 21521019448330705074450097)
                  ·
                    refine ⟨16140764586248028805837573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21521019448330705074450097 16140764586248028805837573)
                    ·
                      refine ⟨3026393359921505401094545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16140764586248028805837573 3026393359921505401094545)
                      ·
                        rfl

theorem cell23_5893880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_5893880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893880 prefixEnd_5893880 := by exact prefixLift 5893880
  have htrace : WordTrace (prefixWord ++ tailWord_5893880) baseStart_5893880 baseEnd_5893880 := by
    simpa [prefixWord, tailWord_5893880, baseEnd_5893880] using wordTrace_append hprefix tailTrace_5893880
  have hstable : (prefixWord ++ tailWord_5893880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893880).length < 2 ^ (prefixWord ++ tailWord_5893880).sum := by decide
  have hdescent : baseEnd_5893880 < baseStart_5893880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893884 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_5893884 : Nat := 118140960795 + 5893884 * 2 ^ 59
def prefixEnd_5893884 : Nat := 4983230072969 + 3 ^ 40 * 5893884 * 2
def baseEnd_5893884 : Nat := 3026395413844123385444527

theorem tailTrace_5893884 : CollatzResearch.WordTrace tailWord_5893884 prefixEnd_5893884 3026395413844123385444527 := by
  unfold tailWord_5893884
  simp only [CollatzResearch.WordTrace]
  refine ⟨107483804889736169046584353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143311739852981558728779137 107483804889736169046584353)
  ·
    refine ⟨80612853667302126784938265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107483804889736169046584353 80612853667302126784938265)
    ·
      refine ⟨60459640250476595088703699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80612853667302126784938265 60459640250476595088703699)
      ·
        refine ⟨90689460375714892633055549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60459640250476595088703699 90689460375714892633055549)
        ·
          refine ⟨34008547640893084737395831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90689460375714892633055549 34008547640893084737395831)
          ·
            refine ⟨51012821461339627106093747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34008547640893084737395831 51012821461339627106093747)
            ·
              refine ⟨76519232192009440659140621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51012821461339627106093747 76519232192009440659140621)
              ·
                refine ⟨28694712072003540247177733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76519232192009440659140621 28694712072003540247177733)
                ·
                  refine ⟨5380258513500663796345825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28694712072003540247177733 5380258513500663796345825)
                  ·
                    refine ⟨4035193885125497847259369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5380258513500663796345825 4035193885125497847259369)
                    ·
                      refine ⟨3026395413844123385444527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035193885125497847259369 3026395413844123385444527)
                      ·
                        rfl

theorem cell23_5893884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_5893884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893884 prefixEnd_5893884 := by exact prefixLift 5893884
  have htrace : WordTrace (prefixWord ++ tailWord_5893884) baseStart_5893884 baseEnd_5893884 := by
    simpa [prefixWord, tailWord_5893884, baseEnd_5893884] using wordTrace_append hprefix tailTrace_5893884
  have hstable : (prefixWord ++ tailWord_5893884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893884).length < 2 ^ (prefixWord ++ tailWord_5893884).sum := by decide
  have hdescent : baseEnd_5893884 < baseStart_5893884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893895 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5893895 : Nat := 118140960795 + 5893895 * 2 ^ 59
def prefixEnd_5893895 : Nat := 4983230072969 + 3 ^ 40 * 5893895 * 2
def baseEnd_5893895 : Nat := 3026401062131322842406977

theorem tailTrace_5893895 : CollatzResearch.WordTrace tailWord_5893895 prefixEnd_5893895 3026401062131322842406977 := by
  unfold tailWord_5893895
  simp only [CollatzResearch.WordTrace]
  refine ⟨214968010982432486971819139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143312007321621657981212759 214968010982432486971819139)
  ·
    refine ⟨322452016473648730457728709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214968010982432486971819139 322452016473648730457728709)
    ·
      refine ⟨60459753088809136960824133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322452016473648730457728709 60459753088809136960824133)
      ·
        refine ⟨11336203704151713180154525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60459753088809136960824133 11336203704151713180154525)
        ·
          refine ⟨4251076389056892442557947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11336203704151713180154525 4251076389056892442557947)
          ·
            refine ⟨6376614583585338663836921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251076389056892442557947 6376614583585338663836921)
            ·
              refine ⟨4782460937689003997877691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6376614583585338663836921 4782460937689003997877691)
              ·
                refine ⟨7173691406533505996816537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782460937689003997877691 7173691406533505996816537)
                ·
                  refine ⟨5380268554900129497612403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7173691406533505996816537 5380268554900129497612403)
                  ·
                    refine ⟨8070402832350194246418605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5380268554900129497612403 8070402832350194246418605)
                    ·
                      refine ⟨3026401062131322842406977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8070402832350194246418605 3026401062131322842406977)
                      ·
                        rfl

theorem cell23_5893895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5893895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893895 prefixEnd_5893895 := by exact prefixLift 5893895
  have htrace : WordTrace (prefixWord ++ tailWord_5893895) baseStart_5893895 baseEnd_5893895 := by
    simpa [prefixWord, tailWord_5893895, baseEnd_5893895] using wordTrace_append hprefix tailTrace_5893895
  have hstable : (prefixWord ++ tailWord_5893895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893895).length < 2 ^ (prefixWord ++ tailWord_5893895).sum := by decide
  have hdescent : baseEnd_5893895 < baseStart_5893895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893937 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_5893937 : Nat := 118140960795 + 5893937 * 2 ^ 59
def prefixEnd_5893937 : Nat := 4983230072969 + 3 ^ 40 * 5893937 * 2
def baseEnd_5893937 : Nat := 1008807542772937226027261

theorem tailTrace_5893937 : CollatzResearch.WordTrace tailWord_5893937 prefixEnd_5893937 1008807542772937226027261 := by
  unfold tailWord_5893937
  simp only [CollatzResearch.WordTrace]
  refine ⟨214969542848280328144848065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143313028565520218763232043 214969542848280328144848065)
  ·
    refine ⟨161227157136210246108636049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214969542848280328144848065 161227157136210246108636049)
    ·
      refine ⟨120920367852157684581477037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161227157136210246108636049 120920367852157684581477037)
      ·
        refine ⟨45345137944559131718053889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120920367852157684581477037 45345137944559131718053889)
        ·
          refine ⟨34008853458419348788540417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45345137944559131718053889 34008853458419348788540417)
          ·
            refine ⟨25506640093814511591405313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34008853458419348788540417 25506640093814511591405313)
            ·
              refine ⟨19129980070360883693553985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25506640093814511591405313 19129980070360883693553985)
              ·
                refine ⟨14347485052770662770165489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19129980070360883693553985 14347485052770662770165489)
                ·
                  refine ⟨10760613789577997077624117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14347485052770662770165489 10760613789577997077624117)
                  ·
                    refine ⟨1008807542772937226027261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10760613789577997077624117 1008807542772937226027261)
                    ·
                      rfl

theorem cell23_5893937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_5893937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893937 prefixEnd_5893937 := by exact prefixLift 5893937
  have htrace : WordTrace (prefixWord ++ tailWord_5893937) baseStart_5893937 baseEnd_5893937 := by
    simpa [prefixWord, tailWord_5893937, baseEnd_5893937] using wordTrace_append hprefix tailTrace_5893937
  have hstable : (prefixWord ++ tailWord_5893937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893937).length < 2 ^ (prefixWord ++ tailWord_5893937).sum := by decide
  have hdescent : baseEnd_5893937 < baseStart_5893937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5893977 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_5893977 : Nat := 118140960795 + 5893977 * 2 ^ 59
def prefixEnd_5893977 : Nat := 4983230072969 + 3 ^ 40 * 5893977 * 2
def baseEnd_5893977 : Nat := 3026443167544991521581599

theorem tailTrace_5893977 : CollatzResearch.WordTrace tailWord_5893977 prefixEnd_5893977 3026443167544991521581599 := by
  unfold tailWord_5893977
  simp only [CollatzResearch.WordTrace]
  refine ⟨214971001768135414976304185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143314001178756943317536123 214971001768135414976304185)
  ·
    refine ⟨161228251326101561232228139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214971001768135414976304185 161228251326101561232228139)
    ·
      refine ⟨241842376989152341848342209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161228251326101561232228139 241842376989152341848342209)
      ·
        refine ⟨181381782741864256386256657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241842376989152341848342209 181381782741864256386256657)
        ·
          refine ⟨136036337056398192289692493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181381782741864256386256657 136036337056398192289692493)
          ·
            refine ⟨51013626396149322108634685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136036337056398192289692493 51013626396149322108634685)
            ·
              refine ⟨19130109898555995790738007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51013626396149322108634685 19130109898555995790738007)
              ·
                refine ⟨28695164847833993686107011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19130109898555995790738007 28695164847833993686107011)
                ·
                  refine ⟨43042747271750990529160517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28695164847833993686107011 43042747271750990529160517)
                  ·
                    refine ⟨8070515113453310724217597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43042747271750990529160517 8070515113453310724217597)
                    ·
                      refine ⟨3026443167544991521581599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8070515113453310724217597 3026443167544991521581599)
                      ·
                        rfl

theorem cell23_5893977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_5893977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5893977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5893977 prefixEnd_5893977 := by exact prefixLift 5893977
  have htrace : WordTrace (prefixWord ++ tailWord_5893977) baseStart_5893977 baseEnd_5893977 := by
    simpa [prefixWord, tailWord_5893977, baseEnd_5893977] using wordTrace_append hprefix tailTrace_5893977
  have hstable : (prefixWord ++ tailWord_5893977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5893977).length < 2 ^ (prefixWord ++ tailWord_5893977).sum := by decide
  have hdescent : baseEnd_5893977 < baseStart_5893977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5893977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894067 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5]
def baseStart_5894067 : Nat := 118140960795 + 5894067 * 2 ^ 59
def prefixEnd_5894067 : Nat := 4983230072969 + 3 ^ 40 * 5894067 * 2
def baseEnd_5894067 : Nat := 3026489380803896169456185

theorem tailTrace_5894067 : CollatzResearch.WordTrace tailWord_5894067 prefixEnd_5894067 3026489380803896169456185 := by
  unfold tailWord_5894067
  simp only [CollatzResearch.WordTrace]
  refine ⟨214974284337809360347080455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143316189558539573564720303 214974284337809360347080455)
  ·
    refine ⟨322461426506714040520620683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214974284337809360347080455 322461426506714040520620683)
    ·
      refine ⟨483692139760071060780931025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322461426506714040520620683 483692139760071060780931025)
      ·
        refine ⟨362769104820053295585698269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483692139760071060780931025 362769104820053295585698269)
        ·
          refine ⟨136038414307519985844636851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362769104820053295585698269 136038414307519985844636851)
          ·
            refine ⟨204057621461279978766955277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136038414307519985844636851 204057621461279978766955277)
            ·
              refine ⟨76521608047979992037608229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204057621461279978766955277 76521608047979992037608229)
              ·
                refine ⟨14347801508996248507051543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76521608047979992037608229 14347801508996248507051543)
                ·
                  refine ⟨21521702263494372760577315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14347801508996248507051543 21521702263494372760577315)
                  ·
                    refine ⟨32282553395241559140865973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21521702263494372760577315 32282553395241559140865973)
                    ·
                      refine ⟨3026489380803896169456185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32282553395241559140865973 3026489380803896169456185)
                      ·
                        rfl

theorem cell23_5894067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_5894067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894067 prefixEnd_5894067 := by exact prefixLift 5894067
  have htrace : WordTrace (prefixWord ++ tailWord_5894067) baseStart_5894067 baseEnd_5894067 := by
    simpa [prefixWord, tailWord_5894067, baseEnd_5894067] using wordTrace_append hprefix tailTrace_5894067
  have hstable : (prefixWord ++ tailWord_5894067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894067).length < 2 ^ (prefixWord ++ tailWord_5894067).sum := by decide
  have hdescent : baseEnd_5894067 < baseStart_5894067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894094 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5894094 : Nat := 118140960795 + 5894094 * 2 ^ 59
def prefixEnd_5894094 : Nat := 4983230072969 + 3 ^ 40 * 5894094 * 2
def baseEnd_5894094 : Nat := 3026503244781567563818561

theorem tailTrace_5894094 : CollatzResearch.WordTrace tailWord_5894094 prefixEnd_5894094 3026503244781567563818561 := by
  unfold tailWord_5894094
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871908638588942994789167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143316846072474362638875557 26871908638588942994789167)
  ·
    refine ⟨40307862957883414492183751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26871908638588942994789167 40307862957883414492183751)
    ·
      refine ⟨60461794436825121738275627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40307862957883414492183751 60461794436825121738275627)
      ·
        refine ⟨90692691655237682607413441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60461794436825121738275627 90692691655237682607413441)
        ·
          refine ⟨68019518741428261955560081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90692691655237682607413441 68019518741428261955560081)
          ·
            refine ⟨51014639056071196466670061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68019518741428261955560081 51014639056071196466670061)
            ·
              refine ⟨19130489646026698675001273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51014639056071196466670061 19130489646026698675001273)
              ·
                refine ⟨14347867234520024006250955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19130489646026698675001273 14347867234520024006250955)
                ·
                  refine ⟨21521800851780036009376433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14347867234520024006250955 21521800851780036009376433)
                  ·
                    refine ⟨16141350638835027007032325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21521800851780036009376433 16141350638835027007032325)
                    ·
                      refine ⟨3026503244781567563818561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16141350638835027007032325 3026503244781567563818561)
                      ·
                        rfl

theorem cell23_5894094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5894094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894094 prefixEnd_5894094 := by exact prefixLift 5894094
  have htrace : WordTrace (prefixWord ++ tailWord_5894094) baseStart_5894094 baseEnd_5894094 := by
    simpa [prefixWord, tailWord_5894094, baseEnd_5894094] using wordTrace_append hprefix tailTrace_5894094
  have hstable : (prefixWord ++ tailWord_5894094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894094).length < 2 ^ (prefixWord ++ tailWord_5894094).sum := by decide
  have hdescent : baseEnd_5894094 < baseStart_5894094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894101 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5894101 : Nat := 118140960795 + 5894101 * 2 ^ 59
def prefixEnd_5894101 : Nat := 4983230072969 + 3 ^ 40 * 5894101 * 2
def baseEnd_5894101 : Nat := 3026506839146149036431029

theorem tailTrace_5894101 : CollatzResearch.WordTrace tailWord_5894101 prefixEnd_5894101 3026506839146149036431029 := by
  unfold tailWord_5894101
  simp only [CollatzResearch.WordTrace]
  refine ⟨214975524419686184153818157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143317016279790789435878771 214975524419686184153818157)
  ·
    refine ⟨80615821657382319057681809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214975524419686184153818157 80615821657382319057681809)
    ·
      refine ⟨60461866243036739293261357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80615821657382319057681809 60461866243036739293261357)
      ·
        refine ⟨22673199841138777234973009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60461866243036739293261357 22673199841138777234973009)
        ·
          refine ⟨17004899880854082926229757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22673199841138777234973009 17004899880854082926229757)
          ·
            refine ⟨6376837455320281097336159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17004899880854082926229757 6376837455320281097336159)
            ·
              refine ⟨9565256182980421646004239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376837455320281097336159 9565256182980421646004239)
              ·
                refine ⟨14347884274470632469006359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9565256182980421646004239 14347884274470632469006359)
                ·
                  refine ⟨21521826411705948703509539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14347884274470632469006359 21521826411705948703509539)
                  ·
                    refine ⟨32282739617558923055264309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21521826411705948703509539 32282739617558923055264309)
                    ·
                      refine ⟨3026506839146149036431029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32282739617558923055264309 3026506839146149036431029)
                      ·
                        rfl

theorem cell23_5894101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5894101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894101 prefixEnd_5894101 := by exact prefixLift 5894101
  have htrace : WordTrace (prefixWord ++ tailWord_5894101) baseStart_5894101 baseEnd_5894101 := by
    simpa [prefixWord, tailWord_5894101, baseEnd_5894101] using wordTrace_append hprefix tailTrace_5894101
  have hstable : (prefixWord ++ tailWord_5894101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894101).length < 2 ^ (prefixWord ++ tailWord_5894101).sum := by decide
  have hdescent : baseEnd_5894101 < baseStart_5894101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894109 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5894109 : Nat := 118140960795 + 5894109 * 2 ^ 59
def prefixEnd_5894109 : Nat := 4983230072969 + 3 ^ 40 * 5894109 * 2
def baseEnd_5894109 : Nat := 3026510946991385005130993

theorem tailTrace_5894109 : CollatzResearch.WordTrace tailWord_5894109 prefixEnd_5894109 3026510946991385005130993 := by
  unfold tailWord_5894109
  simp only [CollatzResearch.WordTrace]
  refine ⟨214975816203657201520109381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143317210802438134346739587 214975816203657201520109381)
  ·
    refine ⟨40307965538185725285020509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214975816203657201520109381 40307965538185725285020509)
    ·
      refine ⟨15115487076819646981882691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40307965538185725285020509 15115487076819646981882691)
      ·
        refine ⟨22673230615229470472824037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15115487076819646981882691 22673230615229470472824037)
        ·
          refine ⟨4251230740355525713654507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22673230615229470472824037 4251230740355525713654507)
          ·
            refine ⟨6376846110533288570481761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251230740355525713654507 6376846110533288570481761)
            ·
              refine ⟨4782634582899966427861321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6376846110533288570481761 4782634582899966427861321)
              ·
                refine ⟨3586975937174974820895991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4782634582899966427861321 3586975937174974820895991)
                ·
                  refine ⟨5380463905762462231343987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586975937174974820895991 5380463905762462231343987)
                  ·
                    refine ⟨8070695858643693347015981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5380463905762462231343987 8070695858643693347015981)
                    ·
                      refine ⟨3026510946991385005130993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8070695858643693347015981 3026510946991385005130993)
                      ·
                        rfl

theorem cell23_5894109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5894109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894109 prefixEnd_5894109 := by exact prefixLift 5894109
  have htrace : WordTrace (prefixWord ++ tailWord_5894109) baseStart_5894109 baseEnd_5894109 := by
    simpa [prefixWord, tailWord_5894109, baseEnd_5894109] using wordTrace_append hprefix tailTrace_5894109
  have hstable : (prefixWord ++ tailWord_5894109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894109).length < 2 ^ (prefixWord ++ tailWord_5894109).sum := by decide
  have hdescent : baseEnd_5894109 < baseStart_5894109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894115 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5894115 : Nat := 118140960795 + 5894115 * 2 ^ 59
def prefixEnd_5894115 : Nat := 4983230072969 + 3 ^ 40 * 5894115 * 2
def baseEnd_5894115 : Nat := 3026514027875311981655965

theorem tailTrace_5894115 : CollatzResearch.WordTrace tailWord_5894115 prefixEnd_5894115 3026514027875311981655965 := by
  unfold tailWord_5894115
  simp only [CollatzResearch.WordTrace]
  refine ⟨214976035041635464544827799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143317356694423643029885199 214976035041635464544827799)
  ·
    refine ⟨322464052562453196817241699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214976035041635464544827799 322464052562453196817241699)
    ·
      refine ⟨483696078843679795225862549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322464052562453196817241699 483696078843679795225862549)
      ·
        refine ⟨22673253695797490401212307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 483696078843679795225862549 22673253695797490401212307)
        ·
          refine ⟨34009880543696235601818461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22673253695797490401212307 34009880543696235601818461)
          ·
            refine ⟨12753705203886088350681923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34009880543696235601818461 12753705203886088350681923)
            ·
              refine ⟨19130557805829132526022885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12753705203886088350681923 19130557805829132526022885)
              ·
                refine ⟨3586979588592962348629291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19130557805829132526022885 3586979588592962348629291)
                ·
                  refine ⟨5380469382889443522943937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586979588592962348629291 5380469382889443522943937)
                  ·
                    refine ⟨4035352037167082642207953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5380469382889443522943937 4035352037167082642207953)
                    ·
                      refine ⟨3026514027875311981655965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035352037167082642207953 3026514027875311981655965)
                      ·
                        rfl

theorem cell23_5894115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5894115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894115 prefixEnd_5894115 := by exact prefixLift 5894115
  have htrace : WordTrace (prefixWord ++ tailWord_5894115) baseStart_5894115 baseEnd_5894115 := by
    simpa [prefixWord, tailWord_5894115, baseEnd_5894115] using wordTrace_append hprefix tailTrace_5894115
  have hstable : (prefixWord ++ tailWord_5894115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894115).length < 2 ^ (prefixWord ++ tailWord_5894115).sum := by decide
  have hdescent : baseEnd_5894115 < baseStart_5894115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894141 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_5894141 : Nat := 118140960795 + 5894141 * 2 ^ 59
def prefixEnd_5894141 : Nat := 4983230072969 + 3 ^ 40 * 5894141 * 2
def baseEnd_5894141 : Nat := 3026527378372328879930845

theorem tailTrace_5894141 : CollatzResearch.WordTrace tailWord_5894141 prefixEnd_5894141 3026527378372328879930845 := by
  unfold tailWord_5894141
  simp only [CollatzResearch.WordTrace]
  refine ⟨214976983339541270985274277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143317988893027513990182851 214976983339541270985274277)
  ·
    refine ⟨40308184376163988309738927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214976983339541270985274277 40308184376163988309738927)
    ·
      refine ⟨60462276564245982464608391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40308184376163988309738927 60462276564245982464608391)
      ·
        refine ⟨90693414846368973696912587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60462276564245982464608391 90693414846368973696912587)
        ·
          refine ⟨136040122269553460545368881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90693414846368973696912587 136040122269553460545368881)
          ·
            refine ⟨102030091702165095409026661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136040122269553460545368881 102030091702165095409026661)
            ·
              refine ⟨19130642194155955389192499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102030091702165095409026661 19130642194155955389192499)
              ·
                refine ⟨28695963291233933083788749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19130642194155955389192499 28695963291233933083788749)
                ·
                  refine ⟨10760986234212724906420781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28695963291233933083788749 10760986234212724906420781)
                  ·
                    refine ⟨4035369837829771839907793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10760986234212724906420781 4035369837829771839907793)
                    ·
                      refine ⟨3026527378372328879930845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035369837829771839907793 3026527378372328879930845)
                      ·
                        rfl

theorem cell23_5894141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_5894141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894141 prefixEnd_5894141 := by exact prefixLift 5894141
  have htrace : WordTrace (prefixWord ++ tailWord_5894141) baseStart_5894141 baseEnd_5894141 := by
    simpa [prefixWord, tailWord_5894141, baseEnd_5894141] using wordTrace_append hprefix tailTrace_5894141
  have hstable : (prefixWord ++ tailWord_5894141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894141).length < 2 ^ (prefixWord ++ tailWord_5894141).sum := by decide
  have hdescent : baseEnd_5894141 < baseStart_5894141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894158 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_5894158 : Nat := 118140960795 + 5894158 * 2 ^ 59
def prefixEnd_5894158 : Nat := 4983230072969 + 3 ^ 40 * 5894158 * 2
def baseEnd_5894158 : Nat := 3026536107543455313418267

theorem tailTrace_5894158 : CollatzResearch.WordTrace tailWord_5894158 prefixEnd_5894158 3026536107543455313418267 := by
  unfold tailWord_5894158
  simp only [CollatzResearch.WordTrace]
  refine ⟨26872200422559960361080391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143318402253653121925762085 26872200422559960361080391)
  ·
    refine ⟨40308300633839940541620587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26872200422559960361080391 40308300633839940541620587)
    ·
      refine ⟨60462450950759910812430881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40308300633839940541620587 60462450950759910812430881)
      ·
        refine ⟨45346838213069933109323161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60462450950759910812430881 45346838213069933109323161)
        ·
          refine ⟨34010128659802449831992371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45346838213069933109323161 34010128659802449831992371)
          ·
            refine ⟨51015192989703674747988557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34010128659802449831992371 51015192989703674747988557)
            ·
              refine ⟨19130697371138878030495709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51015192989703674747988557 19130697371138878030495709)
              ·
                refine ⟨7174011514177079261435891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19130697371138878030495709 7174011514177079261435891)
                ·
                  refine ⟨10761017271265618892153837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174011514177079261435891 10761017271265618892153837)
                  ·
                    refine ⟨4035381476724607084557689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10761017271265618892153837 4035381476724607084557689)
                    ·
                      refine ⟨3026536107543455313418267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035381476724607084557689 3026536107543455313418267)
                      ·
                        rfl

theorem cell23_5894158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_5894158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894158 prefixEnd_5894158 := by exact prefixLift 5894158
  have htrace : WordTrace (prefixWord ++ tailWord_5894158) baseStart_5894158 baseEnd_5894158 := by
    simpa [prefixWord, tailWord_5894158, baseEnd_5894158] using wordTrace_append hprefix tailTrace_5894158
  have hstable : (prefixWord ++ tailWord_5894158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894158).length < 2 ^ (prefixWord ++ tailWord_5894158).sum := by decide
  have hdescent : baseEnd_5894158 < baseStart_5894158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894165 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_5894165 : Nat := 118140960795 + 5894165 * 2 ^ 59
def prefixEnd_5894165 : Nat := 4983230072969 + 3 ^ 40 * 5894165 * 2
def baseEnd_5894165 : Nat := 3026539701908036786030735

theorem tailTrace_5894165 : CollatzResearch.WordTrace tailWord_5894165 prefixEnd_5894165 3026539701908036786030735 := by
  unfold tailWord_5894165
  simp only [CollatzResearch.WordTrace]
  refine ⟨214977858691454323084147949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143318572460969548722765299 214977858691454323084147949)
  ·
    refine ⟨80616697009295371156555481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214977858691454323084147949 80616697009295371156555481)
    ·
      refine ⟨60462522756971528367416611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80616697009295371156555481 60462522756971528367416611)
      ·
        refine ⟨90693784135457292551124917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60462522756971528367416611 90693784135457292551124917)
        ·
          refine ⟨8502542262699121176667961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90693784135457292551124917 8502542262699121176667961)
          ·
            refine ⟨6376906697024340882500971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8502542262699121176667961 6376906697024340882500971)
            ·
              refine ⟨9565360045536511323751457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376906697024340882500971 9565360045536511323751457)
              ·
                refine ⟨7174020034152383492813593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9565360045536511323751457 7174020034152383492813593)
                ·
                  refine ⟨5380515025614287619610195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7174020034152383492813593 5380515025614287619610195)
                  ·
                    refine ⟨8070772538421431429415293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5380515025614287619610195 8070772538421431429415293)
                    ·
                      refine ⟨3026539701908036786030735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8070772538421431429415293 3026539701908036786030735)
                      ·
                        rfl

theorem cell23_5894165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_5894165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894165 prefixEnd_5894165 := by exact prefixLift 5894165
  have htrace : WordTrace (prefixWord ++ tailWord_5894165) baseStart_5894165 baseEnd_5894165 := by
    simpa [prefixWord, tailWord_5894165, baseEnd_5894165] using wordTrace_append hprefix tailTrace_5894165
  have hstable : (prefixWord ++ tailWord_5894165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894165).length < 2 ^ (prefixWord ++ tailWord_5894165).sum := by decide
  have hdescent : baseEnd_5894165 < baseStart_5894165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894194 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_5894194 : Nat := 118140960795 + 5894194 * 2 ^ 59
def prefixEnd_5894194 : Nat := 4983230072969 + 3 ^ 40 * 5894194 * 2
def baseEnd_5894194 : Nat := 336283843649668574729789

theorem tailTrace_5894194 : CollatzResearch.WordTrace tailWord_5894194 prefixEnd_5894194 336283843649668574729789 := by
  unfold tailWord_5894194
  simp only [CollatzResearch.WordTrace]
  refine ⟨53744729102087315259238409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143319277605566174024635757 53744729102087315259238409)
  ·
    refine ⟨40308546826565486444428807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53744729102087315259238409 40308546826565486444428807)
    ·
      refine ⟨60462820239848229666643211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40308546826565486444428807 60462820239848229666643211)
      ·
        refine ⟨90694230359772344499964817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60462820239848229666643211 90694230359772344499964817)
        ·
          refine ⟨68020672769829258374973613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90694230359772344499964817 68020672769829258374973613)
          ·
            refine ⟨25507752288685971890615105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68020672769829258374973613 25507752288685971890615105)
            ·
              refine ⟨19130814216514478917961329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25507752288685971890615105 19130814216514478917961329)
              ·
                refine ⟨14348110662385859188470997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19130814216514478917961329 14348110662385859188470997)
                ·
                  refine ⟨336283843649668574729789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14348110662385859188470997 336283843649668574729789)
                  ·
                    rfl

theorem cell23_5894194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_5894194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894194 prefixEnd_5894194 := by exact prefixLift 5894194
  have htrace : WordTrace (prefixWord ++ tailWord_5894194) baseStart_5894194 baseEnd_5894194 := by
    simpa [prefixWord, tailWord_5894194, baseEnd_5894194] using wordTrace_append hprefix tailTrace_5894194
  have hstable : (prefixWord ++ tailWord_5894194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894194).length < 2 ^ (prefixWord ++ tailWord_5894194).sum := by decide
  have hdescent : baseEnd_5894194 < baseStart_5894194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894234 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_5894234 : Nat := 118140960795 + 5894234 * 2 ^ 59
def prefixEnd_5894234 : Nat := 4983230072969 + 3 ^ 40 * 5894234 * 2
def baseEnd_5894234 : Nat := 3026575132073197016067917

theorem tailTrace_5894234 : CollatzResearch.WordTrace tailWord_5894234 prefixEnd_5894234 3026575132073197016067917 := by
  unfold tailWord_5894234
  simp only [CollatzResearch.WordTrace]
  refine ⟨53745093832051086967102439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143320250218802898578939837 53745093832051086967102439)
  ·
    refine ⟨80617640748076630450653659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53745093832051086967102439 80617640748076630450653659)
    ·
      refine ⟨120926461122114945675980489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80617640748076630450653659 120926461122114945675980489)
      ·
        refine ⟨90694845841586209256985367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120926461122114945675980489 90694845841586209256985367)
        ·
          refine ⟨136042268762379313885478051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90694845841586209256985367 136042268762379313885478051)
          ·
            refine ⟨204063403143568970828217077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136042268762379313885478051 204063403143568970828217077)
            ·
              refine ⟨19130944044709591015145351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204063403143568970828217077 19130944044709591015145351)
              ·
                refine ⟨28696416067064386522718027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19130944044709591015145351 28696416067064386522718027)
                ·
                  refine ⟨43044624100596579784077041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28696416067064386522718027 43044624100596579784077041)
                  ·
                    refine ⟨32283468075447434838057781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43044624100596579784077041 32283468075447434838057781)
                    ·
                      refine ⟨3026575132073197016067917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32283468075447434838057781 3026575132073197016067917)
                      ·
                        rfl

theorem cell23_5894234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_5894234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894234 prefixEnd_5894234 := by exact prefixLift 5894234
  have htrace : WordTrace (prefixWord ++ tailWord_5894234) baseStart_5894234 baseEnd_5894234 := by
    simpa [prefixWord, tailWord_5894234, baseEnd_5894234] using wordTrace_append hprefix tailTrace_5894234
  have hstable : (prefixWord ++ tailWord_5894234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894234).length < 2 ^ (prefixWord ++ tailWord_5894234).sum := by decide
  have hdescent : baseEnd_5894234 < baseStart_5894234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894244 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_5894244 : Nat := 118140960795 + 5894244 * 2 ^ 59
def prefixEnd_5894244 : Nat := 4983230072969 + 3 ^ 40 * 5894244 * 2
def baseEnd_5894244 : Nat := 3026580266879741976942871

theorem tailTrace_5894244 : CollatzResearch.WordTrace tailWord_5894244 prefixEnd_5894244 3026580266879741976942871 := by
  unfold tailWord_5894244
  simp only [CollatzResearch.WordTrace]
  refine ⟨107490370029084059788136893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143320493372112079717515857 107490370029084059788136893)
  ·
    refine ⟨40308888760906522420551335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107490370029084059788136893 40308888760906522420551335)
    ·
      refine ⟨60463333141359783630827003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40308888760906522420551335 60463333141359783630827003)
      ·
        refine ⟨90694999712039675446240505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60463333141359783630827003 90694999712039675446240505)
        ·
          refine ⟨68021249784029756584680379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90694999712039675446240505 68021249784029756584680379)
          ·
            refine ⟨102031874676044634877020569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68021249784029756584680379 102031874676044634877020569)
            ·
              refine ⟨76523906007033476157765427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102031874676044634877020569 76523906007033476157765427)
              ·
                refine ⟨114785859010550214236648141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76523906007033476157765427 114785859010550214236648141)
                ·
                  refine ⟨43044697128956330338743053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114785859010550214236648141 43044697128956330338743053)
                  ·
                    refine ⟨16141761423358623877028645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43044697128956330338743053 16141761423358623877028645)
                    ·
                      refine ⟨3026580266879741976942871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16141761423358623877028645 3026580266879741976942871)
                      ·
                        rfl

theorem cell23_5894244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_5894244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894244 prefixEnd_5894244 := by exact prefixLift 5894244
  have htrace : WordTrace (prefixWord ++ tailWord_5894244) baseStart_5894244 baseEnd_5894244 := by
    simpa [prefixWord, tailWord_5894244, baseEnd_5894244] using wordTrace_append hprefix tailTrace_5894244
  have hstable : (prefixWord ++ tailWord_5894244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894244).length < 2 ^ (prefixWord ++ tailWord_5894244).sum := by decide
  have hdescent : baseEnd_5894244 < baseStart_5894244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894281 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_5894281 : Nat := 118140960795 + 5894281 * 2 ^ 59
def prefixEnd_5894281 : Nat := 4983230072969 + 3 ^ 40 * 5894281 * 2
def baseEnd_5894281 : Nat := 3026599265663958332180201

theorem tailTrace_5894281 : CollatzResearch.WordTrace tailWord_5894281 prefixEnd_5894281 3026599265663958332180201 := by
  unfold tailWord_5894281
  simp only [CollatzResearch.WordTrace]
  refine ⟨214982089559034074895370697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143321393039356049930247131 214982089559034074895370697)
  ·
    refine ⟨161236567169275556171528023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214982089559034074895370697 161236567169275556171528023)
    ·
      refine ⟨241854850753913334257292035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161236567169275556171528023 241854850753913334257292035)
      ·
        refine ⟨362782276130870001385938053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241854850753913334257292035 362782276130870001385938053)
        ·
          refine ⟨68021676774538125259863385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362782276130870001385938053 68021676774538125259863385)
          ·
            refine ⟨51016257580903593944897539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68021676774538125259863385 51016257580903593944897539)
            ·
              refine ⟨76524386371355390917346309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51016257580903593944897539 76524386371355390917346309)
              ·
                refine ⟨14348322444629135797002433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76524386371355390917346309 14348322444629135797002433)
                ·
                  refine ⟨10761241833471851847751825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14348322444629135797002433 10761241833471851847751825)
                  ·
                    refine ⟨8070931375103888885813869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10761241833471851847751825 8070931375103888885813869)
                    ·
                      refine ⟨3026599265663958332180201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8070931375103888885813869 3026599265663958332180201)
                      ·
                        rfl

theorem cell23_5894281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_5894281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894281 prefixEnd_5894281 := by exact prefixLift 5894281
  have htrace : WordTrace (prefixWord ++ tailWord_5894281) baseStart_5894281 baseEnd_5894281 := by
    simpa [prefixWord, tailWord_5894281, baseEnd_5894281] using wordTrace_append hprefix tailTrace_5894281
  have hstable : (prefixWord ++ tailWord_5894281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894281).length < 2 ^ (prefixWord ++ tailWord_5894281).sum := by decide
  have hdescent : baseEnd_5894281 < baseStart_5894281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894288 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 1, 4]
def baseStart_5894288 : Nat := 118140960795 + 5894288 * 2 ^ 59
def prefixEnd_5894288 : Nat := 4983230072969 + 3 ^ 40 * 5894288 * 2
def baseEnd_5894288 : Nat := 1008867620009513268264223

theorem tailTrace_5894288 : CollatzResearch.WordTrace tailWord_5894288 prefixEnd_5894288 1008867620009513268264223 := by
  unfold tailWord_5894288
  simp only [CollatzResearch.WordTrace]
  refine ⟨107491172435004357545437759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143321563246672476727250345 107491172435004357545437759)
  ·
    refine ⟨161236758652506536318156639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107491172435004357545437759 161236758652506536318156639)
    ·
      refine ⟨241855137978759804477234959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161236758652506536318156639 241855137978759804477234959)
      ·
        refine ⟨362782706968139706715852439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241855137978759804477234959 362782706968139706715852439)
        ·
          refine ⟨544174060452209560073778659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362782706968139706715852439 544174060452209560073778659)
          ·
            refine ⟨816261090678314340110667989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544174060452209560073778659 816261090678314340110667989)
            ·
              refine ⟨19131119312772992346343781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 816261090678314340110667989 19131119312772992346343781)
              ·
                refine ⟨3587084871144936064939459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19131119312772992346343781 3587084871144936064939459)
                ·
                  refine ⟨5380627306717404097409189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587084871144936064939459 5380627306717404097409189)
                  ·
                    refine ⟨1008867620009513268264223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5380627306717404097409189 1008867620009513268264223)
                    ·
                      rfl

theorem cell23_5894288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 4].length) (baseStart_5894288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894288 prefixEnd_5894288 := by exact prefixLift 5894288
  have htrace : WordTrace (prefixWord ++ tailWord_5894288) baseStart_5894288 baseEnd_5894288 := by
    simpa [prefixWord, tailWord_5894288, baseEnd_5894288] using wordTrace_append hprefix tailTrace_5894288
  have hstable : (prefixWord ++ tailWord_5894288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894288).length < 2 ^ (prefixWord ++ tailWord_5894288).sum := by decide
  have hdescent : baseEnd_5894288 < baseStart_5894288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894301 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 6]
def baseStart_5894301 : Nat := 118140960795 + 5894301 * 2 ^ 59
def prefixEnd_5894301 : Nat := 4983230072969 + 3 ^ 40 * 5894301 * 2
def baseEnd_5894301 : Nat := 336289948364116472658901

theorem tailTrace_5894301 : CollatzResearch.WordTrace tailWord_5894301 prefixEnd_5894301 336289948364116472658901 := by
  unfold tailWord_5894301
  simp only [CollatzResearch.WordTrace]
  refine ⟨214982819018961618311098757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143321879345974412207399171 214982819018961618311098757)
  ·
    refine ⟨40309278566055303433331017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214982819018961618311098757 40309278566055303433331017)
    ·
      refine ⟨30231958924541477574998263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40309278566055303433331017 30231958924541477574998263)
      ·
        refine ⟨45347938386812216362497395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30231958924541477574998263 45347938386812216362497395)
        ·
          refine ⟨68021907580218324543746093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45347938386812216362497395 68021907580218324543746093)
          ·
            refine ⟨25508215342581871703904785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68021907580218324543746093 25508215342581871703904785)
            ·
              refine ⟨19131161506936403777928589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25508215342581871703904785 19131161506936403777928589)
              ·
                refine ⟨7174185565101151416723221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19131161506936403777928589 7174185565101151416723221)
                ·
                  refine ⟨336289948364116472658901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7174185565101151416723221 336289948364116472658901)
                  ·
                    rfl

theorem cell23_5894301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_5894301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894301 prefixEnd_5894301 := by exact prefixLift 5894301
  have htrace : WordTrace (prefixWord ++ tailWord_5894301) baseStart_5894301 baseEnd_5894301 := by
    simpa [prefixWord, tailWord_5894301, baseEnd_5894301] using wordTrace_append hprefix tailTrace_5894301
  have hstable : (prefixWord ++ tailWord_5894301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894301).length < 2 ^ (prefixWord ++ tailWord_5894301).sum := by decide
  have hdescent : baseEnd_5894301 < baseStart_5894301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894331 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 1, 5]
def baseStart_5894331 : Nat := 118140960795 + 5894331 * 2 ^ 59
def prefixEnd_5894331 : Nat := 4983230072969 + 3 ^ 40 * 5894331 * 2
def baseEnd_5894331 : Nat := 1008874979898894378851657

theorem tailTrace_5894331 : CollatzResearch.WordTrace tailWord_5894331 prefixEnd_5894331 1008874979898894378851657 := by
  unfold tailWord_5894331
  simp only [CollatzResearch.WordTrace]
  refine ⟨214983913208852933434690847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143322608805901955623127231 214983913208852933434690847)
  ·
    refine ⟨322475869813279400152036271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214983913208852933434690847 322475869813279400152036271)
    ·
      refine ⟨483713804719919100228054407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322475869813279400152036271 483713804719919100228054407)
      ·
        refine ⟨725570707079878650342081611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483713804719919100228054407 725570707079878650342081611)
        ·
          refine ⟨1088356060619817975513122417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725570707079878650342081611 1088356060619817975513122417)
          ·
            refine ⟨816267045464863481634841813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088356060619817975513122417 816267045464863481634841813)
            ·
              refine ⟨19131258878082737850816605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 816267045464863481634841813 19131258878082737850816605)
              ·
                refine ⟨7174222079281026694056227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19131258878082737850816605 7174222079281026694056227)
                ·
                  refine ⟨10761333118921540041084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174222079281026694056227 10761333118921540041084341)
                  ·
                    refine ⟨1008874979898894378851657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10761333118921540041084341 1008874979898894378851657)
                    ·
                      rfl

theorem cell23_5894331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 5].length) (baseStart_5894331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894331 prefixEnd_5894331 := by exact prefixLift 5894331
  have htrace : WordTrace (prefixWord ++ tailWord_5894331) baseStart_5894331 baseEnd_5894331 := by
    simpa [prefixWord, tailWord_5894331, baseEnd_5894331] using wordTrace_append hprefix tailTrace_5894331
  have hstable : (prefixWord ++ tailWord_5894331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894331).length < 2 ^ (prefixWord ++ tailWord_5894331).sum := by decide
  have hdescent : baseEnd_5894331 < baseStart_5894331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894361 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 1, 6]
def baseStart_5894361 : Nat := 118140960795 + 5894361 * 2 ^ 59
def prefixEnd_5894361 : Nat := 4983230072969 + 3 ^ 40 * 5894361 * 2
def baseEnd_5894361 : Nat := 1008880114705439339726611

theorem tailTrace_5894361 : CollatzResearch.WordTrace tailWord_5894361 prefixEnd_5894361 1008880114705439339726611 := by
  unfold tailWord_5894361
  simp only [CollatzResearch.WordTrace]
  refine ⟨214985007398744248558282937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143323338265829499038855291 214985007398744248558282937)
  ·
    refine ⟨161238755549058186418712203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214985007398744248558282937 161238755549058186418712203)
    ·
      refine ⟨241858133323587279628068305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161238755549058186418712203 241858133323587279628068305)
      ·
        refine ⟨181393599992690459721051229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241858133323587279628068305 181393599992690459721051229)
        ·
          refine ⟨68022599997258922395394211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181393599992690459721051229 68022599997258922395394211)
          ·
            refine ⟨102033899995888383593091317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68022599997258922395394211 102033899995888383593091317)
            ·
              refine ⟨9565678124614535961852311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102033899995888383593091317 9565678124614535961852311)
              ·
                refine ⟨14348517186921803942778467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9565678124614535961852311 14348517186921803942778467)
                ·
                  refine ⟨21522775780382705914167701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14348517186921803942778467 21522775780382705914167701)
                  ·
                    refine ⟨1008880114705439339726611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21522775780382705914167701 1008880114705439339726611)
                    ·
                      rfl

theorem cell23_5894361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_5894361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894361 prefixEnd_5894361 := by exact prefixLift 5894361
  have htrace : WordTrace (prefixWord ++ tailWord_5894361) baseStart_5894361 baseEnd_5894361 := by
    simpa [prefixWord, tailWord_5894361, baseEnd_5894361] using wordTrace_append hprefix tailTrace_5894361
  have hstable : (prefixWord ++ tailWord_5894361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894361).length < 2 ^ (prefixWord ++ tailWord_5894361).sum := by decide
  have hdescent : baseEnd_5894361 < baseStart_5894361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894365 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5894365 : Nat := 118140960795 + 5894365 * 2 ^ 59
def prefixEnd_5894365 : Nat := 4983230072969 + 3 ^ 40 * 5894365 * 2
def baseEnd_5894365 : Nat := 1008880799346312001176605

theorem tailTrace_5894365 : CollatzResearch.WordTrace tailWord_5894365 prefixEnd_5894365 1008880799346312001176605 := by
  unfold tailWord_5894365
  simp only [CollatzResearch.WordTrace]
  refine ⟨214985153290729757241428549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143323435527153171494285699 214985153290729757241428549)
  ·
    refine ⟨40309716242011829482767853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214985153290729757241428549 40309716242011829482767853)
    ·
      refine ⟨15116143590754436056037945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40309716242011829482767853 15116143590754436056037945)
      ·
        refine ⟨11337107693065827042028459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15116143590754436056037945 11337107693065827042028459)
        ·
          refine ⟨17005661539598740563042689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11337107693065827042028459 17005661539598740563042689)
          ·
            refine ⟨12754246154699055422282017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17005661539598740563042689 12754246154699055422282017)
            ·
              refine ⟨9565684616024291566711513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12754246154699055422282017 9565684616024291566711513)
              ·
                refine ⟨7174263462018218675033635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9565684616024291566711513 7174263462018218675033635)
                ·
                  refine ⟨10761395193027328012550453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174263462018218675033635 10761395193027328012550453)
                  ·
                    refine ⟨1008880799346312001176605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10761395193027328012550453 1008880799346312001176605)
                    ·
                      rfl

theorem cell23_5894365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5894365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894365 prefixEnd_5894365 := by exact prefixLift 5894365
  have htrace : WordTrace (prefixWord ++ tailWord_5894365) baseStart_5894365 baseEnd_5894365 := by
    simpa [prefixWord, tailWord_5894365, baseEnd_5894365] using wordTrace_append hprefix tailTrace_5894365
  have hstable : (prefixWord ++ tailWord_5894365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894365).length < 2 ^ (prefixWord ++ tailWord_5894365).sum := by decide
  have hdescent : baseEnd_5894365 < baseStart_5894365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894368 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4]
def baseStart_5894368 : Nat := 118140960795 + 5894368 * 2 ^ 59
def prefixEnd_5894368 : Nat := 4983230072969 + 3 ^ 40 * 5894368 * 2
def baseEnd_5894368 : Nat := 3026643938480899491792301

theorem tailTrace_5894368 : CollatzResearch.WordTrace tailWord_5894368 prefixEnd_5894368 3026643938480899491792301 := by
  unfold tailWord_5894368
  simp only [CollatzResearch.WordTrace]
  refine ⟨107492631354859444376893879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143323508473145925835858505 107492631354859444376893879)
  ·
    refine ⟨161238947032289166565340819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107492631354859444376893879 161238947032289166565340819)
    ·
      refine ⟨241858420548433749848011229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161238947032289166565340819 241858420548433749848011229)
      ·
        refine ⟨90696907705662656193004211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241858420548433749848011229 90696907705662656193004211)
        ·
          refine ⟨136045361558493984289506317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90696907705662656193004211 136045361558493984289506317)
          ·
            refine ⟨51017010584435244108564869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136045361558493984289506317 51017010584435244108564869)
            ·
              refine ⟨9565689484581608270355913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51017010584435244108564869 9565689484581608270355913)
              ·
                refine ⟨7174267113436206202766935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9565689484581608270355913 7174267113436206202766935)
                ·
                  refine ⟨10761400670154309304150403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174267113436206202766935 10761400670154309304150403)
                  ·
                    refine ⟨16142101005231463956225605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10761400670154309304150403 16142101005231463956225605)
                    ·
                      refine ⟨3026643938480899491792301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16142101005231463956225605 3026643938480899491792301)
                      ·
                        rfl

theorem cell23_5894368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_5894368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894368 prefixEnd_5894368 := by exact prefixLift 5894368
  have htrace : WordTrace (prefixWord ++ tailWord_5894368) baseStart_5894368 baseEnd_5894368 := by
    simpa [prefixWord, tailWord_5894368, baseEnd_5894368] using wordTrace_append hprefix tailTrace_5894368
  have hstable : (prefixWord ++ tailWord_5894368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894368).length < 2 ^ (prefixWord ++ tailWord_5894368).sum := by decide
  have hdescent : baseEnd_5894368 < baseStart_5894368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894439 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5894439 : Nat := 118140960795 + 5894439 * 2 ^ 59
def prefixEnd_5894439 : Nat := 4983230072969 + 3 ^ 40 * 5894439 * 2
def baseEnd_5894439 : Nat := 3026680395607368714004475

theorem tailTrace_5894439 : CollatzResearch.WordTrace tailWord_5894439 prefixEnd_5894439 3026680395607368714004475 := by
  unfold tailWord_5894439
  simp only [CollatzResearch.WordTrace]
  refine ⟨214987852292461667879622371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143325234861641111919748247 214987852292461667879622371)
  ·
    refine ⟨322481778438692501819433557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214987852292461667879622371 322481778438692501819433557)
    ·
      refine ⟨3779083341078427755696487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 322481778438692501819433557 3779083341078427755696487)
      ·
        refine ⟨5668625011617641633544731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779083341078427755696487 5668625011617641633544731)
        ·
          refine ⟨8502937517426462450317097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668625011617641633544731 8502937517426462450317097)
          ·
            refine ⟨6377203138069846837737823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8502937517426462450317097 6377203138069846837737823)
            ·
              refine ⟨9565804707104770256606735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377203138069846837737823 9565804707104770256606735)
              ·
                refine ⟨14348707060657155384910103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9565804707104770256606735 14348707060657155384910103)
                ·
                  refine ⟨21523060590985733077365155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14348707060657155384910103 21523060590985733077365155)
                  ·
                    refine ⟨32284590886478599616047733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21523060590985733077365155 32284590886478599616047733)
                    ·
                      refine ⟨3026680395607368714004475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32284590886478599616047733 3026680395607368714004475)
                      ·
                        rfl

theorem cell23_5894439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5894439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894439 prefixEnd_5894439 := by exact prefixLift 5894439
  have htrace : WordTrace (prefixWord ++ tailWord_5894439) baseStart_5894439 baseEnd_5894439 := by
    simpa [prefixWord, tailWord_5894439, baseEnd_5894439] using wordTrace_append hprefix tailTrace_5894439
  have hstable : (prefixWord ++ tailWord_5894439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894439).length < 2 ^ (prefixWord ++ tailWord_5894439).sum := by decide
  have hdescent : baseEnd_5894439 < baseStart_5894439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894451 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 2, 6]
def baseStart_5894451 : Nat := 118140960795 + 5894451 * 2 ^ 59
def prefixEnd_5894451 : Nat := 4983230072969 + 3 ^ 40 * 5894451 * 2
def baseEnd_5894451 : Nat := 1008895519125074222351473

theorem tailTrace_5894451 : CollatzResearch.WordTrace tailWord_5894451 prefixEnd_5894451 1008895519125074222351473 := by
  unfold tailWord_5894451
  simp only [CollatzResearch.WordTrace]
  refine ⟨214988289968418193929059207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143325526645612129286039471 214988289968418193929059207)
  ·
    refine ⟨322482434952627290893588811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214988289968418193929059207 322482434952627290893588811)
    ·
      refine ⟨483723652428940936340383217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322482434952627290893588811 483723652428940936340383217)
      ·
        refine ⟨362792739321705702255287413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483723652428940936340383217 362792739321705702255287413)
        ·
          refine ⟨34011819311409909586433195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 362792739321705702255287413 34011819311409909586433195)
          ·
            refine ⟨51017728967114864379649793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34011819311409909586433195 51017728967114864379649793)
            ·
              refine ⟨38263296725336148284737345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51017728967114864379649793 38263296725336148284737345)
              ·
                refine ⟨28697472544002111213553009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38263296725336148284737345 28697472544002111213553009)
                ·
                  refine ⟨21523104408001583410164757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28697472544002111213553009 21523104408001583410164757)
                  ·
                    refine ⟨1008895519125074222351473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21523104408001583410164757 1008895519125074222351473)
                    ·
                      rfl

theorem cell23_5894451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 6].length) (baseStart_5894451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894451 prefixEnd_5894451 := by exact prefixLift 5894451
  have htrace : WordTrace (prefixWord ++ tailWord_5894451) baseStart_5894451 baseEnd_5894451 := by
    simpa [prefixWord, tailWord_5894451, baseEnd_5894451] using wordTrace_append hprefix tailTrace_5894451
  have hstable : (prefixWord ++ tailWord_5894451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894451).length < 2 ^ (prefixWord ++ tailWord_5894451).sum := by decide
  have hdescent : baseEnd_5894451 < baseStart_5894451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894452 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_5894452 : Nat := 118140960795 + 5894452 * 2 ^ 59
def prefixEnd_5894452 : Nat := 4983230072969 + 3 ^ 40 * 5894452 * 2
def baseEnd_5894452 : Nat := 3026687070855877163141915

theorem tailTrace_5894452 : CollatzResearch.WordTrace tailWord_5894452 prefixEnd_5894452 3026687070855877163141915 := by
  unfold tailWord_5894452
  simp only [CollatzResearch.WordTrace]
  refine ⟨107494163220707285549922805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143325550960943047399897073 107494163220707285549922805)
  ·
    refine ⟨10077577801941308020305263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107494163220707285549922805 10077577801941308020305263)
    ·
      refine ⟨15116366702911962030457895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10077577801941308020305263 15116366702911962030457895)
      ·
        refine ⟨22674550054367943045686843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15116366702911962030457895 22674550054367943045686843)
        ·
          refine ⟨34011825081551914568530265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22674550054367943045686843 34011825081551914568530265)
          ·
            refine ⟨25508868811163935926397699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34011825081551914568530265 25508868811163935926397699)
            ·
              refine ⟨38263303216745903889596549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25508868811163935926397699 38263303216745903889596549)
              ·
                refine ⟨7174369353139856979299353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38263303216745903889596549 7174369353139856979299353)
                ·
                  refine ⟨5380777014854892734474515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7174369353139856979299353 5380777014854892734474515)
                  ·
                    refine ⟨8071165522282339101711773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5380777014854892734474515 8071165522282339101711773)
                    ·
                      refine ⟨3026687070855877163141915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8071165522282339101711773 3026687070855877163141915)
                      ·
                        rfl

theorem cell23_5894452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_5894452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894452 prefixEnd_5894452 := by exact prefixLift 5894452
  have htrace : WordTrace (prefixWord ++ tailWord_5894452) baseStart_5894452 baseEnd_5894452 := by
    simpa [prefixWord, tailWord_5894452, baseEnd_5894452] using wordTrace_append hprefix tailTrace_5894452
  have hstable : (prefixWord ++ tailWord_5894452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894452).length < 2 ^ (prefixWord ++ tailWord_5894452).sum := by decide
  have hdescent : baseEnd_5894452 < baseStart_5894452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894481 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 9]
def baseStart_5894481 : Nat := 118140960795 + 5894481 * 2 ^ 59
def prefixEnd_5894481 : Nat := 4983230072969 + 3 ^ 40 * 5894481 * 2
def baseEnd_5894481 : Nat := 336300217977206394408809

theorem tailTrace_5894481 : CollatzResearch.WordTrace tailWord_5894481 prefixEnd_5894481 336300217977206394408809 := by
  unfold tailWord_5894481
  simp only [CollatzResearch.WordTrace]
  refine ⟨214989384158309509052651297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143326256105539672701767531 214989384158309509052651297)
  ·
    refine ⟨161242038118732131789488473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214989384158309509052651297 161242038118732131789488473)
    ·
      refine ⟨120931528589049098842116355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161242038118732131789488473 120931528589049098842116355)
      ·
        refine ⟨181397292883573648263174533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120931528589049098842116355 181397292883573648263174533)
        ·
          refine ⟨34011992415670059049345225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181397292883573648263174533 34011992415670059049345225)
          ·
            refine ⟨25508994311752544287008919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34011992415670059049345225 25508994311752544287008919)
            ·
              refine ⟨38263491467628816430513379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25508994311752544287008919 38263491467628816430513379)
              ·
                refine ⟨57395237201443224645770069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38263491467628816430513379 57395237201443224645770069)
                ·
                  refine ⟨336300217977206394408809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57395237201443224645770069 336300217977206394408809)
                  ·
                    rfl

theorem cell23_5894481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_5894481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894481 prefixEnd_5894481 := by exact prefixLift 5894481
  have htrace : WordTrace (prefixWord ++ tailWord_5894481) baseStart_5894481 baseEnd_5894481 := by
    simpa [prefixWord, tailWord_5894481, baseEnd_5894481] using wordTrace_append hprefix tailTrace_5894481
  have hstable : (prefixWord ++ tailWord_5894481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894481).length < 2 ^ (prefixWord ++ tailWord_5894481).sum := by decide
  have hdescent : baseEnd_5894481 < baseStart_5894481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894496 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 1, 3, 2]
def baseStart_5894496 : Nat := 118140960795 + 5894496 * 2 ^ 59
def prefixEnd_5894496 : Nat := 4983230072969 + 3 ^ 40 * 5894496 * 2
def baseEnd_5894496 : Nat := 3026709664004674990991713

theorem tailTrace_5894496 : CollatzResearch.WordTrace tailWord_5894496 prefixEnd_5894496 3026709664004674990991713 := by
  unfold tailWord_5894496
  simp only [CollatzResearch.WordTrace]
  refine ⟨107494965626627583307223671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143326620835503444409631561 107494965626627583307223671)
  ·
    refine ⟨161242448439941374960835507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107494965626627583307223671 161242448439941374960835507)
    ·
      refine ⟨241863672659912062441253261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161242448439941374960835507 241863672659912062441253261)
      ·
        refine ⟨90698877247467023415469973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241863672659912062441253261 90698877247467023415469973)
        ·
          refine ⟨4251509870975016722600155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90698877247467023415469973 4251509870975016722600155)
          ·
            refine ⟨6377264806462525083900233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251509870975016722600155 6377264806462525083900233)
            ·
              refine ⟨4782948604846893812925175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6377264806462525083900233 4782948604846893812925175)
              ·
                refine ⟨7174422907270340719387763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782948604846893812925175 7174422907270340719387763)
                ·
                  refine ⟨10761634360905511079081645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174422907270340719387763 10761634360905511079081645)
                  ·
                    refine ⟨4035612885339566654655617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10761634360905511079081645 4035612885339566654655617)
                    ·
                      refine ⟨3026709664004674990991713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035612885339566654655617 3026709664004674990991713)
                      ·
                        rfl

theorem cell23_5894496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_5894496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894496 prefixEnd_5894496 := by exact prefixLift 5894496
  have htrace : WordTrace (prefixWord ++ tailWord_5894496) baseStart_5894496 baseEnd_5894496 := by
    simpa [prefixWord, tailWord_5894496, baseEnd_5894496] using wordTrace_append hprefix tailTrace_5894496
  have hstable : (prefixWord ++ tailWord_5894496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894496).length < 2 ^ (prefixWord ++ tailWord_5894496).sum := by decide
  have hdescent : baseEnd_5894496 < baseStart_5894496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894521 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5894521 : Nat := 118140960795 + 5894521 * 2 ^ 59
def prefixEnd_5894521 : Nat := 4983230072969 + 3 ^ 40 * 5894521 * 2
def baseEnd_5894521 : Nat := 3026722501021037393179097

theorem tailTrace_5894521 : CollatzResearch.WordTrace tailWord_5894521 prefixEnd_5894521 3026722501021037393179097 := by
  unfold tailWord_5894521
  simp only [CollatzResearch.WordTrace]
  refine ⟨214990843078164595884107417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143327228718776397256071611 214990843078164595884107417)
  ·
    refine ⟨161243132308623446913080563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214990843078164595884107417 161243132308623446913080563)
    ·
      refine ⟨241864698462935170369620845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161243132308623446913080563 241864698462935170369620845)
      ·
        refine ⟨90699261923600688888607817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241864698462935170369620845 90699261923600688888607817)
        ·
          refine ⟨68024446442700516666455863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90699261923600688888607817 68024446442700516666455863)
          ·
            refine ⟨102036669664050774999683795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68024446442700516666455863 102036669664050774999683795)
            ·
              refine ⟨153055004496076162499525693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102036669664050774999683795 153055004496076162499525693)
              ·
                refine ⟨57395626686028560937322135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153055004496076162499525693 57395626686028560937322135)
                ·
                  refine ⟨86093440029042841405983203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57395626686028560937322135 86093440029042841405983203)
                  ·
                    refine ⟨129140160043564262108974805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86093440029042841405983203 129140160043564262108974805)
                    ·
                      refine ⟨3026722501021037393179097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129140160043564262108974805 3026722501021037393179097)
                      ·
                        rfl

theorem cell23_5894521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5894521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894521 prefixEnd_5894521 := by exact prefixLift 5894521
  have htrace : WordTrace (prefixWord ++ tailWord_5894521) baseStart_5894521 baseEnd_5894521 := by
    simpa [prefixWord, tailWord_5894521, baseEnd_5894521] using wordTrace_append hprefix tailTrace_5894521
  have hstable : (prefixWord ++ tailWord_5894521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894521).length < 2 ^ (prefixWord ++ tailWord_5894521).sum := by decide
  have hdescent : baseEnd_5894521 < baseStart_5894521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894655 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 4]
def baseStart_5894655 : Nat := 118140960795 + 5894655 * 2 ^ 59
def prefixEnd_5894655 : Nat := 4983230072969 + 3 ^ 40 * 5894655 * 2
def baseEnd_5894655 : Nat := 3026791307428739868903481

theorem tailTrace_5894655 : CollatzResearch.WordTrace tailWord_5894655 prefixEnd_5894655 3026791307428739868903481 := by
  unfold tailWord_5894655
  simp only [CollatzResearch.WordTrace]
  refine ⟨214995730459679136769485419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143330486973119424512990279 214995730459679136769485419)
  ·
    refine ⟨322493595689518705154228129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214995730459679136769485419 322493595689518705154228129)
    ·
      refine ⟨241870196767139028865671097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322493595689518705154228129 241870196767139028865671097)
      ·
        refine ⟨181402647575354271649253323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241870196767139028865671097 181402647575354271649253323)
        ·
          refine ⟨272103971363031407473879985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181402647575354271649253323 272103971363031407473879985)
          ·
            refine ⟨204077978522273555605409989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272103971363031407473879985 204077978522273555605409989)
            ·
              refine ⟨38264620972926291676014373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204077978522273555605409989 38264620972926291676014373)
              ·
                refine ⟨7174616432423679689252695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38264620972926291676014373 7174616432423679689252695)
                ·
                  refine ⟨10761924648635519533879043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174616432423679689252695 10761924648635519533879043)
                  ·
                    refine ⟨16142886972953279300818565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10761924648635519533879043 16142886972953279300818565)
                    ·
                      refine ⟨3026791307428739868903481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16142886972953279300818565 3026791307428739868903481)
                      ·
                        rfl

theorem cell23_5894655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_5894655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894655 prefixEnd_5894655 := by exact prefixLift 5894655
  have htrace : WordTrace (prefixWord ++ tailWord_5894655) baseStart_5894655 baseEnd_5894655 := by
    simpa [prefixWord, tailWord_5894655, baseEnd_5894655] using wordTrace_append hprefix tailTrace_5894655
  have hstable : (prefixWord ++ tailWord_5894655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894655).length < 2 ^ (prefixWord ++ tailWord_5894655).sum := by decide
  have hdescent : baseEnd_5894655 < baseStart_5894655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894682 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_5894682 : Nat := 118140960795 + 5894682 * 2 ^ 59
def prefixEnd_5894682 : Nat := 4983230072969 + 3 ^ 40 * 5894682 * 2
def baseEnd_5894682 : Nat := 1008935057135470421088619

theorem tailTrace_5894682 : CollatzResearch.WordTrace tailWord_5894682 prefixEnd_5894682 1008935057135470421088619 := by
  unfold tailWord_5894682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53749178807645330095179575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143331143487054213587145533 53749178807645330095179575)
  ·
    refine ⟨80623768211467995142769363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53749178807645330095179575 80623768211467995142769363)
    ·
      refine ⟨120935652317201992714154045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80623768211467995142769363 120935652317201992714154045)
      ·
        refine ⟨45350869618950747267807767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120935652317201992714154045 45350869618950747267807767)
        ·
          refine ⟨68026304428426120901711651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45350869618950747267807767 68026304428426120901711651)
          ·
            refine ⟨102039456642639181352567477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68026304428426120901711651 102039456642639181352567477)
            ·
              refine ⟨9566199060247423251803201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102039456642639181352567477 9566199060247423251803201)
              ·
                refine ⟨7174649295185567438852401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9566199060247423251803201 7174649295185567438852401)
                ·
                  refine ⟨5380986971389175579139301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7174649295185567438852401 5380986971389175579139301)
                  ·
                    refine ⟨1008935057135470421088619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5380986971389175579139301 1008935057135470421088619)
                    ·
                      rfl

theorem cell23_5894682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_5894682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894682 prefixEnd_5894682 := by exact prefixLift 5894682
  have htrace : WordTrace (prefixWord ++ tailWord_5894682) baseStart_5894682 baseEnd_5894682 := by
    simpa [prefixWord, tailWord_5894682, baseEnd_5894682] using wordTrace_append hprefix tailTrace_5894682
  have hstable : (prefixWord ++ tailWord_5894682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894682).length < 2 ^ (prefixWord ++ tailWord_5894682).sum := by decide
  have hdescent : baseEnd_5894682 < baseStart_5894682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894689 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5894689 : Nat := 118140960795 + 5894689 * 2 ^ 59
def prefixEnd_5894689 : Nat := 4983230072969 + 3 ^ 40 * 5894689 * 2
def baseEnd_5894689 : Nat := 3026808765770992735878325

theorem tailTrace_5894689 : CollatzResearch.WordTrace tailWord_5894689 prefixEnd_5894689 3026808765770992735878325 := by
  unfold tailWord_5894689
  simp only [CollatzResearch.WordTrace]
  refine ⟨214996970541555960576223121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143331313694370640384148747 214996970541555960576223121)
  ·
    refine ⟨161247727906166970432167341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214996970541555960576223121 161247727906166970432167341)
    ·
      refine ⟨60467897964812613912062753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161247727906166970432167341 60467897964812613912062753)
      ·
        refine ⟨45350923473609460434047065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60467897964812613912062753 45350923473609460434047065)
        ·
          refine ⟨34013192605207095325535299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45350923473609460434047065 34013192605207095325535299)
          ·
            refine ⟨51019788907810642988302949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34013192605207095325535299 51019788907810642988302949)
            ·
              refine ⟨9566210420214495560306803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51019788907810642988302949 9566210420214495560306803)
              ·
                refine ⟨14349315630321743340460205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9566210420214495560306803 14349315630321743340460205)
                ·
                  refine ⟨5380993361370653752672577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14349315630321743340460205 5380993361370653752672577)
                  ·
                    refine ⟨4035745021027990314504433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5380993361370653752672577 4035745021027990314504433)
                    ·
                      refine ⟨3026808765770992735878325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035745021027990314504433 3026808765770992735878325)
                      ·
                        rfl

theorem cell23_5894689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5894689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894689 prefixEnd_5894689 := by exact prefixLift 5894689
  have htrace : WordTrace (prefixWord ++ tailWord_5894689) baseStart_5894689 baseEnd_5894689 := by
    simpa [prefixWord, tailWord_5894689, baseEnd_5894689] using wordTrace_append hprefix tailTrace_5894689
  have hstable : (prefixWord ++ tailWord_5894689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894689).length < 2 ^ (prefixWord ++ tailWord_5894689).sum := by decide
  have hdescent : baseEnd_5894689 < baseStart_5894689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894702 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_5894702 : Nat := 118140960795 + 5894702 * 2 ^ 59
def prefixEnd_5894702 : Nat := 4983230072969 + 3 ^ 40 * 5894702 * 2
def baseEnd_5894702 : Nat := 3026815441019501185015765

theorem tailTrace_5894702 : CollatzResearch.WordTrace tailWord_5894702 prefixEnd_5894702 3026815441019501185015765 := by
  unfold tailWord_5894702
  simp only [CollatzResearch.WordTrace]
  refine ⟨26874680586313607974555795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143331629793672575864297573 26874680586313607974555795)
  ·
    refine ⟨40312020879470411961833693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26874680586313607974555795 40312020879470411961833693)
    ·
      refine ⟨15117007829801404485687635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40312020879470411961833693 15117007829801404485687635)
      ·
        refine ⟨22675511744702106728531453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15117007829801404485687635 22675511744702106728531453)
        ·
          refine ⟨8503316904263290023199295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22675511744702106728531453 8503316904263290023199295)
          ·
            refine ⟨12754975356394935034798943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503316904263290023199295 12754975356394935034798943)
            ·
              refine ⟨19132463034592402552198415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12754975356394935034798943 19132463034592402552198415)
              ·
                refine ⟨28698694551888603828297623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19132463034592402552198415 28698694551888603828297623)
                ·
                  refine ⟨43048041827832905742446435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28698694551888603828297623 43048041827832905742446435)
                  ·
                    refine ⟨64572062741749358613669653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43048041827832905742446435 64572062741749358613669653)
                    ·
                      refine ⟨3026815441019501185015765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64572062741749358613669653 3026815441019501185015765)
                      ·
                        rfl

theorem cell23_5894702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_5894702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894702 prefixEnd_5894702 := by exact prefixLift 5894702
  have htrace : WordTrace (prefixWord ++ tailWord_5894702) baseStart_5894702 baseEnd_5894702 := by
    simpa [prefixWord, tailWord_5894702, baseEnd_5894702] using wordTrace_append hprefix tailTrace_5894702
  have hstable : (prefixWord ++ tailWord_5894702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894702).length < 2 ^ (prefixWord ++ tailWord_5894702).sum := by decide
  have hdescent : baseEnd_5894702 < baseStart_5894702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894726 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5894726 : Nat := 118140960795 + 5894726 * 2 ^ 59
def prefixEnd_5894726 : Nat := 4983230072969 + 3 ^ 40 * 5894726 * 2
def baseEnd_5894726 : Nat := 3026827764555209091115655

theorem tailTrace_5894726 : CollatzResearch.WordTrace tailWord_5894726 prefixEnd_5894726 3026827764555209091115655 := by
  unfold tailWord_5894726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718697501325684871728751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143332213361614610596880021 6718697501325684871728751)
  ·
    refine ⟨10078046251988527307593127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6718697501325684871728751 10078046251988527307593127)
    ·
      refine ⟨15117069377982790961389691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10078046251988527307593127 15117069377982790961389691)
      ·
        refine ⟨22675604066974186442084537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15117069377982790961389691 22675604066974186442084537)
        ·
          refine ⟨17006703050230639831563403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22675604066974186442084537 17006703050230639831563403)
          ·
            refine ⟨25510054575345959747345105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17006703050230639831563403 25510054575345959747345105)
            ·
              refine ⟨19132540931509469810508829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25510054575345959747345105 19132540931509469810508829)
              ·
                refine ⟨7174702849316051178940811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19132540931509469810508829 7174702849316051178940811)
                ·
                  refine ⟨10762054273974076768411217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174702849316051178940811 10762054273974076768411217)
                  ·
                    refine ⟨8071540705480557576308413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10762054273974076768411217 8071540705480557576308413)
                    ·
                      refine ⟨3026827764555209091115655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8071540705480557576308413 3026827764555209091115655)
                      ·
                        rfl

theorem cell23_5894726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5894726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894726 prefixEnd_5894726 := by exact prefixLift 5894726
  have htrace : WordTrace (prefixWord ++ tailWord_5894726) baseStart_5894726 baseEnd_5894726 := by
    simpa [prefixWord, tailWord_5894726, baseEnd_5894726] using wordTrace_append hprefix tailTrace_5894726
  have hstable : (prefixWord ++ tailWord_5894726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894726).length < 2 ^ (prefixWord ++ tailWord_5894726).sum := by decide
  have hdescent : baseEnd_5894726 < baseStart_5894726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894728 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_5894728 : Nat := 118140960795 + 5894728 * 2 ^ 59
def prefixEnd_5894728 : Nat := 4983230072969 + 3 ^ 40 * 5894728 * 2
def baseEnd_5894728 : Nat := 3026828791516518083290645

theorem tailTrace_5894728 : CollatzResearch.WordTrace tailWord_5894728 prefixEnd_5894728 3026828791516518083290645 := by
  unfold tailWord_5894728
  simp only [CollatzResearch.WordTrace]
  refine ⟨107499196494207335118446419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143332261992276446824595225 107499196494207335118446419)
  ·
    refine ⟨161248794741311002677669629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107499196494207335118446419 161248794741311002677669629)
    ·
      refine ⟨60468298027991626004126111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161248794741311002677669629 60468298027991626004126111)
      ·
        refine ⟨90702447041987439006189167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60468298027991626004126111 90702447041987439006189167)
        ·
          refine ⟨136053670562981158509283751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90702447041987439006189167 136053670562981158509283751)
          ·
            refine ⟨204080505844471737763925627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136053670562981158509283751 204080505844471737763925627)
            ·
              refine ⟨306120758766707606645888441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204080505844471737763925627 306120758766707606645888441)
              ·
                refine ⟨229590569075030704984416331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306120758766707606645888441 229590569075030704984416331)
                ·
                  refine ⟨344385853612546057476624497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229590569075030704984416331 344385853612546057476624497)
                  ·
                    refine ⟨258289390209409543107468373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344385853612546057476624497 258289390209409543107468373)
                    ·
                      refine ⟨3026828791516518083290645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 258289390209409543107468373 3026828791516518083290645)
                      ·
                        rfl

theorem cell23_5894728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_5894728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894728 prefixEnd_5894728 := by exact prefixLift 5894728
  have htrace : WordTrace (prefixWord ++ tailWord_5894728) baseStart_5894728 baseEnd_5894728 := by
    simpa [prefixWord, tailWord_5894728, baseEnd_5894728] using wordTrace_append hprefix tailTrace_5894728
  have hstable : (prefixWord ++ tailWord_5894728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894728).length < 2 ^ (prefixWord ++ tailWord_5894728).sum := by decide
  have hdescent : baseEnd_5894728 < baseStart_5894728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894766 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5894766 : Nat := 118140960795 + 5894766 * 2 ^ 59
def prefixEnd_5894766 : Nat := 4983230072969 + 3 ^ 40 * 5894766 * 2
def baseEnd_5894766 : Nat := 3026848303781388934615471

theorem tailTrace_5894766 : CollatzResearch.WordTrace tailWord_5894766 prefixEnd_5894766 3026848303781388934615471 := by
  unfold tailWord_5894766
  simp only [CollatzResearch.WordTrace]
  refine ⟨26874972370284625340847019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143333185974851335151184101 26874972370284625340847019)
  ·
    refine ⟨40312458555426938011270529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26874972370284625340847019 40312458555426938011270529)
    ·
      refine ⟨30234343916570203508452897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40312458555426938011270529 30234343916570203508452897)
      ·
        refine ⟨22675757937427652631339673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30234343916570203508452897 22675757937427652631339673)
        ·
          refine ⟨17006818453070739473504755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22675757937427652631339673 17006818453070739473504755)
          ·
            refine ⟨25510227679606109210257133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17006818453070739473504755 25510227679606109210257133)
            ·
              refine ⟨9566335379852290953846425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25510227679606109210257133 9566335379852290953846425)
              ·
                refine ⟨7174751534889218215384819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9566335379852290953846425 7174751534889218215384819)
                ·
                  refine ⟨10762127302333827323077229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174751534889218215384819 10762127302333827323077229)
                  ·
                    refine ⟨4035797738375185246153961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10762127302333827323077229 4035797738375185246153961)
                    ·
                      refine ⟨3026848303781388934615471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035797738375185246153961 3026848303781388934615471)
                      ·
                        rfl

theorem cell23_5894766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5894766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894766 prefixEnd_5894766 := by exact prefixLift 5894766
  have htrace : WordTrace (prefixWord ++ tailWord_5894766) baseStart_5894766 baseEnd_5894766 := by
    simpa [prefixWord, tailWord_5894766, baseEnd_5894766] using wordTrace_append hprefix tailTrace_5894766
  have hstable : (prefixWord ++ tailWord_5894766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894766).length < 2 ^ (prefixWord ++ tailWord_5894766).sum := by decide
  have hdescent : baseEnd_5894766 < baseStart_5894766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894812 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5894812 : Nat := 118140960795 + 5894812 * 2 ^ 59
def prefixEnd_5894812 : Nat := 4983230072969 + 3 ^ 40 * 5894812 * 2
def baseEnd_5894812 : Nat := 3026871923891495754640259

theorem tailTrace_5894812 : CollatzResearch.WordTrace tailWord_5894812 prefixEnd_5894812 3026871923891495754640259 := by
  unfold tailWord_5894812
  simp only [CollatzResearch.WordTrace]
  refine ⟨107500728360055176291475345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143334304480073568388633793 107500728360055176291475345)
  ·
    refine ⟨80625546270041382218606509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107500728360055176291475345 80625546270041382218606509)
    ·
      refine ⟨30234579851265518331977441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80625546270041382218606509 30234579851265518331977441)
      ·
        refine ⟨22675934888449138748983081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30234579851265518331977441 22675934888449138748983081)
        ·
          refine ⟨17006951166336854061737311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22675934888449138748983081 17006951166336854061737311)
          ·
            refine ⟨25510426749505281092605967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17006951166336854061737311 25510426749505281092605967)
            ·
              refine ⟨38265640124257921638908951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25510426749505281092605967 38265640124257921638908951)
              ·
                refine ⟨57398460186386882458363427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38265640124257921638908951 57398460186386882458363427)
                ·
                  refine ⟨86097690279580323687545141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57398460186386882458363427 86097690279580323687545141)
                  ·
                    refine ⟨8071658463710655345707357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86097690279580323687545141 8071658463710655345707357)
                    ·
                      refine ⟨3026871923891495754640259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8071658463710655345707357 3026871923891495754640259)
                      ·
                        rfl

theorem cell23_5894812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5894812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894812 prefixEnd_5894812 := by exact prefixLift 5894812
  have htrace : WordTrace (prefixWord ++ tailWord_5894812) baseStart_5894812 baseEnd_5894812 := by
    simpa [prefixWord, tailWord_5894812, baseEnd_5894812] using wordTrace_append hprefix tailTrace_5894812
  have hstable : (prefixWord ++ tailWord_5894812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894812).length < 2 ^ (prefixWord ++ tailWord_5894812).sum := by decide
  have hdescent : baseEnd_5894812 < baseStart_5894812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894865 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_5894865 : Nat := 118140960795 + 5894865 * 2 ^ 59
def prefixEnd_5894865 : Nat := 4983230072969 + 3 ^ 40 * 5894865 * 2
def baseEnd_5894865 : Nat := 3026899138366184047277515

theorem tailTrace_5894865 : CollatzResearch.WordTrace tailWord_5894865 prefixEnd_5894865 3026899138366184047277515 := by
  unfold tailWord_5894865
  simp only [CollatzResearch.WordTrace]
  refine ⟨215003389788918342634630049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143335593192612228423086699 215003389788918342634630049)
  ·
    refine ⟨161252542341688756975972537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215003389788918342634630049 161252542341688756975972537)
    ·
      refine ⟨120939406756266567731979403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161252542341688756975972537 120939406756266567731979403)
      ·
        refine ⟨181409110134399851597969105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120939406756266567731979403 181409110134399851597969105)
        ·
          refine ⟨136056832600799888698476829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181409110134399851597969105 136056832600799888698476829)
          ·
            refine ⟨51021312225299958261928811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136056832600799888698476829 51021312225299958261928811)
            ·
              refine ⟨76531968337949937392893217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51021312225299958261928811 76531968337949937392893217)
              ·
                refine ⟨57398976253462453044669913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76531968337949937392893217 57398976253462453044669913)
                ·
                  refine ⟨43049232190096839783502435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57398976253462453044669913 43049232190096839783502435)
                  ·
                    refine ⟨64573848285145259675253653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43049232190096839783502435 64573848285145259675253653)
                    ·
                      refine ⟨3026899138366184047277515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64573848285145259675253653 3026899138366184047277515)
                      ·
                        rfl

theorem cell23_5894865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_5894865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894865 prefixEnd_5894865 := by exact prefixLift 5894865
  have htrace : WordTrace (prefixWord ++ tailWord_5894865) baseStart_5894865 baseEnd_5894865 := by
    simpa [prefixWord, tailWord_5894865, baseEnd_5894865] using wordTrace_append hprefix tailTrace_5894865
  have hstable : (prefixWord ++ tailWord_5894865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894865).length < 2 ^ (prefixWord ++ tailWord_5894865).sum := by decide
  have hdescent : baseEnd_5894865 < baseStart_5894865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894872 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_5894872 : Nat := 118140960795 + 5894872 * 2 ^ 59
def prefixEnd_5894872 : Nat := 4983230072969 + 3 ^ 40 * 5894872 * 2
def baseEnd_5894872 : Nat := 3026902732730765519889983

theorem tailTrace_5894872 : CollatzResearch.WordTrace tailWord_5894872 prefixEnd_5894872 3026902732730765519889983 := by
  unfold tailWord_5894872
  simp only [CollatzResearch.WordTrace]
  refine ⟨107501822549946491415067435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143335763399928655220089913 107501822549946491415067435)
  ·
    refine ⟨161252733824919737122601153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107501822549946491415067435 161252733824919737122601153)
    ·
      refine ⟨120939550368689802841950865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161252733824919737122601153 120939550368689802841950865)
      ·
        refine ⟨90704662776517352131463149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120939550368689802841950865 90704662776517352131463149)
        ·
          refine ⟨34014248541194007049298681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90704662776517352131463149 34014248541194007049298681)
          ·
            refine ⟨25510686405895505286974011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34014248541194007049298681 25510686405895505286974011)
            ·
              refine ⟨38266029608843257930461017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25510686405895505286974011 38266029608843257930461017)
              ·
                refine ⟨28699522206632443447845763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38266029608843257930461017 28699522206632443447845763)
                ·
                  refine ⟨43049283309948665171768645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28699522206632443447845763 43049283309948665171768645)
                  ·
                    refine ⟨8071740620615374719706621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43049283309948665171768645 8071740620615374719706621)
                    ·
                      refine ⟨3026902732730765519889983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8071740620615374719706621 3026902732730765519889983)
                      ·
                        rfl

theorem cell23_5894872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_5894872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894872 prefixEnd_5894872 := by exact prefixLift 5894872
  have htrace : WordTrace (prefixWord ++ tailWord_5894872) baseStart_5894872 baseEnd_5894872 := by
    simpa [prefixWord, tailWord_5894872, baseEnd_5894872] using wordTrace_append hprefix tailTrace_5894872
  have hstable : (prefixWord ++ tailWord_5894872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894872).length < 2 ^ (prefixWord ++ tailWord_5894872).sum := by decide
  have hdescent : baseEnd_5894872 < baseStart_5894872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894915 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_5894915 : Nat := 118140960795 + 5894915 * 2 ^ 59
def prefixEnd_5894915 : Nat := 4983230072969 + 3 ^ 40 * 5894915 * 2
def baseEnd_5894915 : Nat := 3026924812398908851652285

theorem tailTrace_5894915 : CollatzResearch.WordTrace tailWord_5894915 prefixEnd_5894915 3026924812398908851652285 := by
  unfold tailWord_5894915
  simp only [CollatzResearch.WordTrace]
  refine ⟨215005213438737201173950199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143336808959158134115966799 215005213438737201173950199)
  ·
    refine ⟨322507820158105801760925299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215005213438737201173950199 322507820158105801760925299)
    ·
      refine ⟨483761730237158702641387949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322507820158105801760925299 483761730237158702641387949)
      ·
        refine ⟨181410648838934513490520481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483761730237158702641387949 181410648838934513490520481)
        ·
          refine ⟨136057986629200885117890361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181410648838934513490520481 136057986629200885117890361)
          ·
            refine ⟨102043489971900663838417771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136057986629200885117890361 102043489971900663838417771)
            ·
              refine ⟨153065234957850995757626657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102043489971900663838417771 153065234957850995757626657)
              ·
                refine ⟨114798926218388246818219993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153065234957850995757626657 114798926218388246818219993)
                ·
                  refine ⟨86099194663791185113664995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114798926218388246818219993 86099194663791185113664995)
                  ·
                    refine ⟨129148791995686777670497493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86099194663791185113664995 129148791995686777670497493)
                    ·
                      refine ⟨3026924812398908851652285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129148791995686777670497493 3026924812398908851652285)
                      ·
                        rfl

theorem cell23_5894915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_5894915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894915 prefixEnd_5894915 := by exact prefixLift 5894915
  have htrace : WordTrace (prefixWord ++ tailWord_5894915) baseStart_5894915 baseEnd_5894915 := by
    simpa [prefixWord, tailWord_5894915, baseEnd_5894915] using wordTrace_append hprefix tailTrace_5894915
  have hstable : (prefixWord ++ tailWord_5894915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894915).length < 2 ^ (prefixWord ++ tailWord_5894915).sum := by decide
  have hdescent : baseEnd_5894915 < baseStart_5894915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894922 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_5894922 : Nat := 118140960795 + 5894922 * 2 ^ 59
def prefixEnd_5894922 : Nat := 4983230072969 + 3 ^ 40 * 5894922 * 2
def baseEnd_5894922 : Nat := 1008976135587830108088251

theorem tailTrace_5894922 : CollatzResearch.WordTrace tailWord_5894922 prefixEnd_5894922 1008976135587830108088251 := by
  unfold tailWord_5894922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53751367187427960342363755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143336979166474560912970013 53751367187427960342363755)
  ·
    refine ⟨80627050781141940513545633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53751367187427960342363755 80627050781141940513545633)
    ·
      refine ⟨60470288085856455385159225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80627050781141940513545633 60470288085856455385159225)
      ·
        refine ⟨45352716064392341538869419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60470288085856455385159225 45352716064392341538869419)
        ·
          refine ⟨68029074096588512308304129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45352716064392341538869419 68029074096588512308304129)
          ·
            refine ⟨51021805572441384231228097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68029074096588512308304129 51021805572441384231228097)
            ·
              refine ⟨38266354179331038173421073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51021805572441384231228097 38266354179331038173421073)
              ·
                refine ⟨28699765634498278630065805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38266354179331038173421073 28699765634498278630065805)
                ·
                  refine ⟨10762412112936854486274677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28699765634498278630065805 10762412112936854486274677)
                  ·
                    refine ⟨1008976135587830108088251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10762412112936854486274677 1008976135587830108088251)
                    ·
                      rfl

theorem cell23_5894922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_5894922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894922 prefixEnd_5894922 := by exact prefixLift 5894922
  have htrace : WordTrace (prefixWord ++ tailWord_5894922) baseStart_5894922 baseEnd_5894922 := by
    simpa [prefixWord, tailWord_5894922, baseEnd_5894922] using wordTrace_append hprefix tailTrace_5894922
  have hstable : (prefixWord ++ tailWord_5894922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894922).length < 2 ^ (prefixWord ++ tailWord_5894922).sum := by decide
  have hdescent : baseEnd_5894922 < baseStart_5894922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894946 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_5894946 : Nat := 118140960795 + 5894946 * 2 ^ 59
def prefixEnd_5894946 : Nat := 4983230072969 + 3 ^ 40 * 5894946 * 2
def baseEnd_5894946 : Nat := 3026940730299198230364643

theorem tailTrace_5894946 : CollatzResearch.WordTrace tailWord_5894946 prefixEnd_5894946 3026940730299198230364643 := by
  unfold tailWord_5894946
  simp only [CollatzResearch.WordTrace]
  refine ⟨53751586025406223367082173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143337562734416595645552461 53751586025406223367082173)
  ·
    refine ⟨20156844759527333762655815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53751586025406223367082173 20156844759527333762655815)
    ·
      refine ⟨30235267139291000643983723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20156844759527333762655815 30235267139291000643983723)
      ·
        refine ⟨45352900708936500965975585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30235267139291000643983723 45352900708936500965975585)
        ·
          refine ⟨34014675531702375724481689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45352900708936500965975585 34014675531702375724481689)
          ·
            refine ⟨25511006648776781793361267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34014675531702375724481689 25511006648776781793361267)
            ·
              refine ⟨38266509973165172690041901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25511006648776781793361267 38266509973165172690041901)
              ·
                refine ⟨14349941239936939758765713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38266509973165172690041901 14349941239936939758765713)
                ·
                  refine ⟨10762455929952704819074285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14349941239936939758765713 10762455929952704819074285)
                  ·
                    refine ⟨4035920973732264307152857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10762455929952704819074285 4035920973732264307152857)
                    ·
                      refine ⟨3026940730299198230364643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035920973732264307152857 3026940730299198230364643)
                      ·
                        rfl

theorem cell23_5894946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_5894946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894946 prefixEnd_5894946 := by exact prefixLift 5894946
  have htrace : WordTrace (prefixWord ++ tailWord_5894946) baseStart_5894946 baseEnd_5894946 := by
    simpa [prefixWord, tailWord_5894946, baseEnd_5894946] using wordTrace_append hprefix tailTrace_5894946
  have hstable : (prefixWord ++ tailWord_5894946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894946).length < 2 ^ (prefixWord ++ tailWord_5894946).sum := by decide
  have hdescent : baseEnd_5894946 < baseStart_5894946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894972 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5894972 : Nat := 118140960795 + 5894972 * 2 ^ 59
def prefixEnd_5894972 : Nat := 4983230072969 + 3 ^ 40 * 5894972 * 2
def baseEnd_5894972 : Nat := 3026954080796215128639523

theorem tailTrace_5894972 : CollatzResearch.WordTrace tailWord_5894972 prefixEnd_5894972 3026954080796215128639523 := by
  unfold tailWord_5894972
  simp only [CollatzResearch.WordTrace]
  refine ⟨107503646199765349954387585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143338194933020466605850113 107503646199765349954387585)
  ·
    refine ⟨80627734649824012465790689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107503646199765349954387585 80627734649824012465790689)
    ·
      refine ⟨60470800987368009349343017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80627734649824012465790689 60470800987368009349343017)
      ·
        refine ⟨45353100740526007012007263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60470800987368009349343017 45353100740526007012007263)
        ·
          refine ⟨68029651110789010518010895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45353100740526007012007263 68029651110789010518010895)
          ·
            refine ⟨102044476666183515777016343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68029651110789010518010895 102044476666183515777016343)
            ·
              refine ⟨153066714999275273665524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102044476666183515777016343 153066714999275273665524515)
              ·
                refine ⟨229600072498912910498286773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153066714999275273665524515 229600072498912910498286773)
                ·
                  refine ⟨21525006796773085359214385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229600072498912910498286773 21525006796773085359214385)
                  ·
                    refine ⟨16143755097579814019410789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21525006796773085359214385 16143755097579814019410789)
                    ·
                      refine ⟨3026954080796215128639523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16143755097579814019410789 3026954080796215128639523)
                      ·
                        rfl

theorem cell23_5894972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5894972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894972 prefixEnd_5894972 := by exact prefixLift 5894972
  have htrace : WordTrace (prefixWord ++ tailWord_5894972) baseStart_5894972 baseEnd_5894972 := by
    simpa [prefixWord, tailWord_5894972, baseEnd_5894972] using wordTrace_append hprefix tailTrace_5894972
  have hstable : (prefixWord ++ tailWord_5894972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894972).length < 2 ^ (prefixWord ++ tailWord_5894972).sum := by decide
  have hdescent : baseEnd_5894972 < baseStart_5894972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894993 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 3, 2, 2]
def baseStart_5894993 : Nat := 118140960795 + 5894993 * 2 ^ 59
def prefixEnd_5894993 : Nat := 4983230072969 + 3 ^ 40 * 5894993 * 2
def baseEnd_5894993 : Nat := 3026964863889959546476927

theorem tailTrace_5894993 : CollatzResearch.WordTrace tailWord_5894993 prefixEnd_5894993 3026964863889959546476927 := by
  unfold tailWord_5894993
  simp only [CollatzResearch.WordTrace]
  refine ⟨215008058332454620495289633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143338705554969746996859755 215008058332454620495289633)
  ·
    refine ⟨161256043749340965371467225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215008058332454620495289633 161256043749340965371467225)
    ·
      refine ⟨120942032812005724028600419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161256043749340965371467225 120942032812005724028600419)
      ·
        refine ⟨181413049218008586042900629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120942032812005724028600419 181413049218008586042900629)
        ·
          refine ⟨8503736682094152470760967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181413049218008586042900629 8503736682094152470760967)
          ·
            refine ⟨12755605023141228706141451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503736682094152470760967 12755605023141228706141451)
            ·
              refine ⟨19133407534711843059212177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12755605023141228706141451 19133407534711843059212177)
              ·
                refine ⟨14350055651033882294409133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19133407534711843059212177 14350055651033882294409133)
                ·
                  refine ⟨5381270869137705860403425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14350055651033882294409133 5381270869137705860403425)
                  ·
                    refine ⟨4035953151853279395302569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5381270869137705860403425 4035953151853279395302569)
                    ·
                      refine ⟨3026964863889959546476927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4035953151853279395302569 3026964863889959546476927)
                      ·
                        rfl

theorem cell23_5894993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_5894993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894993 prefixEnd_5894993 := by exact prefixLift 5894993
  have htrace : WordTrace (prefixWord ++ tailWord_5894993) baseStart_5894993 baseEnd_5894993 := by
    simpa [prefixWord, tailWord_5894993, baseEnd_5894993] using wordTrace_append hprefix tailTrace_5894993
  have hstable : (prefixWord ++ tailWord_5894993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894993).length < 2 ^ (prefixWord ++ tailWord_5894993).sum := by decide
  have hdescent : baseEnd_5894993 < baseStart_5894993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5894999 : List Nat := [1, 1, 3, 2, 4, 2, 3, 7]
def baseStart_5894999 : Nat := 118140960795 + 5894999 * 2 ^ 59
def prefixEnd_5894999 : Nat := 4983230072969 + 3 ^ 40 * 5894999 * 2
def baseEnd_5894999 : Nat := 112109923880514315666737

theorem tailTrace_5894999 : CollatzResearch.WordTrace tailWord_5894999 prefixEnd_5894999 112109923880514315666737 := by
  unfold tailWord_5894999
  simp only [CollatzResearch.WordTrace]
  refine ⟨215008277170432883520008051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143338851446955255680005367 215008277170432883520008051)
  ·
    refine ⟨322512415755649325280012077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215008277170432883520008051 322512415755649325280012077)
    ·
      refine ⟨120942155908368496980004529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322512415755649325280012077 120942155908368496980004529)
      ·
        refine ⟨90706616931276372735003397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120942155908368496980004529 90706616931276372735003397)
        ·
          refine ⟨17007490674614319887813137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90706616931276372735003397 17007490674614319887813137)
          ·
            refine ⟨12755618005960739915859853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17007490674614319887813137 12755618005960739915859853)
            ·
              refine ⟨4783356752235277468447445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12755618005960739915859853 4783356752235277468447445)
              ·
                refine ⟨112109923880514315666737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4783356752235277468447445 112109923880514315666737)
                ·
                  rfl

theorem cell23_5894999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 7].length) (baseStart_5894999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5894999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5894999 prefixEnd_5894999 := by exact prefixLift 5894999
  have htrace : WordTrace (prefixWord ++ tailWord_5894999) baseStart_5894999 baseEnd_5894999 := by
    simpa [prefixWord, tailWord_5894999, baseEnd_5894999] using wordTrace_append hprefix tailTrace_5894999
  have hstable : (prefixWord ++ tailWord_5894999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5894999).length < 2 ^ (prefixWord ++ tailWord_5894999).sum := by decide
  have hdescent : baseEnd_5894999 < baseStart_5894999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5894999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895010 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_5895010 : Nat := 118140960795 + 5895010 * 2 ^ 59
def prefixEnd_5895010 : Nat := 4983230072969 + 3 ^ 40 * 5895010 * 2
def baseEnd_5895010 : Nat := 3026973593061085979964349

theorem tailTrace_5895010 : CollatzResearch.WordTrace tailWord_5895010 prefixEnd_5895010 3026973593061085979964349 := by
  unfold tailWord_5895010
  simp only [CollatzResearch.WordTrace]
  refine ⟨53752169593348258099664621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143339118915595354932438989 53752169593348258099664621)
  ·
    refine ⟨20157063597505596787374233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53752169593348258099664621 20157063597505596787374233)
    ·
      refine ⟨15117797698129197590530675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20157063597505596787374233 15117797698129197590530675)
      ·
        refine ⟨22676696547193796385796013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15117797698129197590530675 22676696547193796385796013)
        ·
          refine ⟨8503761205197673644673505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22676696547193796385796013 8503761205197673644673505)
          ·
            refine ⟨6377820903898255233505129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8503761205197673644673505 6377820903898255233505129)
            ·
              refine ⟨4783365677923691425128847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6377820903898255233505129 4783365677923691425128847)
              ·
                refine ⟨7175048516885537137693271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783365677923691425128847 7175048516885537137693271)
                ·
                  refine ⟨10762572775328305706539907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7175048516885537137693271 10762572775328305706539907)
                  ·
                    refine ⟨16143859162992458559809861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10762572775328305706539907 16143859162992458559809861)
                    ·
                      refine ⟨3026973593061085979964349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16143859162992458559809861 3026973593061085979964349)
                      ·
                        rfl

theorem cell23_5895010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_5895010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895010 prefixEnd_5895010 := by exact prefixLift 5895010
  have htrace : WordTrace (prefixWord ++ tailWord_5895010) baseStart_5895010 baseEnd_5895010 := by
    simpa [prefixWord, tailWord_5895010, baseEnd_5895010] using wordTrace_append hprefix tailTrace_5895010
  have hstable : (prefixWord ++ tailWord_5895010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895010).length < 2 ^ (prefixWord ++ tailWord_5895010).sum := by decide
  have hdescent : baseEnd_5895010 < baseStart_5895010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895032 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_5895032 : Nat := 118140960795 + 5895032 * 2 ^ 59
def prefixEnd_5895032 : Nat := 4983230072969 + 3 ^ 40 * 5895032 * 2
def baseEnd_5895032 : Nat := 3026984889635484893889247

theorem tailTrace_5895032 : CollatzResearch.WordTrace tailWord_5895032 prefixEnd_5895032 3026984889635484893889247 := by
  unfold tailWord_5895032
  simp only [CollatzResearch.WordTrace]
  refine ⟨107504740389656665077979675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143339653852875553437306233 107504740389656665077979675)
  ·
    refine ⟨161257110584484997616969513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107504740389656665077979675 161257110584484997616969513)
    ·
      refine ⟨120942832938363748212727135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161257110584484997616969513 120942832938363748212727135)
      ·
        refine ⟨181414249407545622319090703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120942832938363748212727135 181414249407545622319090703)
        ·
          refine ⟨272121374111318433478636055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181414249407545622319090703 272121374111318433478636055)
          ·
            refine ⟨408182061166977650217954083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272121374111318433478636055 408182061166977650217954083)
            ·
              refine ⟨612273091750466475326931125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408182061166977650217954083 612273091750466475326931125)
              ·
                refine ⟨57400602351606232061899793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 612273091750466475326931125 57400602351606232061899793)
                ·
                  refine ⟨43050451763704674046424845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57400602351606232061899793 43050451763704674046424845)
                  ·
                    refine ⟨16143919411389252767409317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43050451763704674046424845 16143919411389252767409317)
                    ·
                      refine ⟨3026984889635484893889247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16143919411389252767409317 3026984889635484893889247)
                      ·
                        rfl

theorem cell23_5895032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_5895032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895032 prefixEnd_5895032 := by exact prefixLift 5895032
  have htrace : WordTrace (prefixWord ++ tailWord_5895032) baseStart_5895032 baseEnd_5895032 := by
    simpa [prefixWord, tailWord_5895032, baseEnd_5895032] using wordTrace_append hprefix tailTrace_5895032
  have hstable : (prefixWord ++ tailWord_5895032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895032).length < 2 ^ (prefixWord ++ tailWord_5895032).sum := by decide
  have hdescent : baseEnd_5895032 < baseStart_5895032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895043 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 2, 1, 3]
def baseStart_5895043 : Nat := 118140960795 + 5895043 * 2 ^ 59
def prefixEnd_5895043 : Nat := 4983230072969 + 3 ^ 40 * 5895043 * 2
def baseEnd_5895043 : Nat := 3026990537922684350851697

theorem tailTrace_5895043 : CollatzResearch.WordTrace tailWord_5895043 prefixEnd_5895043 3026990537922684350851697 := by
  unfold tailWord_5895043
  simp only [CollatzResearch.WordTrace]
  refine ⟨215009881982273479034609783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143339921321515652689739855 215009881982273479034609783)
  ·
    refine ⟨322514822973410218551914675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215009881982273479034609783 322514822973410218551914675)
    ·
      refine ⟨483772234460115327827872013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322514822973410218551914675 483772234460115327827872013)
      ·
        refine ⟨181414587922543247935452005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483772234460115327827872013 181414587922543247935452005)
        ·
          refine ⟨34015235235476858987897251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181414587922543247935452005 34015235235476858987897251)
          ·
            refine ⟨51022852853215288481845877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34015235235476858987897251 51022852853215288481845877)
            ·
              refine ⟨4783392454988933295173051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51022852853215288481845877 4783392454988933295173051)
              ·
                refine ⟨7175088682483399942759577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783392454988933295173051 7175088682483399942759577)
                ·
                  refine ⟨5381316511862549957069683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7175088682483399942759577 5381316511862549957069683)
                  ·
                    refine ⟨8071974767793824935604525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5381316511862549957069683 8071974767793824935604525)
                    ·
                      refine ⟨3026990537922684350851697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8071974767793824935604525 3026990537922684350851697)
                      ·
                        rfl

theorem cell23_5895043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_5895043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895043 prefixEnd_5895043 := by exact prefixLift 5895043
  have htrace : WordTrace (prefixWord ++ tailWord_5895043) baseStart_5895043 baseEnd_5895043 := by
    simpa [prefixWord, tailWord_5895043, baseEnd_5895043] using wordTrace_append hprefix tailTrace_5895043
  have hstable : (prefixWord ++ tailWord_5895043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895043).length < 2 ^ (prefixWord ++ tailWord_5895043).sum := by decide
  have hdescent : baseEnd_5895043 < baseStart_5895043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895069 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_5895069 : Nat := 118140960795 + 5895069 * 2 ^ 59
def prefixEnd_5895069 : Nat := 4983230072969 + 3 ^ 40 * 5895069 * 2
def baseEnd_5895069 : Nat := 3027003888419701249126577

theorem tailTrace_5895069 : CollatzResearch.WordTrace tailWord_5895069 prefixEnd_5895069 3027003888419701249126577 := by
  unfold tailWord_5895069
  simp only [CollatzResearch.WordTrace]
  refine ⟨215010830280179285475056261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143340553520119523650037507 215010830280179285475056261)
  ·
    refine ⟨40314530677533616026573049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215010830280179285475056261 40314530677533616026573049)
    ·
      refine ⟨30235898008150212019929787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40314530677533616026573049 30235898008150212019929787)
      ·
        refine ⟨45353847012225318029894681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30235898008150212019929787 45353847012225318029894681)
        ·
          refine ⟨34015385259168988522421011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45353847012225318029894681 34015385259168988522421011)
          ·
            refine ⟨51023077888753482783631517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34015385259168988522421011 51023077888753482783631517)
            ·
              refine ⟨19133654208282556043861819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51023077888753482783631517 19133654208282556043861819)
              ·
                refine ⟨28700481312423834065792729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19133654208282556043861819 28700481312423834065792729)
                ·
                  refine ⟨21525360984317875549344547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28700481312423834065792729 21525360984317875549344547)
                  ·
                    refine ⟨32288041476476813324016821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21525360984317875549344547 32288041476476813324016821)
                    ·
                      refine ⟨3027003888419701249126577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32288041476476813324016821 3027003888419701249126577)
                      ·
                        rfl

theorem cell23_5895069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_5895069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895069 prefixEnd_5895069 := by exact prefixLift 5895069
  have htrace : WordTrace (prefixWord ++ tailWord_5895069) baseStart_5895069 baseEnd_5895069 := by
    simpa [prefixWord, tailWord_5895069, baseEnd_5895069] using wordTrace_append hprefix tailTrace_5895069
  have hstable : (prefixWord ++ tailWord_5895069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895069).length < 2 ^ (prefixWord ++ tailWord_5895069).sum := by decide
  have hdescent : baseEnd_5895069 < baseStart_5895069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895072 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 9]
def baseStart_5895072 : Nat := 118140960795 + 5895072 * 2 ^ 59
def prefixEnd_5895072 : Nat := 4983230072969 + 3 ^ 40 * 5895072 * 2
def baseEnd_5895072 : Nat := 336333936540184970821007

theorem tailTrace_5895072 : CollatzResearch.WordTrace tailWord_5895072 prefixEnd_5895072 336333936540184970821007 := by
  unfold tailWord_5895072
  simp only [CollatzResearch.WordTrace]
  refine ⟨107505469849584208493707735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143340626466112277991610313 107505469849584208493707735)
  ·
    refine ⟨161258204774376312740561603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107505469849584208493707735 161258204774376312740561603)
    ·
      refine ⟨241887307161564469110842405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161258204774376312740561603 241887307161564469110842405)
      ·
        refine ⟨45353870092793337958282951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241887307161564469110842405 45353870092793337958282951)
        ·
          refine ⟨68030805139190006937424427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45353870092793337958282951 68030805139190006937424427)
          ·
            refine ⟨102046207708785010406136641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68030805139190006937424427 102046207708785010406136641)
            ·
              refine ⟨76534655781588757804602481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102046207708785010406136641 76534655781588757804602481)
              ·
                refine ⟨57400991836191568353451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76534655781588757804602481 57400991836191568353451861)
                ·
                  refine ⟨336333936540184970821007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57400991836191568353451861 336333936540184970821007)
                  ·
                    rfl

theorem cell23_5895072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_5895072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895072 prefixEnd_5895072 := by exact prefixLift 5895072
  have htrace : WordTrace (prefixWord ++ tailWord_5895072) baseStart_5895072 baseEnd_5895072 := by
    simpa [prefixWord, tailWord_5895072, baseEnd_5895072] using wordTrace_append hprefix tailTrace_5895072
  have hstable : (prefixWord ++ tailWord_5895072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895072).length < 2 ^ (prefixWord ++ tailWord_5895072).sum := by decide
  have hdescent : baseEnd_5895072 < baseStart_5895072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895094 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5895094 : Nat := 118140960795 + 5895094 * 2 ^ 59
def prefixEnd_5895094 : Nat := 4983230072969 + 3 ^ 40 * 5895094 * 2
def baseEnd_5895094 : Nat := 3027016725436063651313963

theorem tailTrace_5895094 : CollatzResearch.WordTrace tailWord_5895094 prefixEnd_5895094 3027016725436063651313963 := by
  unfold tailWord_5895094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438233881568044671544771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143341161403392476496477557 13438233881568044671544771)
  ·
    refine ⟨20157350822352067007317157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13438233881568044671544771 20157350822352067007317157)
    ·
      refine ⟨3779503279191012563871967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20157350822352067007317157 3779503279191012563871967)
      ·
        refine ⟨5669254918786518845807951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779503279191012563871967 5669254918786518845807951)
        ·
          refine ⟨8503882378179778268711927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669254918786518845807951 8503882378179778268711927)
          ·
            refine ⟨12755823567269667403067891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503882378179778268711927 12755823567269667403067891)
            ·
              refine ⟨19133735350904501104601837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12755823567269667403067891 19133735350904501104601837)
              ·
                refine ⟨7175150756589187914225689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19133735350904501104601837 7175150756589187914225689)
                ·
                  refine ⟨5381363067441890935669267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7175150756589187914225689 5381363067441890935669267)
                  ·
                    refine ⟨8072044601162836403503901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5381363067441890935669267 8072044601162836403503901)
                    ·
                      refine ⟨3027016725436063651313963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8072044601162836403503901 3027016725436063651313963)
                      ·
                        rfl

theorem cell23_5895094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5895094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895094 prefixEnd_5895094 := by exact prefixLift 5895094
  have htrace : WordTrace (prefixWord ++ tailWord_5895094) baseStart_5895094 baseEnd_5895094 := by
    simpa [prefixWord, tailWord_5895094, baseEnd_5895094] using wordTrace_append hprefix tailTrace_5895094
  have hstable : (prefixWord ++ tailWord_5895094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895094).length < 2 ^ (prefixWord ++ tailWord_5895094).sum := by decide
  have hdescent : baseEnd_5895094 < baseStart_5895094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895119 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 2, 5]
def baseStart_5895119 : Nat := 118140960795 + 5895119 * 2 ^ 59
def prefixEnd_5895119 : Nat := 4983230072969 + 3 ^ 40 * 5895119 * 2
def baseEnd_5895119 : Nat := 1009009854150808684500449

theorem tailTrace_5895119 : CollatzResearch.WordTrace tailWord_5895119 prefixEnd_5895119 1009009854150808684500449 := by
  unfold tailWord_5895119
  simp only [CollatzResearch.WordTrace]
  refine ⟨215012653929998144014376411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143341769286665429342917607 215012653929998144014376411)
  ·
    refine ⟨322518980894997216021564617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215012653929998144014376411 322518980894997216021564617)
    ·
      refine ⟨241889235671247912016173463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322518980894997216021564617 241889235671247912016173463)
      ·
        refine ⟨362833853506871868024260195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241889235671247912016173463 362833853506871868024260195)
        ·
          refine ⟨544250780260307802036390293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362833853506871868024260195 544250780260307802036390293)
          ·
            refine ⟨25511755324701928220455795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 544250780260307802036390293 25511755324701928220455795)
            ·
              refine ⟨38267632987052892330683693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25511755324701928220455795 38267632987052892330683693)
              ·
                refine ⟨14350362370144834624006385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38267632987052892330683693 14350362370144834624006385)
                ·
                  refine ⟨10762771777608625968004789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14350362370144834624006385 10762771777608625968004789)
                  ·
                    refine ⟨1009009854150808684500449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10762771777608625968004789 1009009854150808684500449)
                    ·
                      rfl

theorem cell23_5895119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_5895119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895119 prefixEnd_5895119 := by exact prefixLift 5895119
  have htrace : WordTrace (prefixWord ++ tailWord_5895119) baseStart_5895119 baseEnd_5895119 := by
    simpa [prefixWord, tailWord_5895119, baseEnd_5895119] using wordTrace_append hprefix tailTrace_5895119
  have hstable : (prefixWord ++ tailWord_5895119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895119).length < 2 ^ (prefixWord ++ tailWord_5895119).sum := by decide
  have hdescent : baseEnd_5895119 < baseStart_5895119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895129 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_5895129 : Nat := 118140960795 + 5895129 * 2 ^ 59
def prefixEnd_5895129 : Nat := 4983230072969 + 3 ^ 40 * 5895129 * 2
def baseEnd_5895129 : Nat := 3027034697258971014376301

theorem tailTrace_5895129 : CollatzResearch.WordTrace tailWord_5895129 prefixEnd_5895129 3027034697258971014376301 := by
  unfold tailWord_5895129
  simp only [CollatzResearch.WordTrace]
  refine ⟨215013018659961915722240441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143342012439974610481493627 215013018659961915722240441)
  ·
    refine ⟨161259763994971436791680331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215013018659961915722240441 161259763994971436791680331)
    ·
      refine ⟨241889645992457155187520497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161259763994971436791680331 241889645992457155187520497)
      ·
        refine ⟨181417234494342866390640373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241889645992457155187520497 181417234494342866390640373)
        ·
          refine ⟨17007865733844643724122535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181417234494342866390640373 17007865733844643724122535)
          ·
            refine ⟨25511798600766965586183803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17007865733844643724122535 25511798600766965586183803)
            ·
              refine ⟨38267697901150448379275705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25511798600766965586183803 38267697901150448379275705)
              ·
                refine ⟨28700773425862836284456779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38267697901150448379275705 28700773425862836284456779)
                ·
                  refine ⟨43051160138794254426685169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28700773425862836284456779 43051160138794254426685169)
                  ·
                    refine ⟨32288370104095690820013877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43051160138794254426685169 32288370104095690820013877)
                    ·
                      refine ⟨3027034697258971014376301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32288370104095690820013877 3027034697258971014376301)
                      ·
                        rfl

theorem cell23_5895129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_5895129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895129 prefixEnd_5895129 := by exact prefixLift 5895129
  have htrace : WordTrace (prefixWord ++ tailWord_5895129) baseStart_5895129 baseEnd_5895129 := by
    simpa [prefixWord, tailWord_5895129, baseEnd_5895129] using wordTrace_append hprefix tailTrace_5895129
  have hstable : (prefixWord ++ tailWord_5895129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895129).length < 2 ^ (prefixWord ++ tailWord_5895129).sum := by decide
  have hdescent : baseEnd_5895129 < baseStart_5895129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895176 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_5895176 : Nat := 118140960795 + 5895176 * 2 ^ 59
def prefixEnd_5895176 : Nat := 4983230072969 + 3 ^ 40 * 5895176 * 2
def baseEnd_5895176 : Nat := 3027058830849732330488585

theorem tailTrace_5895176 : CollatzResearch.WordTrace tailWord_5895176 prefixEnd_5895176 3027058830849732330488585 := by
  unfold tailWord_5895176
  simp only [CollatzResearch.WordTrace]
  refine ⟨107507366445395821374600691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143343155260527761832800921 107507366445395821374600691)
  ·
    refine ⟨161261049668093732061901037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107507366445395821374600691 161261049668093732061901037)
    ·
      refine ⟨60472893625535149523212889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161261049668093732061901037 60472893625535149523212889)
      ·
        refine ⟨45354670219151362142409667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60472893625535149523212889 45354670219151362142409667)
        ·
          refine ⟨68032005328727043213614501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45354670219151362142409667 68032005328727043213614501)
          ·
            refine ⟨12756000999136320602552719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68032005328727043213614501 12756000999136320602552719)
            ·
              refine ⟨19134001498704480903829079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756000999136320602552719 19134001498704480903829079)
              ·
                refine ⟨28701002248056721355743619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19134001498704480903829079 28701002248056721355743619)
                ·
                  refine ⟨43051503372085082033615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28701002248056721355743619 43051503372085082033615429)
                  ·
                    refine ⟨8072156882265952881302893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43051503372085082033615429 8072156882265952881302893)
                    ·
                      refine ⟨3027058830849732330488585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8072156882265952881302893 3027058830849732330488585)
                      ·
                        rfl

theorem cell23_5895176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_5895176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895176 prefixEnd_5895176 := by exact prefixLift 5895176
  have htrace : WordTrace (prefixWord ++ tailWord_5895176) baseStart_5895176 baseEnd_5895176 := by
    simpa [prefixWord, tailWord_5895176, baseEnd_5895176] using wordTrace_append hprefix tailTrace_5895176
  have hstable : (prefixWord ++ tailWord_5895176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895176).length < 2 ^ (prefixWord ++ tailWord_5895176).sum := by decide
  have hdescent : baseEnd_5895176 < baseStart_5895176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895196 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 8]
def baseStart_5895196 : Nat := 118140960795 + 5895196 * 2 ^ 59
def prefixEnd_5895196 : Nat := 4983230072969 + 3 ^ 40 * 5895196 * 2
def baseEnd_5895196 : Nat := 336341011162535805804277

theorem tailTrace_5895196 : CollatzResearch.WordTrace tailWord_5895196 prefixEnd_5895196 336341011162535805804277 := by
  unfold tailWord_5895196
  simp only [CollatzResearch.WordTrace]
  refine ⟨107507731175359593082464721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143343641567146124109952961 107507731175359593082464721)
  ·
    refine ⟨80630798381519694811848541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107507731175359593082464721 80630798381519694811848541)
    ·
      refine ⟨30236549393069885554443203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80630798381519694811848541 30236549393069885554443203)
      ·
        refine ⟨45354824089604828331664805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30236549393069885554443203 45354824089604828331664805)
        ·
          refine ⟨8504029516800905312187151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45354824089604828331664805 8504029516800905312187151)
          ·
            refine ⟨12756044275201357968280727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8504029516800905312187151 12756044275201357968280727)
            ·
              refine ⟨19134066412802036952421091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756044275201357968280727 19134066412802036952421091)
              ·
                refine ⟨28701099619203055428631637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19134066412802036952421091 28701099619203055428631637)
                ·
                  refine ⟨336341011162535805804277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28701099619203055428631637 336341011162535805804277)
                  ·
                    rfl

theorem cell23_5895196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_5895196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895196 prefixEnd_5895196 := by exact prefixLift 5895196
  have htrace : WordTrace (prefixWord ++ tailWord_5895196) baseStart_5895196 baseEnd_5895196 := by
    simpa [prefixWord, tailWord_5895196, baseEnd_5895196] using wordTrace_append hprefix tailTrace_5895196
  have hstable : (prefixWord ++ tailWord_5895196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895196).length < 2 ^ (prefixWord ++ tailWord_5895196).sum := by decide
  have hdescent : baseEnd_5895196 < baseStart_5895196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895199 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_5895199 : Nat := 118140960795 + 5895199 * 2 ^ 59
def prefixEnd_5895199 : Nat := 4983230072969 + 3 ^ 40 * 5895199 * 2
def baseEnd_5895199 : Nat := 3027070640904785740500979

theorem tailTrace_5895199 : CollatzResearch.WordTrace tailWord_5895199 prefixEnd_5895199 3027070640904785740500979 := by
  unfold tailWord_5895199
  simp only [CollatzResearch.WordTrace]
  refine ⟨215015571769708317677288651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143343714513138878451525767 215015571769708317677288651)
  ·
    refine ⟨322523357654562476515932977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215015571769708317677288651 322523357654562476515932977)
    ·
      refine ⟨241892518240921857386949733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322523357654562476515932977 241892518240921857386949733)
      ·
        refine ⟨45354847170172848260053075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241892518240921857386949733 45354847170172848260053075)
        ·
          refine ⟨68032270755259272390079613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45354847170172848260053075 68032270755259272390079613)
          ·
            refine ⟨25512101533222227146279855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68032270755259272390079613 25512101533222227146279855)
            ·
              refine ⟨38268152299833340719419783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25512101533222227146279855 38268152299833340719419783)
              ·
                refine ⟨57402228449750011079129675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38268152299833340719419783 57402228449750011079129675)
                ·
                  refine ⟨86103342674625016618694513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57402228449750011079129675 86103342674625016618694513)
                  ·
                    refine ⟨64577507005968762464020885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86103342674625016618694513 64577507005968762464020885)
                    ·
                      refine ⟨3027070640904785740500979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64577507005968762464020885 3027070640904785740500979)
                      ·
                        rfl

theorem cell23_5895199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_5895199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895199 prefixEnd_5895199 := by exact prefixLift 5895199
  have htrace : WordTrace (prefixWord ++ tailWord_5895199) baseStart_5895199 baseEnd_5895199 := by
    simpa [prefixWord, tailWord_5895199, baseEnd_5895199] using wordTrace_append hprefix tailTrace_5895199
  have hstable : (prefixWord ++ tailWord_5895199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895199).length < 2 ^ (prefixWord ++ tailWord_5895199).sum := by decide
  have hdescent : baseEnd_5895199 < baseStart_5895199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895200 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 3, 4]
def baseStart_5895200 : Nat := 118140960795 + 5895200 * 2 ^ 59
def prefixEnd_5895200 : Nat := 4983230072969 + 3 ^ 40 * 5895200 * 2
def baseEnd_5895200 : Nat := 1009023718128480078862825

theorem tailTrace_5895200 : CollatzResearch.WordTrace tailWord_5895200 prefixEnd_5895200 1009023718128480078862825 := by
  unfold tailWord_5895200
  simp only [CollatzResearch.WordTrace]
  refine ⟨107507804121352347424037527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143343738828469796565383369 107507804121352347424037527)
  ·
    refine ⟨161261706182028521136056291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107507804121352347424037527 161261706182028521136056291)
    ·
      refine ⟨241892559273042781704084437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161261706182028521136056291 241892559273042781704084437)
      ·
        refine ⟨5669356857961940196189479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 241892559273042781704084437 5669356857961940196189479)
        ·
          refine ⟨8504035286942910294284219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669356857961940196189479 8504035286942910294284219)
          ·
            refine ⟨12756052930414365441426329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8504035286942910294284219 12756052930414365441426329)
            ·
              refine ⟨9567039697810774081069747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12756052930414365441426329 9567039697810774081069747)
              ·
                refine ⟨14350559546716161121604621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9567039697810774081069747 14350559546716161121604621)
                ·
                  refine ⟨5381459830018560420601733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14350559546716161121604621 5381459830018560420601733)
                  ·
                    refine ⟨1009023718128480078862825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5381459830018560420601733 1009023718128480078862825)
                    ·
                      rfl

theorem cell23_5895200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_5895200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895200 prefixEnd_5895200 := by exact prefixLift 5895200
  have htrace : WordTrace (prefixWord ++ tailWord_5895200) baseStart_5895200 baseEnd_5895200 := by
    simpa [prefixWord, tailWord_5895200, baseEnd_5895200] using wordTrace_append hprefix tailTrace_5895200
  have hstable : (prefixWord ++ tailWord_5895200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895200).length < 2 ^ (prefixWord ++ tailWord_5895200).sum := by decide
  have hdescent : baseEnd_5895200 < baseStart_5895200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895216 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 3, 5, 2]
def baseStart_5895216 : Nat := 118140960795 + 5895216 * 2 ^ 59
def prefixEnd_5895216 : Nat := 4983230072969 + 3 ^ 40 * 5895216 * 2
def baseEnd_5895216 : Nat := 3027079370075912173988401

theorem tailTrace_5895216 : CollatzResearch.WordTrace tailWord_5895216 prefixEnd_5895216 3027079370075912173988401 := by
  unfold tailWord_5895216
  simp only [CollatzResearch.WordTrace]
  refine ⟨107508095905323364790328751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143344127873764486387105001 107508095905323364790328751)
  ·
    refine ⟨161262143857985047185493127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107508095905323364790328751 161262143857985047185493127)
    ·
      refine ⟨241893215786977570778239691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161262143857985047185493127 241893215786977570778239691)
      ·
        refine ⟨362839823680466356167359537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241893215786977570778239691 362839823680466356167359537)
        ·
          refine ⟨272129867760349767125519653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362839823680466356167359537 272129867760349767125519653)
          ·
            refine ⟨51024350205065581336034935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272129867760349767125519653 51024350205065581336034935)
            ·
              refine ⟨76536525307598372004052403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51024350205065581336034935 76536525307598372004052403)
              ·
                refine ⟨114804787961397558006078605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76536525307598372004052403 114804787961397558006078605)
                ·
                  refine ⟨43051795485524084252279477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114804787961397558006078605 43051795485524084252279477)
                  ·
                    refine ⟨4036105826767882898651201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43051795485524084252279477 4036105826767882898651201)
                    ·
                      refine ⟨3027079370075912173988401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036105826767882898651201 3027079370075912173988401)
                      ·
                        rfl

theorem cell23_5895216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 5, 2].length) (baseStart_5895216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895216 prefixEnd_5895216 := by exact prefixLift 5895216
  have htrace : WordTrace (prefixWord ++ tailWord_5895216) baseStart_5895216 baseEnd_5895216 := by
    simpa [prefixWord, tailWord_5895216, baseEnd_5895216] using wordTrace_append hprefix tailTrace_5895216
  have hstable : (prefixWord ++ tailWord_5895216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895216).length < 2 ^ (prefixWord ++ tailWord_5895216).sum := by decide
  have hdescent : baseEnd_5895216 < baseStart_5895216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895226 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_5895226 : Nat := 118140960795 + 5895226 * 2 ^ 59
def prefixEnd_5895226 : Nat := 4983230072969 + 3 ^ 40 * 5895226 * 2
def baseEnd_5895226 : Nat := 1009028168294152378287785

theorem tailTrace_5895226 : CollatzResearch.WordTrace tailWord_5895226 prefixEnd_5895226 1009028168294152378287785 := by
  unfold tailWord_5895226
  simp only [CollatzResearch.WordTrace]
  refine ⟨53754139135152625322130383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143344371027073667525681021 53754139135152625322130383)
  ·
    refine ⟨80631208702728937983195575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53754139135152625322130383 80631208702728937983195575)
    ·
      refine ⟨120946813054093406974793363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80631208702728937983195575 120946813054093406974793363)
      ·
        refine ⟨181420219581140110462190045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120946813054093406974793363 181420219581140110462190045)
        ·
          refine ⟨68032582342927541423321267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181420219581140110462190045 68032582342927541423321267)
          ·
            refine ⟨102048873514391312134981901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68032582342927541423321267 102048873514391312134981901)
            ·
              refine ⟨38268327567896742050618213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102048873514391312134981901 38268327567896742050618213)
              ·
                refine ⟨7175311418980639134490915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38268327567896742050618213 7175311418980639134490915)
                ·
                  refine ⟨10762967128470958701736373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7175311418980639134490915 10762967128470958701736373)
                  ·
                    refine ⟨1009028168294152378287785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10762967128470958701736373 1009028168294152378287785)
                    ·
                      rfl

theorem cell23_5895226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_5895226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895226 prefixEnd_5895226 := by exact prefixLift 5895226
  have htrace : WordTrace (prefixWord ++ tailWord_5895226) baseStart_5895226 baseEnd_5895226 := by
    simpa [prefixWord, tailWord_5895226, baseEnd_5895226] using wordTrace_append hprefix tailTrace_5895226
  have hstable : (prefixWord ++ tailWord_5895226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895226).length < 2 ^ (prefixWord ++ tailWord_5895226).sum := by decide
  have hdescent : baseEnd_5895226 < baseStart_5895226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895250 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_5895250 : Nat := 118140960795 + 5895250 * 2 ^ 59
def prefixEnd_5895250 : Nat := 4983230072969 + 3 ^ 40 * 5895250 * 2
def baseEnd_5895250 : Nat := 3027096828418165040963245

theorem tailTrace_5895250 : CollatzResearch.WordTrace tailWord_5895250 prefixEnd_5895250 3027096828418165040963245 := by
  unfold tailWord_5895250
  simp only [CollatzResearch.WordTrace]
  refine ⟨53754357973130888346848801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143344954595015702258263469 53754357973130888346848801)
  ·
    refine ⟨40315768479848166260136601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53754357973130888346848801 40315768479848166260136601)
    ·
      refine ⟨30236826359886124695102451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40315768479848166260136601 30236826359886124695102451)
      ·
        refine ⟨45355239539829187042653677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30236826359886124695102451 45355239539829187042653677)
        ·
          refine ⟨17008214827435945140995129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45355239539829187042653677 17008214827435945140995129)
          ·
            refine ⟨12756161120576958855746347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17008214827435945140995129 12756161120576958855746347)
            ·
              refine ⟨19134241680865438283619521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756161120576958855746347 19134241680865438283619521)
              ·
                refine ⟨14350681260649078712714641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19134241680865438283619521 14350681260649078712714641)
                ·
                  refine ⟨10763010945486809034535981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14350681260649078712714641 10763010945486809034535981)
                  ·
                    refine ⟨4036129104557553387950993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10763010945486809034535981 4036129104557553387950993)
                    ·
                      refine ⟨3027096828418165040963245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036129104557553387950993 3027096828418165040963245)
                      ·
                        rfl

theorem cell23_5895250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_5895250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895250 prefixEnd_5895250 := by exact prefixLift 5895250
  have htrace : WordTrace (prefixWord ++ tailWord_5895250) baseStart_5895250 baseEnd_5895250 := by
    simpa [prefixWord, tailWord_5895250, baseEnd_5895250] using wordTrace_append hprefix tailTrace_5895250
  have hstable : (prefixWord ++ tailWord_5895250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895250).length < 2 ^ (prefixWord ++ tailWord_5895250).sum := by decide
  have hdescent : baseEnd_5895250 < baseStart_5895250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895256 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 4, 4]
def baseStart_5895256 : Nat := 118140960795 + 5895256 * 2 ^ 59
def prefixEnd_5895256 : Nat := 4983230072969 + 3 ^ 40 * 5895256 * 2
def baseEnd_5895256 : Nat := 1009033303100697339162739

theorem tailTrace_5895256 : CollatzResearch.WordTrace tailWord_5895256 prefixEnd_5895256 1009033303100697339162739 := by
  unfold tailWord_5895256
  simp only [CollatzResearch.WordTrace]
  refine ⟨107508825365250908206056811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143345100487001210941409081 107508825365250908206056811)
  ·
    refine ⟨161263238047876362309085217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107508825365250908206056811 161263238047876362309085217)
    ·
      refine ⟨120947428535907271731813913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161263238047876362309085217 120947428535907271731813913)
      ·
        refine ⟨90710571401930453798860435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120947428535907271731813913 90710571401930453798860435)
        ·
          refine ⟨136065857102895680698290653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90710571401930453798860435 136065857102895680698290653)
          ·
            refine ⟨51024696413585880261858995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136065857102895680698290653 51024696413585880261858995)
            ·
              refine ⟨76537044620378820392788493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51024696413585880261858995 76537044620378820392788493)
              ·
                refine ⟨28701391732642057647295685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76537044620378820392788493 28701391732642057647295685)
                ·
                  refine ⟨5381510949870385808867941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28701391732642057647295685 5381510949870385808867941)
                  ·
                    refine ⟨1009033303100697339162739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5381510949870385808867941 1009033303100697339162739)
                    ·
                      rfl

theorem cell23_5895256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_5895256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895256 prefixEnd_5895256 := by exact prefixLift 5895256
  have htrace : WordTrace (prefixWord ++ tailWord_5895256) baseStart_5895256 baseEnd_5895256 := by
    simpa [prefixWord, tailWord_5895256, baseEnd_5895256] using wordTrace_append hprefix tailTrace_5895256
  have hstable : (prefixWord ++ tailWord_5895256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895256).length < 2 ^ (prefixWord ++ tailWord_5895256).sum := by decide
  have hdescent : baseEnd_5895256 < baseStart_5895256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895273 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 2, 4]
def baseStart_5895273 : Nat := 118140960795 + 5895273 * 2 ^ 59
def prefixEnd_5895273 : Nat := 4983230072969 + 3 ^ 40 * 5895273 * 2
def baseEnd_5895273 : Nat := 1009036212824406150325213

theorem tailTrace_5895273 : CollatzResearch.WordTrace tailWord_5895273 prefixEnd_5895273 1009036212824406150325213 := by
  unfold tailWord_5895273
  simp only [CollatzResearch.WordTrace]
  refine ⟨215018270771440228315482473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143345513847626818876988315 215018270771440228315482473)
  ·
    refine ⟨161263703078580171236611855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215018270771440228315482473 161263703078580171236611855)
    ·
      refine ⟨241895554617870256854917783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161263703078580171236611855 241895554617870256854917783)
      ·
        refine ⟨362843331926805385282376675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241895554617870256854917783 362843331926805385282376675)
        ·
          refine ⟨544264997890208077923565013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362843331926805385282376675 544264997890208077923565013)
          ·
            refine ⟨12756210888051751826333555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 544264997890208077923565013 12756210888051751826333555)
            ·
              refine ⟨19134316332077627739500333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756210888051751826333555 19134316332077627739500333)
              ·
                refine ⟨7175368624529110402312625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19134316332077627739500333 7175368624529110402312625)
                ·
                  refine ⟨5381526468396832801734469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7175368624529110402312625 5381526468396832801734469)
                  ·
                    refine ⟨1009036212824406150325213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5381526468396832801734469 1009036212824406150325213)
                    ·
                      rfl

theorem cell23_5895273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_5895273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895273 prefixEnd_5895273 := by exact prefixLift 5895273
  have htrace : WordTrace (prefixWord ++ tailWord_5895273) baseStart_5895273 baseEnd_5895273 := by
    simpa [prefixWord, tailWord_5895273, baseEnd_5895273] using wordTrace_append hprefix tailTrace_5895273
  have hstable : (prefixWord ++ tailWord_5895273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895273).length < 2 ^ (prefixWord ++ tailWord_5895273).sum := by decide
  have hdescent : baseEnd_5895273 < baseStart_5895273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895276 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_5895276 : Nat := 118140960795 + 5895276 * 2 ^ 59
def prefixEnd_5895276 : Nat := 4983230072969 + 3 ^ 40 * 5895276 * 2
def baseEnd_5895276 : Nat := 3027110178915181939238125

theorem tailTrace_5895276 : CollatzResearch.WordTrace tailWord_5895276 prefixEnd_5895276 3027110178915181939238125 := by
  unfold tailWord_5895276
  simp only [CollatzResearch.WordTrace]
  refine ⟨107509190095214679913920841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143345586793619573218561121 107509190095214679913920841)
  ·
    refine ⟨80631892571411009935440631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107509190095214679913920841 80631892571411009935440631)
    ·
      refine ⟨120947838857116514903160947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80631892571411009935440631 120947838857116514903160947)
      ·
        refine ⟨181421758285674772354741421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120947838857116514903160947 181421758285674772354741421)
        ·
          refine ⟨68033159357128039633028033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181421758285674772354741421 68033159357128039633028033)
          ·
            refine ⟨51024869517846029724771025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68033159357128039633028033 51024869517846029724771025)
            ·
              refine ⟨38268652138384522293578269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51024869517846029724771025 38268652138384522293578269)
              ·
                refine ⟨14350744551894195860091851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38268652138384522293578269 14350744551894195860091851)
                ·
                  refine ⟨21526116827841293790137777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14350744551894195860091851 21526116827841293790137777)
                  ·
                    refine ⟨16144587620880970342603333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21526116827841293790137777 16144587620880970342603333)
                    ·
                      refine ⟨3027110178915181939238125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16144587620880970342603333 3027110178915181939238125)
                      ·
                        rfl

theorem cell23_5895276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_5895276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895276 prefixEnd_5895276 := by exact prefixLift 5895276
  have htrace : WordTrace (prefixWord ++ tailWord_5895276) baseStart_5895276 baseEnd_5895276 := by
    simpa [prefixWord, tailWord_5895276, baseEnd_5895276] using wordTrace_append hprefix tailTrace_5895276
  have hstable : (prefixWord ++ tailWord_5895276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895276).length < 2 ^ (prefixWord ++ tailWord_5895276).sum := by decide
  have hdescent : baseEnd_5895276 < baseStart_5895276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895286 : List Nat := [5, 1, 1, 2, 1, 1, 1, 11]
def baseStart_5895286 : Nat := 118140960795 + 5895286 * 2 ^ 59
def prefixEnd_5895286 : Nat := 4983230072969 + 3 ^ 40 * 5895286 * 2
def baseEnd_5895286 : Nat := 112115381989693588893077

theorem tailTrace_5895286 : CollatzResearch.WordTrace tailWord_5895286 prefixEnd_5895286 112115381989693588893077 := by
  unfold tailWord_5895286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438671557524570720981607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143345829946928754357137141 13438671557524570720981607)
  ·
    refine ⟨20158007336286856081472411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13438671557524570720981607 20158007336286856081472411)
    ·
      refine ⟨30237011004430284122208617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20158007336286856081472411 30237011004430284122208617)
      ·
        refine ⟨22677758253322713091656463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30237011004430284122208617 22677758253322713091656463)
        ·
          refine ⟨34016637379984069637484695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22677758253322713091656463 34016637379984069637484695)
          ·
            refine ⟨51024956069976104456227043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34016637379984069637484695 51024956069976104456227043)
            ·
              refine ⟨76537434104964156684340565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51024956069976104456227043 76537434104964156684340565)
              ·
                refine ⟨112115381989693588893077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 76537434104964156684340565 112115381989693588893077)
                ·
                  rfl

theorem cell23_5895286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_5895286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895286 prefixEnd_5895286 := by exact prefixLift 5895286
  have htrace : WordTrace (prefixWord ++ tailWord_5895286) baseStart_5895286 baseEnd_5895286 := by
    simpa [prefixWord, tailWord_5895286, baseEnd_5895286] using wordTrace_append hprefix tailTrace_5895286
  have hstable : (prefixWord ++ tailWord_5895286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895286).length < 2 ^ (prefixWord ++ tailWord_5895286).sum := by decide
  have hdescent : baseEnd_5895286 < baseStart_5895286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895296 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_5895296 : Nat := 118140960795 + 5895296 * 2 ^ 59
def prefixEnd_5895296 : Nat := 4983230072969 + 3 ^ 40 * 5895296 * 2
def baseEnd_5895296 : Nat := 3027120448528271860988033

theorem tailTrace_5895296 : CollatzResearch.WordTrace tailWord_5895296 prefixEnd_5895296 3027120448528271860988033 := by
  unfold tailWord_5895296
  simp only [CollatzResearch.WordTrace]
  refine ⟨107509554825178451621784871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143346073100237935495713161 107509554825178451621784871)
  ·
    refine ⟨161264332237767677432677307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107509554825178451621784871 161264332237767677432677307)
    ·
      refine ⟨241896498356651516149015961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161264332237767677432677307 241896498356651516149015961)
      ·
        refine ⟨181422373767488637111761971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241896498356651516149015961 181422373767488637111761971)
        ·
          refine ⟨272133560651232955667642957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181422373767488637111761971 272133560651232955667642957)
          ·
            refine ⟨102050085244212358375366109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272133560651232955667642957 102050085244212358375366109)
            ·
              refine ⟨38268781966579634390762291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102050085244212358375366109 38268781966579634390762291)
              ·
                refine ⟨57403172949869451586143437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38268781966579634390762291 57403172949869451586143437)
                ·
                  refine ⟨21526189856201044344803789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57403172949869451586143437 21526189856201044344803789)
                  ·
                    refine ⟨8072321196075391629301421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21526189856201044344803789 8072321196075391629301421)
                    ·
                      refine ⟨3027120448528271860988033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8072321196075391629301421 3027120448528271860988033)
                      ·
                        rfl

theorem cell23_5895296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_5895296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895296 prefixEnd_5895296 := by exact prefixLift 5895296
  have htrace : WordTrace (prefixWord ++ tailWord_5895296) baseStart_5895296 baseEnd_5895296 := by
    simpa [prefixWord, tailWord_5895296, baseEnd_5895296] using wordTrace_append hprefix tailTrace_5895296
  have hstable : (prefixWord ++ tailWord_5895296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895296).length < 2 ^ (prefixWord ++ tailWord_5895296).sum := by decide
  have hdescent : baseEnd_5895296 < baseStart_5895296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895314 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5895314 : Nat := 118140960795 + 5895314 * 2 ^ 59
def prefixEnd_5895314 : Nat := 4983230072969 + 3 ^ 40 * 5895314 * 2
def baseEnd_5895314 : Nat := 3027129691180052790562951

theorem tailTrace_5895314 : CollatzResearch.WordTrace tailWord_5895314 prefixEnd_5895314 3027129691180052790562951 := by
  unfold tailWord_5895314
  simp only [CollatzResearch.WordTrace]
  refine ⟨53754941541072923079431249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143346510776194461545149997 53754941541072923079431249)
  ·
    refine ⟨40316206155804692309573437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53754941541072923079431249 40316206155804692309573437)
    ·
      refine ⟨15118577308426759616090039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40316206155804692309573437 15118577308426759616090039)
      ·
        refine ⟨22677865962640139424135059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15118577308426759616090039 22677865962640139424135059)
        ·
          refine ⟨34016798943960209136202589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22677865962640139424135059 34016798943960209136202589)
          ·
            refine ⟨12756299603985078426075971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34016798943960209136202589 12756299603985078426075971)
            ·
              refine ⟨19134449405977617639113957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756299603985078426075971 19134449405977617639113957)
              ·
                refine ⟨3587709263620803307333867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19134449405977617639113957 3587709263620803307333867)
                ·
                  refine ⟨5381563895431204961000801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587709263620803307333867 5381563895431204961000801)
                  ·
                    refine ⟨4036172921573403720750601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5381563895431204961000801 4036172921573403720750601)
                    ·
                      refine ⟨3027129691180052790562951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036172921573403720750601 3027129691180052790562951)
                      ·
                        rfl

theorem cell23_5895314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5895314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895314 prefixEnd_5895314 := by exact prefixLift 5895314
  have htrace : WordTrace (prefixWord ++ tailWord_5895314) baseStart_5895314 baseEnd_5895314 := by
    simpa [prefixWord, tailWord_5895314, baseEnd_5895314] using wordTrace_append hprefix tailTrace_5895314
  have hstable : (prefixWord ++ tailWord_5895314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895314).length < 2 ^ (prefixWord ++ tailWord_5895314).sum := by decide
  have hdescent : baseEnd_5895314 < baseStart_5895314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895357 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_5895357 : Nat := 118140960795 + 5895357 * 2 ^ 59
def prefixEnd_5895357 : Nat := 4983230072969 + 3 ^ 40 * 5895357 * 2
def baseEnd_5895357 : Nat := 3027151770848196122325253

theorem tailTrace_5895357 : CollatzResearch.WordTrace tailWord_5895357 prefixEnd_5895357 3027151770848196122325253 := by
  unfold tailWord_5895357
  simp only [CollatzResearch.WordTrace]
  refine ⟨215021334503135910661540325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143347556335423940441026883 215021334503135910661540325)
  ·
    refine ⟨40316500219337983249038811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215021334503135910661540325 40316500219337983249038811)
    ·
      refine ⟨60474750329006974873558217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40316500219337983249038811 60474750329006974873558217)
      ·
        refine ⟨45356062746755231155168663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60474750329006974873558217 45356062746755231155168663)
        ·
          refine ⟨68034094120132846732752995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45356062746755231155168663 68034094120132846732752995)
          ·
            refine ⟨102051141180199270099129493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68034094120132846732752995 102051141180199270099129493)
            ·
              refine ⟨4783647242821840785896695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102051141180199270099129493 4783647242821840785896695)
              ·
                refine ⟨7175470864232761178845043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783647242821840785896695 7175470864232761178845043)
                ·
                  refine ⟨10763206296349141768267565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7175470864232761178845043 10763206296349141768267565)
                  ·
                    refine ⟨4036202361130928163100337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10763206296349141768267565 4036202361130928163100337)
                    ·
                      refine ⟨3027151770848196122325253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036202361130928163100337 3027151770848196122325253)
                      ·
                        rfl

theorem cell23_5895357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_5895357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895357 prefixEnd_5895357 := by exact prefixLift 5895357
  have htrace : WordTrace (prefixWord ++ tailWord_5895357) baseStart_5895357 baseEnd_5895357 := by
    simpa [prefixWord, tailWord_5895357, baseEnd_5895357] using wordTrace_append hprefix tailTrace_5895357
  have hstable : (prefixWord ++ tailWord_5895357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895357).length < 2 ^ (prefixWord ++ tailWord_5895357).sum := by decide
  have hdescent : baseEnd_5895357 < baseStart_5895357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895364 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_5895364 : Nat := 118140960795 + 5895364 * 2 ^ 59
def prefixEnd_5895364 : Nat := 4983230072969 + 3 ^ 40 * 5895364 * 2
def baseEnd_5895364 : Nat := 3027155365212777594937721

theorem tailTrace_5895364 : CollatzResearch.WordTrace tailWord_5895364 prefixEnd_5895364 3027155365212777594937721 := by
  unfold tailWord_5895364
  simp only [CollatzResearch.WordTrace]
  refine ⟨107510794907055275428522573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143347726542740367238030097 107510794907055275428522573)
  ·
    refine ⟨40316548090145728285695965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107510794907055275428522573 40316548090145728285695965)
    ·
      refine ⟨15118705533804648107135987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40316548090145728285695965 15118705533804648107135987)
      ·
        refine ⟨22678058300706972160703981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15118705533804648107135987 22678058300706972160703981)
        ·
          refine ⟨8504271862765114560263993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22678058300706972160703981 8504271862765114560263993)
          ·
            refine ⟨6378203897073835920197995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8504271862765114560263993 6378203897073835920197995)
            ·
              refine ⟨9567305845610753880296993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378203897073835920197995 9567305845610753880296993)
              ·
                refine ⟨7175479384208065410222745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9567305845610753880296993 7175479384208065410222745)
                ·
                  refine ⟨5381609538156049057667059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7175479384208065410222745 5381609538156049057667059)
                  ·
                    refine ⟨8072414307234073586500589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5381609538156049057667059 8072414307234073586500589)
                    ·
                      refine ⟨3027155365212777594937721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8072414307234073586500589 3027155365212777594937721)
                      ·
                        rfl

theorem cell23_5895364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_5895364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895364 prefixEnd_5895364 := by exact prefixLift 5895364
  have htrace : WordTrace (prefixWord ++ tailWord_5895364) baseStart_5895364 baseEnd_5895364 := by
    simpa [prefixWord, tailWord_5895364, baseEnd_5895364] using wordTrace_append hprefix tailTrace_5895364
  have hstable : (prefixWord ++ tailWord_5895364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895364).length < 2 ^ (prefixWord ++ tailWord_5895364).sum := by decide
  have hdescent : baseEnd_5895364 < baseStart_5895364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895423 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 2, 5]
def baseStart_5895423 : Nat := 118140960795 + 5895423 * 2 ^ 59
def prefixEnd_5895423 : Nat := 4983230072969 + 3 ^ 40 * 5895423 * 2
def baseEnd_5895423 : Nat := 1009061886857130954699983

theorem tailTrace_5895423 : CollatzResearch.WordTrace tailWord_5895423 prefixEnd_5895423 1009061886857130954699983 := by
  unfold tailWord_5895423
  simp only [CollatzResearch.WordTrace]
  refine ⟨215023741720896803933442923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143349161147264535955628615 215023741720896803933442923)
  ·
    refine ⟨322535612581345205900164385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215023741720896803933442923 322535612581345205900164385)
    ·
      refine ⟨241901709436008904425123289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322535612581345205900164385 241901709436008904425123289)
      ·
        refine ⟨181426282077006678318842467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241901709436008904425123289 181426282077006678318842467)
        ·
          refine ⟨272139423115510017478263701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181426282077006678318842467 272139423115510017478263701)
          ·
            refine ⟨12756535458539532069293611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 272139423115510017478263701 12756535458539532069293611)
            ·
              refine ⟨19134803187809298103940417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756535458539532069293611 19134803187809298103940417)
              ·
                refine ⟨14351102390856973577955313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19134803187809298103940417 14351102390856973577955313)
                ·
                  refine ⟨10763326793142730183466485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14351102390856973577955313 10763326793142730183466485)
                  ·
                    refine ⟨1009061886857130954699983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10763326793142730183466485 1009061886857130954699983)
                    ·
                      rfl

theorem cell23_5895423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_5895423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895423 prefixEnd_5895423 := by exact prefixLift 5895423
  have htrace : WordTrace (prefixWord ++ tailWord_5895423) baseStart_5895423 baseEnd_5895423 := by
    simpa [prefixWord, tailWord_5895423, baseEnd_5895423] using wordTrace_append hprefix tailTrace_5895423
  have hstable : (prefixWord ++ tailWord_5895423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895423).length < 2 ^ (prefixWord ++ tailWord_5895423).sum := by decide
  have hdescent : baseEnd_5895423 < baseStart_5895423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895460 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_5895460 : Nat := 118140960795 + 5895460 * 2 ^ 59
def prefixEnd_5895460 : Nat := 4983230072969 + 3 ^ 40 * 5895460 * 2
def baseEnd_5895460 : Nat := 3027204659355609219337279

theorem tailTrace_5895460 : CollatzResearch.WordTrace tailWord_5895460 prefixEnd_5895460 3027204659355609219337279 := by
  unfold tailWord_5895460
  simp only [CollatzResearch.WordTrace]
  refine ⟨107512545610881379626269917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143350060814508506168359889 107512545610881379626269917)
  ·
    refine ⟨40317204604080517359851219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107512545610881379626269917 40317204604080517359851219)
    ·
      refine ⟨60475806906120776039776829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40317204604080517359851219 60475806906120776039776829)
      ·
        refine ⟨22678427589795291014916311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60475806906120776039776829 22678427589795291014916311)
        ·
          refine ⟨34017641384692936522374467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22678427589795291014916311 34017641384692936522374467)
          ·
            refine ⟨51026462077039404783561701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34017641384692936522374467 51026462077039404783561701)
            ·
              refine ⟨9567461639444888396917819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51026462077039404783561701 9567461639444888396917819)
              ·
                refine ⟨14351192459167332595376729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9567461639444888396917819 14351192459167332595376729)
                ·
                  refine ⟨10763394344375499446532547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14351192459167332595376729 10763394344375499446532547)
                  ·
                    refine ⟨16145091516563249169798821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10763394344375499446532547 16145091516563249169798821)
                    ·
                      refine ⟨3027204659355609219337279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16145091516563249169798821 3027204659355609219337279)
                      ·
                        rfl

theorem cell23_5895460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_5895460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895460 prefixEnd_5895460 := by exact prefixLift 5895460
  have htrace : WordTrace (prefixWord ++ tailWord_5895460) baseStart_5895460 baseEnd_5895460 := by
    simpa [prefixWord, tailWord_5895460, baseEnd_5895460] using wordTrace_append hprefix tailTrace_5895460
  have hstable : (prefixWord ++ tailWord_5895460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895460).length < 2 ^ (prefixWord ++ tailWord_5895460).sum := by decide
  have hdescent : baseEnd_5895460 < baseStart_5895460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895478 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_5895478 : Nat := 118140960795 + 5895478 * 2 ^ 59
def prefixEnd_5895478 : Nat := 4983230072969 + 3 ^ 40 * 5895478 * 2
def baseEnd_5895478 : Nat := 336357100223043349879133

theorem tailTrace_5895478 : CollatzResearch.WordTrace tailWord_5895478 prefixEnd_5895478 336357100223043349879133 := by
  unfold tailWord_5895478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13439109233481096770418443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143350498490465032217796725 13439109233481096770418443)
  ·
    refine ⟨20158663850221645155627665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13439109233481096770418443 20158663850221645155627665)
    ·
      refine ⟨15118997887666233866720749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20158663850221645155627665 15118997887666233866720749)
      ·
        refine ⟨5669624207874837700020281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15118997887666233866720749 5669624207874837700020281)
        ·
          refine ⟨4252218155906128275015211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5669624207874837700020281 4252218155906128275015211)
          ·
            refine ⟨6378327233859192412522817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252218155906128275015211 6378327233859192412522817)
            ·
              refine ⟨4783745425394394309392113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6378327233859192412522817 4783745425394394309392113)
              ·
                refine ⟨3587809069045795732044085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783745425394394309392113 3587809069045795732044085)
                ·
                  refine ⟨336357100223043349879133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3587809069045795732044085 336357100223043349879133)
                  ·
                    rfl

theorem cell23_5895478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_5895478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895478 prefixEnd_5895478 := by exact prefixLift 5895478
  have htrace : WordTrace (prefixWord ++ tailWord_5895478) baseStart_5895478 baseEnd_5895478 := by
    simpa [prefixWord, tailWord_5895478, baseEnd_5895478] using wordTrace_append hprefix tailTrace_5895478
  have hstable : (prefixWord ++ tailWord_5895478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895478).length < 2 ^ (prefixWord ++ tailWord_5895478).sum := by decide
  have hdescent : baseEnd_5895478 < baseStart_5895478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895487 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 1, 4]
def baseStart_5895487 : Nat := 118140960795 + 5895487 * 2 ^ 59
def prefixEnd_5895487 : Nat := 4983230072969 + 3 ^ 40 * 5895487 * 2
def baseEnd_5895487 : Nat := 1009072841111093537899885

theorem tailTrace_5895487 : CollatzResearch.WordTrace tailWord_5895487 prefixEnd_5895487 1009072841111093537899885 := by
  unfold tailWord_5895487
  simp only [CollatzResearch.WordTrace]
  refine ⟨215026075992664942863772715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143350717328443295242515143 215026075992664942863772715)
  ·
    refine ⟨322539113988997414295659073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215026075992664942863772715 322539113988997414295659073)
    ·
      refine ⟨241904335491748060721744305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322539113988997414295659073 241904335491748060721744305)
      ·
        refine ⟨181428251618811045541308229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241904335491748060721744305 181428251618811045541308229)
        ·
          refine ⟨34017797178527071038995293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181428251618811045541308229 34017797178527071038995293)
          ·
            refine ⟨12756673941947651639623235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34017797178527071038995293 12756673941947651639623235)
            ·
              refine ⟨19135010912921477459434853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756673941947651639623235 19135010912921477459434853)
              ·
                refine ⟨3587814546172777023644035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19135010912921477459434853 3587814546172777023644035)
                ·
                  refine ⟨5381721819259165535466053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587814546172777023644035 5381721819259165535466053)
                  ·
                    refine ⟨1009072841111093537899885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5381721819259165535466053 1009072841111093537899885)
                    ·
                      rfl

theorem cell23_5895487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 4].length) (baseStart_5895487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895487 prefixEnd_5895487 := by exact prefixLift 5895487
  have htrace : WordTrace (prefixWord ++ tailWord_5895487) baseStart_5895487 baseEnd_5895487 := by
    simpa [prefixWord, tailWord_5895487, baseEnd_5895487] using wordTrace_append hprefix tailTrace_5895487
  have hstable : (prefixWord ++ tailWord_5895487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895487).length < 2 ^ (prefixWord ++ tailWord_5895487).sum := by decide
  have hdescent : baseEnd_5895487 < baseStart_5895487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895513 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_5895513 : Nat := 118140960795 + 5895513 * 2 ^ 59
def prefixEnd_5895513 : Nat := 4983230072969 + 3 ^ 40 * 5895513 * 2
def baseEnd_5895513 : Nat := 1009077291276765837324845

theorem tailTrace_5895513 : CollatzResearch.WordTrace tailWord_5895513 prefixEnd_5895513 1009077291276765837324845 := by
  unfold tailWord_5895513
  simp only [CollatzResearch.WordTrace]
  refine ⟨215027024290570749304219193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143351349527047166202812795 215027024290570749304219193)
  ·
    refine ⟨161270268217928061978164395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215027024290570749304219193 161270268217928061978164395)
    ·
      refine ⟨241905402326892092967246593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161270268217928061978164395 241905402326892092967246593)
      ·
        refine ⟨181429051745169069725434945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241905402326892092967246593 181429051745169069725434945)
        ·
          refine ⟨136071788808876802294076209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181429051745169069725434945 136071788808876802294076209)
          ·
            refine ⟨102053841606657601720557157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136071788808876802294076209 102053841606657601720557157)
            ·
              refine ⟨19135095301248300322604467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102053841606657601720557157 19135095301248300322604467)
              ·
                refine ⟨28702642951872450483906701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19135095301248300322604467 28702642951872450483906701)
                ·
                  refine ⟨10763491106952168931465013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28702642951872450483906701 10763491106952168931465013)
                  ·
                    refine ⟨1009077291276765837324845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10763491106952168931465013 1009077291276765837324845)
                    ·
                      rfl

theorem cell23_5895513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_5895513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895513 prefixEnd_5895513 := by exact prefixLift 5895513
  have htrace : WordTrace (prefixWord ++ tailWord_5895513) baseStart_5895513 baseEnd_5895513 := by
    simpa [prefixWord, tailWord_5895513, baseEnd_5895513] using wordTrace_append hprefix tailTrace_5895513
  have hstable : (prefixWord ++ tailWord_5895513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895513).length < 2 ^ (prefixWord ++ tailWord_5895513).sum := by decide
  have hdescent : baseEnd_5895513 < baseStart_5895513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895534 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_5895534 : Nat := 118140960795 + 5895534 * 2 ^ 59
def prefixEnd_5895534 : Nat := 4983230072969 + 3 ^ 40 * 5895534 * 2
def baseEnd_5895534 : Nat := 336360295213782436645771

theorem tailTrace_5895534 : CollatzResearch.WordTrace tailWord_5895534 prefixEnd_5895534 336360295213782436645771 := by
  unfold tailWord_5895534
  simp only [CollatzResearch.WordTrace]
  refine ⟨26878473777936833736341707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143351860148996446593822437 26878473777936833736341707)
  ·
    refine ⟨40317710666905250604512561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26878473777936833736341707 40317710666905250604512561)
    ·
      refine ⟨30238283000178937953384421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40317710666905250604512561 30238283000178937953384421)
      ·
        refine ⟨5669678062533550866259579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30238283000178937953384421 5669678062533550866259579)
        ·
          refine ⟨8504517093800326299389369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669678062533550866259579 8504517093800326299389369)
          ·
            refine ⟨6378387820350244724542027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8504517093800326299389369 6378387820350244724542027)
            ·
              refine ⟨9567581730525367086813041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378387820350244724542027 9567581730525367086813041)
              ·
                refine ⟨7175686297894025315109781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9567581730525367086813041 7175686297894025315109781)
                ·
                  refine ⟨336360295213782436645771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7175686297894025315109781 336360295213782436645771)
                  ·
                    rfl

theorem cell23_5895534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_5895534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895534 prefixEnd_5895534 := by exact prefixLift 5895534
  have htrace : WordTrace (prefixWord ++ tailWord_5895534) baseStart_5895534 baseEnd_5895534 := by
    simpa [prefixWord, tailWord_5895534, baseEnd_5895534] using wordTrace_append hprefix tailTrace_5895534
  have hstable : (prefixWord ++ tailWord_5895534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895534).length < 2 ^ (prefixWord ++ tailWord_5895534).sum := by decide
  have hdescent : baseEnd_5895534 < baseStart_5895534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895554 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5895554 : Nat := 118140960795 + 5895554 * 2 ^ 59
def prefixEnd_5895554 : Nat := 4983230072969 + 3 ^ 40 * 5895554 * 2
def baseEnd_5895554 : Nat := 3027252926537131851561847

theorem tailTrace_5895554 : CollatzResearch.WordTrace tailWord_5895554 prefixEnd_5895554 3027252926537131851561847 := by
  unfold tailWord_5895554
  simp only [CollatzResearch.WordTrace]
  refine ⟨53757129920855553326615429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143352346455614808870974477 53757129920855553326615429)
  ·
    refine ⟨10079461860160416248740393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53757129920855553326615429 10079461860160416248740393)
    ·
      refine ⟨7559596395120312186555295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10079461860160416248740393 7559596395120312186555295)
      ·
        refine ⟨11339394592680468279832943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559596395120312186555295 11339394592680468279832943)
        ·
          refine ⟨17009091889020702419749415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11339394592680468279832943 17009091889020702419749415)
          ·
            refine ⟨25513637833531053629624123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17009091889020702419749415 25513637833531053629624123)
            ·
              refine ⟨38270456750296580444436185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25513637833531053629624123 38270456750296580444436185)
              ·
                refine ⟨28702842562722435333327139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38270456750296580444436185 28702842562722435333327139)
                ·
                  refine ⟨43054263844083652999990709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28702842562722435333327139 43054263844083652999990709)
                  ·
                    refine ⟨4036337235382842468749129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43054263844083652999990709 4036337235382842468749129)
                    ·
                      refine ⟨3027252926537131851561847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036337235382842468749129 3027252926537131851561847)
                      ·
                        rfl

theorem cell23_5895554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5895554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895554 prefixEnd_5895554 := by exact prefixLift 5895554
  have htrace : WordTrace (prefixWord ++ tailWord_5895554) baseStart_5895554 baseEnd_5895554 := by
    simpa [prefixWord, tailWord_5895554, baseEnd_5895554] using wordTrace_append hprefix tailTrace_5895554
  have hstable : (prefixWord ++ tailWord_5895554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895554).length < 2 ^ (prefixWord ++ tailWord_5895554).sum := by decide
  have hdescent : baseEnd_5895554 < baseStart_5895554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895560 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 1, 6]
def baseStart_5895560 : Nat := 118140960795 + 5895560 * 2 ^ 59
def prefixEnd_5895560 : Nat := 4983230072969 + 3 ^ 40 * 5895560 * 2
def baseEnd_5895560 : Nat := 1009085335807019609362273

theorem tailTrace_5895560 : CollatzResearch.WordTrace tailWord_5895560 prefixEnd_5895560 1009085335807019609362273 := by
  unfold tailWord_5895560
  simp only [CollatzResearch.WordTrace]
  refine ⟨107514369260700238165590067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143352492347600317554120089 107514369260700238165590067)
  ·
    refine ⟨161271553891050357248385101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107514369260700238165590067 161271553891050357248385101)
    ·
      refine ⟨60476832709143883968144413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161271553891050357248385101 60476832709143883968144413)
      ·
        refine ⟨22678812265928956488054155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60476832709143883968144413 22678812265928956488054155)
        ·
          refine ⟨34018218398893434732081233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22678812265928956488054155 34018218398893434732081233)
          ·
            refine ⟨25513663799170076049060925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34018218398893434732081233 25513663799170076049060925)
            ·
              refine ⟨9567623924688778518397847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25513663799170076049060925 9567623924688778518397847)
              ·
                refine ⟨14351435887033167777596771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9567623924688778518397847 14351435887033167777596771)
                ·
                  refine ⟨21527153830549751666395157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14351435887033167777596771 21527153830549751666395157)
                  ·
                    refine ⟨1009085335807019609362273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21527153830549751666395157 1009085335807019609362273)
                    ·
                      rfl

theorem cell23_5895560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_5895560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895560 prefixEnd_5895560 := by exact prefixLift 5895560
  have htrace : WordTrace (prefixWord ++ tailWord_5895560) baseStart_5895560 baseEnd_5895560 := by
    simpa [prefixWord, tailWord_5895560, baseEnd_5895560] using wordTrace_append hprefix tailTrace_5895560
  have hstable : (prefixWord ++ tailWord_5895560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895560).length < 2 ^ (prefixWord ++ tailWord_5895560).sum := by decide
  have hdescent : baseEnd_5895560 < baseStart_5895560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895563 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6]
def baseStart_5895563 : Nat := 118140960795 + 5895563 * 2 ^ 59
def prefixEnd_5895563 : Nat := 4983230072969 + 3 ^ 40 * 5895563 * 2
def baseEnd_5895563 : Nat := 3027257547863022316349305

theorem tailTrace_5895563 : CollatzResearch.WordTrace tailWord_5895563 prefixEnd_5895563 3027257547863022316349305 := by
  unfold tailWord_5895563
  simp only [CollatzResearch.WordTrace]
  refine ⟨215028847940389607843539343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143352565293593071895692895 215028847940389607843539343)
  ·
    refine ⟨322543271910584411765309015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215028847940389607843539343 322543271910584411765309015)
    ·
      refine ⟨483814907865876617647963523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322543271910584411765309015 483814907865876617647963523)
      ·
        refine ⟨725722361798814926471945285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483814907865876617647963523 725722361798814926471945285)
        ·
          refine ⟨136072942837277798713489741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 725722361798814926471945285 136072942837277798713489741)
          ·
            refine ⟨51027353563979174517558653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136072942837277798713489741 51027353563979174517558653)
            ·
              refine ⟨19135257586492190444084495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51027353563979174517558653 19135257586492190444084495)
              ·
                refine ⟨28702886379738285666126743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19135257586492190444084495 28702886379738285666126743)
                ·
                  refine ⟨43054329569607428499190115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28702886379738285666126743 43054329569607428499190115)
                  ·
                    refine ⟨64581494354411142748785173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43054329569607428499190115 64581494354411142748785173)
                    ·
                      refine ⟨3027257547863022316349305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64581494354411142748785173 3027257547863022316349305)
                      ·
                        rfl

theorem cell23_5895563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_5895563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895563 prefixEnd_5895563 := by exact prefixLift 5895563
  have htrace : WordTrace (prefixWord ++ tailWord_5895563) baseStart_5895563 baseEnd_5895563 := by
    simpa [prefixWord, tailWord_5895563, baseEnd_5895563] using wordTrace_append hprefix tailTrace_5895563
  have hstable : (prefixWord ++ tailWord_5895563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895563).length < 2 ^ (prefixWord ++ tailWord_5895563).sum := by decide
  have hdescent : baseEnd_5895563 < baseStart_5895563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895610 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2]
def baseStart_5895610 : Nat := 118140960795 + 5895610 * 2 ^ 59
def prefixEnd_5895610 : Nat := 4983230072969 + 3 ^ 40 * 5895610 * 2
def baseEnd_5895610 : Nat := 3027281681453783632461589

theorem tailTrace_5895610 : CollatzResearch.WordTrace tailWord_5895610 prefixEnd_5895610 3027281681453783632461589 := by
  unfold tailWord_5895610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53757640542804833717625071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143353708114146223247000189 53757640542804833717625071)
  ·
    refine ⟨80636460814207250576437607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53757640542804833717625071 80636460814207250576437607)
    ·
      refine ⟨120954691221310875864656411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80636460814207250576437607 120954691221310875864656411)
      ·
        refine ⟨181432036831966313796984617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120954691221310875864656411 181432036831966313796984617)
        ·
          refine ⟨136074027623974735347738463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181432036831966313796984617 136074027623974735347738463)
          ·
            refine ⟨204111041435962103021607695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136074027623974735347738463 204111041435962103021607695)
            ·
              refine ⟨306166562153943154532411543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204111041435962103021607695 306166562153943154532411543)
              ·
                refine ⟨459249843230914731798617315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306166562153943154532411543 459249843230914731798617315)
                ·
                  refine ⟨688874764846372097697925973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459249843230914731798617315 688874764846372097697925973)
                  ·
                    refine ⟨4036375575271711509948785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 688874764846372097697925973 4036375575271711509948785)
                    ·
                      refine ⟨3027281681453783632461589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036375575271711509948785 3027281681453783632461589)
                      ·
                        rfl

theorem cell23_5895610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_5895610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895610 prefixEnd_5895610 := by exact prefixLift 5895610
  have htrace : WordTrace (prefixWord ++ tailWord_5895610) baseStart_5895610 baseEnd_5895610 := by
    simpa [prefixWord, tailWord_5895610, baseEnd_5895610] using wordTrace_append hprefix tailTrace_5895610
  have hstable : (prefixWord ++ tailWord_5895610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895610).length < 2 ^ (prefixWord ++ tailWord_5895610).sum := by decide
  have hdescent : baseEnd_5895610 < baseStart_5895610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895618 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5895618 : Nat := 118140960795 + 5895618 * 2 ^ 59
def prefixEnd_5895618 : Nat := 4983230072969 + 3 ^ 40 * 5895618 * 2
def baseEnd_5895618 : Nat := 3027285789299019601161553

theorem tailTrace_5895618 : CollatzResearch.WordTrace tailWord_5895618 prefixEnd_5895618 3027285789299019601161553 := by
  unfold tailWord_5895618
  simp only [CollatzResearch.WordTrace]
  refine ⟨53757713488797588059197877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143353902636793568157861005 53757713488797588059197877)
  ·
    refine ⟨5039785639574773880549801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53757713488797588059197877 5039785639574773880549801)
    ·
      refine ⟨3779839229681080410412351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5039785639574773880549801 3779839229681080410412351)
      ·
        refine ⟨5669758844521620615618527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779839229681080410412351 5669758844521620615618527)
        ·
          refine ⟨8504638266782430923427791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669758844521620615618527 8504638266782430923427791)
          ·
            refine ⟨12756957400173646385141687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8504638266782430923427791 12756957400173646385141687)
            ·
              refine ⟨19135436100260469577712531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756957400173646385141687 19135436100260469577712531)
              ·
                refine ⟨28703154150390704366568797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19135436100260469577712531 28703154150390704366568797)
                ·
                  refine ⟨10763682806396514137463299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28703154150390704366568797 10763682806396514137463299)
                  ·
                    refine ⟨16145524209594771206194949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10763682806396514137463299 16145524209594771206194949)
                    ·
                      refine ⟨3027285789299019601161553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16145524209594771206194949 3027285789299019601161553)
                      ·
                        rfl

theorem cell23_5895618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5895618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895618 prefixEnd_5895618 := by exact prefixLift 5895618
  have htrace : WordTrace (prefixWord ++ tailWord_5895618) baseStart_5895618 baseEnd_5895618 := by
    simpa [prefixWord, tailWord_5895618, baseEnd_5895618] using wordTrace_append hprefix tailTrace_5895618
  have hstable : (prefixWord ++ tailWord_5895618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895618).length < 2 ^ (prefixWord ++ tailWord_5895618).sum := by decide
  have hdescent : baseEnd_5895618 < baseStart_5895618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895633 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_5895633 : Nat := 118140960795 + 5895633 * 2 ^ 59
def prefixEnd_5895633 : Nat := 4983230072969 + 3 ^ 40 * 5895633 * 2
def baseEnd_5895633 : Nat := 1009097830502945680824661

theorem tailTrace_5895633 : CollatzResearch.WordTrace tailWord_5895633 prefixEnd_5895633 1009097830502945680824661 := by
  unfold tailWord_5895633
  simp only [CollatzResearch.WordTrace]
  refine ⟨215031401050136009798587553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143354267366757339865725035 215031401050136009798587553)
  ·
    refine ⟨161273550787602007348940665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215031401050136009798587553 161273550787602007348940665)
    ·
      refine ⟨120955163090701505511705499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161273550787602007348940665 120955163090701505511705499)
      ·
        refine ⟨181432744636052258267558249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120955163090701505511705499 181432744636052258267558249)
        ·
          refine ⟨136074558477039193700668687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181432744636052258267558249 136074558477039193700668687)
          ·
            refine ⟨204111837715558790551003031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136074558477039193700668687 204111837715558790551003031)
            ·
              refine ⟨306167756573338185826504547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204111837715558790551003031 306167756573338185826504547)
              ·
                refine ⟨459251634860007278739756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306167756573338185826504547 459251634860007278739756821)
                ·
                  refine ⟨21527420384062841190926101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 459251634860007278739756821 21527420384062841190926101)
                  ·
                    refine ⟨1009097830502945680824661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21527420384062841190926101 1009097830502945680824661)
                    ·
                      rfl

theorem cell23_5895633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_5895633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895633 prefixEnd_5895633 := by exact prefixLift 5895633
  have htrace : WordTrace (prefixWord ++ tailWord_5895633) baseStart_5895633 baseEnd_5895633 := by
    simpa [prefixWord, tailWord_5895633, baseEnd_5895633] using wordTrace_append hprefix tailTrace_5895633
  have hstable : (prefixWord ++ tailWord_5895633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895633).length < 2 ^ (prefixWord ++ tailWord_5895633).sum := by decide
  have hdescent : baseEnd_5895633 < baseStart_5895633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895657 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 8, 2, 2]
def baseStart_5895657 : Nat := 118140960795 + 5895657 * 2 ^ 59
def prefixEnd_5895657 : Nat := 4983230072969 + 3 ^ 40 * 5895657 * 2
def baseEnd_5895657 : Nat := 3027305815044544948573873

theorem tailTrace_5895657 : CollatzResearch.WordTrace tailWord_5895657 prefixEnd_5895657 3027305815044544948573873 := by
  unfold tailWord_5895657
  simp only [CollatzResearch.WordTrace]
  refine ⟨215032276402049061897461225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143354850934699374598307483 215032276402049061897461225)
  ·
    refine ⟨161274207301536796423095919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215032276402049061897461225 161274207301536796423095919)
    ·
      refine ⟨241911310952305194634643879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161274207301536796423095919 241911310952305194634643879)
      ·
        refine ⟨362866966428457791951965819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241911310952305194634643879 362866966428457791951965819)
        ·
          refine ⟨544300449642686687927948729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362866966428457791951965819 544300449642686687927948729)
          ·
            refine ⟨408225337232015015945961547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544300449642686687927948729 408225337232015015945961547)
            ·
              refine ⟨612338005848022523918942321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408225337232015015945961547 612338005848022523918942321)
              ·
                refine ⟨459253504386016892939206741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612338005848022523918942321 459253504386016892939206741)
                ·
                  refine ⟨5381877004523635464131329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 459253504386016892939206741 5381877004523635464131329)
                  ·
                    refine ⟨4036407753392726598098497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5381877004523635464131329 4036407753392726598098497)
                    ·
                      refine ⟨3027305815044544948573873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036407753392726598098497 3027305815044544948573873)
                      ·
                        rfl

theorem cell23_5895657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 2, 2].length) (baseStart_5895657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895657 prefixEnd_5895657 := by exact prefixLift 5895657
  have htrace : WordTrace (prefixWord ++ tailWord_5895657) baseStart_5895657 baseEnd_5895657 := by
    simpa [prefixWord, tailWord_5895657, baseEnd_5895657] using wordTrace_append hprefix tailTrace_5895657
  have hstable : (prefixWord ++ tailWord_5895657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895657).length < 2 ^ (prefixWord ++ tailWord_5895657).sum := by decide
  have hdescent : baseEnd_5895657 < baseStart_5895657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895674 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2]
def baseStart_5895674 : Nat := 118140960795 + 5895674 * 2 ^ 59
def prefixEnd_5895674 : Nat := 4983230072969 + 3 ^ 40 * 5895674 * 2
def baseEnd_5895674 : Nat := 3027314544215671382061295

theorem tailTrace_5895674 : CollatzResearch.WordTrace tailWord_5895674 prefixEnd_5895674 3027314544215671382061295 := by
  unfold tailWord_5895674
  simp only [CollatzResearch.WordTrace]
  refine ⟨53758224110746868450207519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143355264295324982533886717 53758224110746868450207519)
  ·
    refine ⟨80637336166120302675311279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53758224110746868450207519 80637336166120302675311279)
    ·
      refine ⟨120956004249180454012966919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80637336166120302675311279 120956004249180454012966919)
      ·
        refine ⟨181434006373770681019450379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120956004249180454012966919 181434006373770681019450379)
        ·
          refine ⟨272151009560656021529175569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181434006373770681019450379 272151009560656021529175569)
          ·
            refine ⟨204113257170492016146881677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272151009560656021529175569 204113257170492016146881677)
            ·
              refine ⟨76542471438934506055080629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204113257170492016146881677 76542471438934506055080629)
              ·
                refine ⟨7175856697400109942663809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76542471438934506055080629 7175856697400109942663809)
                ·
                  refine ⟨5381892523050082456997857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7175856697400109942663809 5381892523050082456997857)
                  ·
                    refine ⟨4036419392287561842748393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5381892523050082456997857 4036419392287561842748393)
                    ·
                      refine ⟨3027314544215671382061295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036419392287561842748393 3027314544215671382061295)
                      ·
                        rfl

theorem cell23_5895674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_5895674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895674 prefixEnd_5895674 := by exact prefixLift 5895674
  have htrace : WordTrace (prefixWord ++ tailWord_5895674) baseStart_5895674 baseEnd_5895674 := by
    simpa [prefixWord, tailWord_5895674, baseEnd_5895674] using wordTrace_append hprefix tailTrace_5895674
  have hstable : (prefixWord ++ tailWord_5895674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895674).length < 2 ^ (prefixWord ++ tailWord_5895674).sum := by decide
  have hdescent : baseEnd_5895674 < baseStart_5895674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895697 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 5]
def baseStart_5895697 : Nat := 118140960795 + 5895697 * 2 ^ 59
def prefixEnd_5895697 : Nat := 4983230072969 + 3 ^ 40 * 5895697 * 2
def baseEnd_5895697 : Nat := 336369594918969421341521

theorem tailTrace_5895697 : CollatzResearch.WordTrace tailWord_5895697 prefixEnd_5895697 336369594918969421341521 := by
  unfold tailWord_5895697
  simp only [CollatzResearch.WordTrace]
  refine ⟨215033735321904148728917345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143355823547936099152611563 215033735321904148728917345)
  ·
    refine ⟨161275301491428111546688009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215033735321904148728917345 161275301491428111546688009)
    ·
      refine ⟨120956476118571083660016007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161275301491428111546688009 120956476118571083660016007)
      ·
        refine ⟨181434714177856625490024011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120956476118571083660016007 181434714177856625490024011)
        ·
          refine ⟨272152071266784938235036017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181434714177856625490024011 272152071266784938235036017)
          ·
            refine ⟨204114053450088703676277013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272152071266784938235036017 204114053450088703676277013)
            ·
              refine ⟨9567846255472907984825485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204114053450088703676277013 9567846255472907984825485)
              ·
                refine ⟨3587942345802340494309557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9567846255472907984825485 3587942345802340494309557)
                ·
                  refine ⟨336369594918969421341521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3587942345802340494309557 336369594918969421341521)
                  ·
                    rfl

theorem cell23_5895697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 5].length) (baseStart_5895697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895697 prefixEnd_5895697 := by exact prefixLift 5895697
  have htrace : WordTrace (prefixWord ++ tailWord_5895697) baseStart_5895697 baseEnd_5895697 := by
    simpa [prefixWord, tailWord_5895697, baseEnd_5895697] using wordTrace_append hprefix tailTrace_5895697
  have hstable : (prefixWord ++ tailWord_5895697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895697).length < 2 ^ (prefixWord ++ tailWord_5895697).sum := by decide
  have hdescent : baseEnd_5895697 < baseStart_5895697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895767 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_5895767 : Nat := 118140960795 + 5895767 * 2 ^ 59
def prefixEnd_5895767 : Nat := 4983230072969 + 3 ^ 40 * 5895767 * 2
def baseEnd_5895767 : Nat := 3027362297916539518198367

theorem tailTrace_5895767 : CollatzResearch.WordTrace tailWord_5895767 prefixEnd_5895767 3027362297916539518198367 := by
  unfold tailWord_5895767
  simp only [CollatzResearch.WordTrace]
  refine ⟨215036288431650550683965555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143357525621100367122643703 215036288431650550683965555)
  ·
    refine ⟨322554432647475826025948333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215036288431650550683965555 322554432647475826025948333)
    ·
      refine ⟨120957912242803434759730625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322554432647475826025948333 120957912242803434759730625)
      ·
        refine ⟨90718434182102576069797969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120957912242803434759730625 90718434182102576069797969)
        ·
          refine ⟨68038825636576932052348477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90718434182102576069797969 68038825636576932052348477)
          ·
            refine ⟨25514559613716349519630679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68038825636576932052348477 25514559613716349519630679)
            ·
              refine ⟨38271839420574524279446019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25514559613716349519630679 38271839420574524279446019)
              ·
                refine ⟨57407759130861786419169029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38271839420574524279446019 57407759130861786419169029)
                ·
                  refine ⟨10763954837036584953594193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57407759130861786419169029 10763954837036584953594193)
                  ·
                    refine ⟨8072966127777438715195645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10763954837036584953594193 8072966127777438715195645)
                    ·
                      refine ⟨3027362297916539518198367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8072966127777438715195645 3027362297916539518198367)
                      ·
                        rfl

theorem cell23_5895767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_5895767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895767 prefixEnd_5895767 := by exact prefixLift 5895767
  have htrace : WordTrace (prefixWord ++ tailWord_5895767) baseStart_5895767 baseEnd_5895767 := by
    simpa [prefixWord, tailWord_5895767, baseEnd_5895767] using wordTrace_append hprefix tailTrace_5895767
  have hstable : (prefixWord ++ tailWord_5895767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895767).length < 2 ^ (prefixWord ++ tailWord_5895767).sum := by decide
  have hdescent : baseEnd_5895767 < baseStart_5895767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895807 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 5, 5, 2]
def baseStart_5895807 : Nat := 118140960795 + 5895807 * 2 ^ 59
def prefixEnd_5895807 : Nat := 4983230072969 + 3 ^ 40 * 5895807 * 2
def baseEnd_5895807 : Nat := 3027382837142719361698183

theorem tailTrace_5895807 : CollatzResearch.WordTrace tailWord_5895807 prefixEnd_5895807 3027382837142719361698183 := by
  unfold tailWord_5895807
  simp only [CollatzResearch.WordTrace]
  refine ⟨215037747351505637515421675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143358498234337091676947783 215037747351505637515421675)
  ·
    refine ⟨322556621027258456273132513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215037747351505637515421675 322556621027258456273132513)
    ·
      refine ⟨241917465770443842204849385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322556621027258456273132513 241917465770443842204849385)
      ·
        refine ⟨181438099327832881653637039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241917465770443842204849385 181438099327832881653637039)
        ·
          refine ⟨272157148991749322480455559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181438099327832881653637039 272157148991749322480455559)
          ·
            refine ⟨408235723487623983720683339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272157148991749322480455559 408235723487623983720683339)
            ·
              refine ⟨612353585231435975581025009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408235723487623983720683339 612353585231435975581025009)
              ·
                refine ⟨459265188923576981685768757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612353585231435975581025009 459265188923576981685768757)
                ·
                  refine ⟨43056111461585342033040821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459265188923576981685768757 43056111461585342033040821)
                  ·
                    refine ⟨4036510449523625815597577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43056111461585342033040821 4036510449523625815597577)
                    ·
                      refine ⟨3027382837142719361698183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036510449523625815597577 3027382837142719361698183)
                      ·
                        rfl

theorem cell23_5895807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_5895807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895807 prefixEnd_5895807 := by exact prefixLift 5895807
  have htrace : WordTrace (prefixWord ++ tailWord_5895807) baseStart_5895807 baseEnd_5895807 := by
    simpa [prefixWord, tailWord_5895807, baseEnd_5895807] using wordTrace_append hprefix tailTrace_5895807
  have hstable : (prefixWord ++ tailWord_5895807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895807).length < 2 ^ (prefixWord ++ tailWord_5895807).sum := by decide
  have hdescent : baseEnd_5895807 < baseStart_5895807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895817 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 1, 5]
def baseStart_5895817 : Nat := 118140960795 + 5895817 * 2 ^ 59
def prefixEnd_5895817 : Nat := 4983230072969 + 3 ^ 40 * 5895817 * 2
def baseEnd_5895817 : Nat := 1009129323983088107524379

theorem tailTrace_5895817 : CollatzResearch.WordTrace tailWord_5895817 prefixEnd_5895817 1009129323983088107524379 := by
  unfold tailWord_5895817
  simp only [CollatzResearch.WordTrace]
  refine ⟨215038112081469409223285705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143358741387646272815523803 215038112081469409223285705)
  ·
    refine ⟨161278584061102056917464279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215038112081469409223285705 161278584061102056917464279)
    ·
      refine ⟨241917876091653085376196419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161278584061102056917464279 241917876091653085376196419)
      ·
        refine ⟨362876814137479628064294629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241917876091653085376196419 362876814137479628064294629)
        ·
          refine ⟨68039402650777430262055243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362876814137479628064294629 68039402650777430262055243)
          ·
            refine ⟨102059103976166145393082865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68039402650777430262055243 102059103976166145393082865)
            ·
              refine ⟨76544327982124609044812149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102059103976166145393082865 76544327982124609044812149)
              ·
                refine ⟨7176030748324182097951139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76544327982124609044812149 7176030748324182097951139)
                ·
                  refine ⟨10764046122486273146926709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7176030748324182097951139 10764046122486273146926709)
                  ·
                    refine ⟨1009129323983088107524379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10764046122486273146926709 1009129323983088107524379)
                    ·
                      rfl

theorem cell23_5895817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_5895817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895817 prefixEnd_5895817 := by exact prefixLift 5895817
  have htrace : WordTrace (prefixWord ++ tailWord_5895817) baseStart_5895817 baseEnd_5895817 := by
    simpa [prefixWord, tailWord_5895817, baseEnd_5895817] using wordTrace_append hprefix tailTrace_5895817
  have hstable : (prefixWord ++ tailWord_5895817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895817).length < 2 ^ (prefixWord ++ tailWord_5895817).sum := by decide
  have hdescent : baseEnd_5895817 < baseStart_5895817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895887 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_5895887 : Nat := 118140960795 + 5895887 * 2 ^ 59
def prefixEnd_5895887 : Nat := 4983230072969 + 3 ^ 40 * 5895887 * 2
def baseEnd_5895887 : Nat := 3027423915595079048697815

theorem tailTrace_5895887 : CollatzResearch.WordTrace tailWord_5895887 prefixEnd_5895887 3027423915595079048697815 := by
  unfold tailWord_5895887
  simp only [CollatzResearch.WordTrace]
  refine ⟨215040665191215811178333915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143360443460810540785555943 215040665191215811178333915)
  ·
    refine ⟨322560997786823716767500873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215040665191215811178333915 322560997786823716767500873)
    ·
      refine ⟨241920748340117787575625655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322560997786823716767500873 241920748340117787575625655)
      ·
        refine ⟨362881122510176681363438483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241920748340117787575625655 362881122510176681363438483)
        ·
          refine ⟨544321683765265022045157725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362881122510176681363438483 544321683765265022045157725)
          ·
            refine ⟨204120631411974383266934147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 544321683765265022045157725 204120631411974383266934147)
            ·
              refine ⟨306180947117961574900401221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204120631411974383266934147 306180947117961574900401221)
              ·
                refine ⟨57408927584617795293825229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306180947117961574900401221 57408927584617795293825229)
                ·
                  refine ⟨21528347844231673235184461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57408927584617795293825229 21528347844231673235184461)
                  ·
                    refine ⟨8073130441586877463194173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21528347844231673235184461 8073130441586877463194173)
                    ·
                      refine ⟨3027423915595079048697815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073130441586877463194173 3027423915595079048697815)
                      ·
                        rfl

theorem cell23_5895887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_5895887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895887 prefixEnd_5895887 := by exact prefixLift 5895887
  have htrace : WordTrace (prefixWord ++ tailWord_5895887) baseStart_5895887 baseEnd_5895887 := by
    simpa [prefixWord, tailWord_5895887, baseEnd_5895887] using wordTrace_append hprefix tailTrace_5895887
  have hstable : (prefixWord ++ tailWord_5895887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895887).length < 2 ^ (prefixWord ++ tailWord_5895887).sum := by decide
  have hdescent : baseEnd_5895887 < baseStart_5895887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895901 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5895901 : Nat := 118140960795 + 5895901 * 2 ^ 59
def prefixEnd_5895901 : Nat := 4983230072969 + 3 ^ 40 * 5895901 * 2
def baseEnd_5895901 : Nat := 3027431104324241993922751

theorem tailTrace_5895901 : CollatzResearch.WordTrace tailWord_5895901 prefixEnd_5895901 3027431104324241993922751 := by
  unfold tailWord_5895901
  simp only [CollatzResearch.WordTrace]
  refine ⟨215041175813165091569343557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143360783875443394379562371 215041175813165091569343557)
  ·
    refine ⟨40320220464968454669251917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215041175813165091569343557 40320220464968454669251917)
    ·
      refine ⟨15120082674363170500969469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40320220464968454669251917 15120082674363170500969469)
      ·
        refine ⟨5670031002886188937863551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15120082674363170500969469 5670031002886188937863551)
        ·
          refine ⟨8505046504329283406795327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670031002886188937863551 8505046504329283406795327)
          ·
            refine ⟨12757569756493925110192991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505046504329283406795327 12757569756493925110192991)
            ·
              refine ⟨19136354634740887665289487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12757569756493925110192991 19136354634740887665289487)
              ·
                refine ⟨28704531952111331497934231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19136354634740887665289487 28704531952111331497934231)
                ·
                  refine ⟨43056797928166997246901347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28704531952111331497934231 43056797928166997246901347)
                  ·
                    refine ⟨64585196892250495870352021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43056797928166997246901347 64585196892250495870352021)
                    ·
                      refine ⟨3027431104324241993922751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64585196892250495870352021 3027431104324241993922751)
                      ·
                        rfl

theorem cell23_5895901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5895901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895901 prefixEnd_5895901 := by exact prefixLift 5895901
  have htrace : WordTrace (prefixWord ++ tailWord_5895901) baseStart_5895901 baseEnd_5895901 := by
    simpa [prefixWord, tailWord_5895901, baseEnd_5895901] using wordTrace_append hprefix tailTrace_5895901
  have hstable : (prefixWord ++ tailWord_5895901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895901).length < 2 ^ (prefixWord ++ tailWord_5895901).sum := by decide
  have hdescent : baseEnd_5895901 < baseStart_5895901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895904 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_5895904 : Nat := 118140960795 + 5895904 * 2 ^ 59
def prefixEnd_5895904 : Nat := 4983230072969 + 3 ^ 40 * 5895904 * 2
def baseEnd_5895904 : Nat := 3027432644766205482185237

theorem tailTrace_5895904 : CollatzResearch.WordTrace tailWord_5895904 prefixEnd_5895904 3027432644766205482185237 := by
  unfold tailWord_5895904
  simp only [CollatzResearch.WordTrace]
  refine ⟨107520642616077111540851383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143360856821436148721135177 107520642616077111540851383)
  ·
    refine ⟨161280963924115667311277075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107520642616077111540851383 161280963924115667311277075)
    ·
      refine ⟨241921445886173500966915613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161280963924115667311277075 241921445886173500966915613)
      ·
        refine ⟨90720542207315062862593355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241921445886173500966915613 90720542207315062862593355)
        ·
          refine ⟨136080813310972594293890033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90720542207315062862593355 136080813310972594293890033)
          ·
            refine ⟨102060609983229445720417525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136080813310972594293890033 102060609983229445720417525)
            ·
              refine ⟨9568182185927760536289143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102060609983229445720417525 9568182185927760536289143)
              ·
                refine ⟨14352273278891640804433715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568182185927760536289143 14352273278891640804433715)
                ·
                  refine ⟨21528409918337461206650573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14352273278891640804433715 21528409918337461206650573)
                  ·
                    refine ⟨8073153719376547952493965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21528409918337461206650573 8073153719376547952493965)
                    ·
                      refine ⟨3027432644766205482185237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073153719376547952493965 3027432644766205482185237)
                      ·
                        rfl

theorem cell23_5895904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_5895904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895904 prefixEnd_5895904 := by exact prefixLift 5895904
  have htrace : WordTrace (prefixWord ++ tailWord_5895904) baseStart_5895904 baseEnd_5895904 := by
    simpa [prefixWord, tailWord_5895904, baseEnd_5895904] using wordTrace_append hprefix tailTrace_5895904
  have hstable : (prefixWord ++ tailWord_5895904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895904).length < 2 ^ (prefixWord ++ tailWord_5895904).sum := by decide
  have hdescent : baseEnd_5895904 < baseStart_5895904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895937 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_5895937 : Nat := 118140960795 + 5895937 * 2 ^ 59
def prefixEnd_5895937 : Nat := 4983230072969 + 3 ^ 40 * 5895937 * 2
def baseEnd_5895937 : Nat := 1009149863209267951024195

theorem tailTrace_5895937 : CollatzResearch.WordTrace tailWord_5895937 prefixEnd_5895937 1009149863209267951024195 := by
  unfold tailWord_5895937
  simp only [CollatzResearch.WordTrace]
  refine ⟨215042488841034669717654065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143361659227356446478436043 215042488841034669717654065)
  ·
    refine ⟨161281866630776002288240549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215042488841034669717654065 161281866630776002288240549)
    ·
      refine ⟨30240349993270500429045103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161281866630776002288240549 30240349993270500429045103)
      ·
        refine ⟨45360524989905750643567655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30240349993270500429045103 45360524989905750643567655)
        ·
          refine ⟨68040787484858625965351483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45360524989905750643567655 68040787484858625965351483)
          ·
            refine ⟨102061181227287938948027225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68040787484858625965351483 102061181227287938948027225)
            ·
              refine ⟨76545885920465954211020419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102061181227287938948027225 76545885920465954211020419)
              ·
                refine ⟨114818828880698931316530629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76545885920465954211020419 114818828880698931316530629)
                ·
                  refine ⟨21528530415131049621849493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114818828880698931316530629 21528530415131049621849493)
                  ·
                    refine ⟨1009149863209267951024195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21528530415131049621849493 1009149863209267951024195)
                    ·
                      rfl

theorem cell23_5895937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_5895937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895937 prefixEnd_5895937 := by exact prefixLift 5895937
  have htrace : WordTrace (prefixWord ++ tailWord_5895937) baseStart_5895937 baseEnd_5895937 := by
    simpa [prefixWord, tailWord_5895937, baseEnd_5895937] using wordTrace_append hprefix tailTrace_5895937
  have hstable : (prefixWord ++ tailWord_5895937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895937).length < 2 ^ (prefixWord ++ tailWord_5895937).sum := by decide
  have hdescent : baseEnd_5895937 < baseStart_5895937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895938 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_5895938 : Nat := 118140960795 + 5895938 * 2 ^ 59
def prefixEnd_5895938 : Nat := 4983230072969 + 3 ^ 40 * 5895938 * 2
def baseEnd_5895938 : Nat := 3027450103108458349160081

theorem tailTrace_5895938 : CollatzResearch.WordTrace tailWord_5895938 prefixEnd_5895938 3027450103108458349160081 := by
  unfold tailWord_5895938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53760631328507761722110117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143361683542687364592293645 53760631328507761722110117)
  ·
    refine ⟨10080118374095205322895647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53760631328507761722110117 10080118374095205322895647)
    ·
      refine ⟨15120177561142807984343471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10080118374095205322895647 15120177561142807984343471)
      ·
        refine ⟨22680266341714211976515207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15120177561142807984343471 22680266341714211976515207)
        ·
          refine ⟨34020399512571317964772811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22680266341714211976515207 34020399512571317964772811)
          ·
            refine ⟨51030599268856976947159217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34020399512571317964772811 51030599268856976947159217)
            ·
              refine ⟨38272949451642732710369413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51030599268856976947159217 38272949451642732710369413)
              ·
                refine ⟨7176178022183012383194265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38272949451642732710369413 7176178022183012383194265)
                ·
                  refine ⟨5382133516637259287395699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7176178022183012383194265 5382133516637259287395699)
                  ·
                    refine ⟨8073200274955888931093549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5382133516637259287395699 8073200274955888931093549)
                    ·
                      refine ⟨3027450103108458349160081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073200274955888931093549 3027450103108458349160081)
                      ·
                        rfl

theorem cell23_5895938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_5895938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895938 prefixEnd_5895938 := by exact prefixLift 5895938
  have htrace : WordTrace (prefixWord ++ tailWord_5895938) baseStart_5895938 baseEnd_5895938 := by
    simpa [prefixWord, tailWord_5895938, baseEnd_5895938] using wordTrace_append hprefix tailTrace_5895938
  have hstable : (prefixWord ++ tailWord_5895938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895938).length < 2 ^ (prefixWord ++ tailWord_5895938).sum := by decide
  have hdescent : baseEnd_5895938 < baseStart_5895938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895967 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 9]
def baseStart_5895967 : Nat := 118140960795 + 5895967 * 2 ^ 59
def prefixEnd_5895967 : Nat := 4983230072969 + 3 ^ 40 * 5895967 * 2
def baseEnd_5895967 : Nat := 336384999338604303966383

theorem tailTrace_5895967 : CollatzResearch.WordTrace tailWord_5895967 prefixEnd_5895967 336384999338604303966383 := by
  unfold tailWord_5895967
  simp only [CollatzResearch.WordTrace]
  refine ⟨215043583030925984841246155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143362388687283989894164103 215043583030925984841246155)
  ·
    refine ⟨322565374546388977261869233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215043583030925984841246155 322565374546388977261869233)
    ·
      refine ⟨241924030909791732946401925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322565374546388977261869233 241924030909791732946401925)
      ·
        refine ⟨45360755795585949927450361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241924030909791732946401925 45360755795585949927450361)
        ·
          refine ⟨34020566846689462445587771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45360755795585949927450361 34020566846689462445587771)
          ·
            refine ⟨51030850270034193668381657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34020566846689462445587771 51030850270034193668381657)
            ·
              refine ⟨38273137702525645251286243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51030850270034193668381657 38273137702525645251286243)
              ·
                refine ⟨57409706553788467876929365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38273137702525645251286243 57409706553788467876929365)
                ·
                  refine ⟨336384999338604303966383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57409706553788467876929365 336384999338604303966383)
                  ·
                    rfl

theorem cell23_5895967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 9].length) (baseStart_5895967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895967 prefixEnd_5895967 := by exact prefixLift 5895967
  have htrace : WordTrace (prefixWord ++ tailWord_5895967) baseStart_5895967 baseEnd_5895967 := by
    simpa [prefixWord, tailWord_5895967, baseEnd_5895967] using wordTrace_append hprefix tailTrace_5895967
  have hstable : (prefixWord ++ tailWord_5895967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895967).length < 2 ^ (prefixWord ++ tailWord_5895967).sum := by decide
  have hdescent : baseEnd_5895967 < baseStart_5895967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895982 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5895982 : Nat := 118140960795 + 5895982 * 2 ^ 59
def prefixEnd_5895982 : Nat := 4983230072969 + 3 ^ 40 * 5895982 * 2
def baseEnd_5895982 : Nat := 3027472696257256177009879

theorem tailTrace_5895982 : CollatzResearch.WordTrace tailWord_5895982 prefixEnd_5895982 3027472696257256177009879 := by
  unfold tailWord_5895982
  simp only [CollatzResearch.WordTrace]
  refine ⟨26880516265733955300380275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143362753417247761602028133 26880516265733955300380275)
  ·
    refine ⟨40320774398600932950570413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26880516265733955300380275 40320774398600932950570413)
    ·
      refine ⟨15120290399475349856463905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40320774398600932950570413 15120290399475349856463905)
      ·
        refine ⟨11340217799606512392347929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15120290399475349856463905 11340217799606512392347929)
        ·
          refine ⟨8505163349704884294260947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11340217799606512392347929 8505163349704884294260947)
          ·
            refine ⟨12757745024557326441391421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505163349704884294260947 12757745024557326441391421)
            ·
              refine ⟨4784154384208997415521783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12757745024557326441391421 4784154384208997415521783)
              ·
                refine ⟨7176231576313496123282675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784154384208997415521783 7176231576313496123282675)
                ·
                  refine ⟨10764347364470244184924013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7176231576313496123282675 10764347364470244184924013)
                  ·
                    refine ⟨4036630261676341569346505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10764347364470244184924013 4036630261676341569346505)
                    ·
                      refine ⟨3027472696257256177009879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036630261676341569346505 3027472696257256177009879)
                      ·
                        rfl

theorem cell23_5895982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5895982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5895982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5895982 prefixEnd_5895982 := by exact prefixLift 5895982
  have htrace : WordTrace (prefixWord ++ tailWord_5895982) baseStart_5895982 baseEnd_5895982 := by
    simpa [prefixWord, tailWord_5895982, baseEnd_5895982] using wordTrace_append hprefix tailTrace_5895982
  have hstable : (prefixWord ++ tailWord_5895982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895982).length < 2 ^ (prefixWord ++ tailWord_5895982).sum := by decide
  have hdescent : baseEnd_5895982 < baseStart_5895982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896031 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 2, 5]
def baseStart_5896031 : Nat := 118140960795 + 5896031 * 2 ^ 59
def prefixEnd_5896031 : Nat := 4983230072969 + 3 ^ 40 * 5896031 * 2
def baseEnd_5896031 : Nat := 1009165952269775495099051

theorem tailTrace_5896031 : CollatzResearch.WordTrace tailWord_5896031 prefixEnd_5896031 1009165952269775495099051 := by
  unfold tailWord_5896031
  simp only [CollatzResearch.WordTrace]
  refine ⟨215045917302694123771575947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143363944868462749181050631 215045917302694123771575947)
  ·
    refine ⟨322568875954041185657363921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215045917302694123771575947 322568875954041185657363921)
    ·
      refine ⟨241926656965530889243022941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322568875954041185657363921 241926656965530889243022941)
      ·
        refine ⟨90722496362074083466133603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241926656965530889243022941 90722496362074083466133603)
        ·
          refine ⟨136083744543111125199200405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90722496362074083466133603 136083744543111125199200405)
          ·
            refine ⟨6378925525458333993712519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136083744543111125199200405 6378925525458333993712519)
            ·
              refine ⟨9568388288187500990568779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378925525458333993712519 9568388288187500990568779)
              ·
                refine ⟨14352582432281251485853169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568388288187500990568779 14352582432281251485853169)
                ·
                  refine ⟨10764436824210938614389877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14352582432281251485853169 10764436824210938614389877)
                  ·
                    refine ⟨1009165952269775495099051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10764436824210938614389877 1009165952269775495099051)
                    ·
                      rfl

theorem cell23_5896031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_5896031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896031 prefixEnd_5896031 := by exact prefixLift 5896031
  have htrace : WordTrace (prefixWord ++ tailWord_5896031) baseStart_5896031 baseEnd_5896031 := by
    simpa [prefixWord, tailWord_5896031, baseEnd_5896031] using wordTrace_append hprefix tailTrace_5896031
  have hstable : (prefixWord ++ tailWord_5896031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896031).length < 2 ^ (prefixWord ++ tailWord_5896031).sum := by decide
  have hdescent : baseEnd_5896031 < baseStart_5896031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896101 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_5896101 : Nat := 118140960795 + 5896101 * 2 ^ 59
def prefixEnd_5896101 : Nat := 4983230072969 + 3 ^ 40 * 5896101 * 2
def baseEnd_5896101 : Nat := 3027533800455141211421831

theorem tailTrace_5896101 : CollatzResearch.WordTrace tailWord_5896101 prefixEnd_5896101 3027533800455141211421831 := by
  unfold tailWord_5896101
  simp only [CollatzResearch.WordTrace]
  refine ⟨215048470412440525726624157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143365646941627017151082771 215048470412440525726624157)
  ·
    refine ⟨80643176404665197147484059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215048470412440525726624157 80643176404665197147484059)
    ·
      refine ⟨120964764606997795721226089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80643176404665197147484059 120964764606997795721226089)
      ·
        refine ⟨90723573455248346790919567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120964764606997795721226089 90723573455248346790919567)
        ·
          refine ⟨136085360182872520186379351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90723573455248346790919567 136085360182872520186379351)
          ·
            refine ⟨204128040274308780279569027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136085360182872520186379351 204128040274308780279569027)
            ·
              refine ⟨306192060411463170419353541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204128040274308780279569027 306192060411463170419353541)
              ·
                refine ⟨57411011327149344453628789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306192060411463170419353541 57411011327149344453628789)
                ·
                  refine ⟨5382282311920251042527699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57411011327149344453628789 5382282311920251042527699)
                  ·
                    refine ⟨8073423467880376563791549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5382282311920251042527699 8073423467880376563791549)
                    ·
                      refine ⟨3027533800455141211421831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073423467880376563791549 3027533800455141211421831)
                      ·
                        rfl

theorem cell23_5896101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_5896101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896101 prefixEnd_5896101 := by exact prefixLift 5896101
  have htrace : WordTrace (prefixWord ++ tailWord_5896101) baseStart_5896101 baseEnd_5896101 := by
    simpa [prefixWord, tailWord_5896101, baseEnd_5896101] using wordTrace_append hprefix tailTrace_5896101
  have hstable : (prefixWord ++ tailWord_5896101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896101).length < 2 ^ (prefixWord ++ tailWord_5896101).sum := by decide
  have hdescent : baseEnd_5896101 < baseStart_5896101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896144 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_5896144 : Nat := 118140960795 + 5896144 * 2 ^ 59
def prefixEnd_5896144 : Nat := 4983230072969 + 3 ^ 40 * 5896144 * 2
def baseEnd_5896144 : Nat := 3027555880123284543184133

theorem tailTrace_5896144 : CollatzResearch.WordTrace tailWord_5896144 prefixEnd_5896144 3027555880123284543184133 := by
  unfold tailWord_5896144
  simp only [CollatzResearch.WordTrace]
  refine ⟨107525019375642372035219743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143366692500856496046959657 107525019375642372035219743)
  ·
    refine ⟨161287529063463558052829615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107525019375642372035219743 161287529063463558052829615)
    ·
      refine ⟨241931293595195337079244423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161287529063463558052829615 241931293595195337079244423)
      ·
        refine ⟨362896940392793005618866635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241931293595195337079244423 362896940392793005618866635)
        ·
          refine ⟨544345410589189508428299953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362896940392793005618866635 544345410589189508428299953)
          ·
            refine ⟨408259057941892131321224965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544345410589189508428299953 408259057941892131321224965)
            ·
              refine ⟨76548573364104774622729681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 408259057941892131321224965 76548573364104774622729681)
              ·
                refine ⟨57411430023078580967047261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76548573364104774622729681 57411430023078580967047261)
                ·
                  refine ⟨21529286258654467862642723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57411430023078580967047261 21529286258654467862642723)
                  ·
                    refine ⟨32293929387981701793964085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21529286258654467862642723 32293929387981701793964085)
                    ·
                      refine ⟨3027555880123284543184133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32293929387981701793964085 3027555880123284543184133)
                      ·
                        rfl

theorem cell23_5896144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_5896144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896144 prefixEnd_5896144 := by exact prefixLift 5896144
  have htrace : WordTrace (prefixWord ++ tailWord_5896144) baseStart_5896144 baseEnd_5896144 := by
    simpa [prefixWord, tailWord_5896144, baseEnd_5896144] using wordTrace_append hprefix tailTrace_5896144
  have hstable : (prefixWord ++ tailWord_5896144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896144).length < 2 ^ (prefixWord ++ tailWord_5896144).sum := by decide
  have hdescent : baseEnd_5896144 < baseStart_5896144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896161 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_5896161 : Nat := 118140960795 + 5896161 * 2 ^ 59
def prefixEnd_5896161 : Nat := 4983230072969 + 3 ^ 40 * 5896161 * 2
def baseEnd_5896161 : Nat := 3027564609294410976671555

theorem tailTrace_5896161 : CollatzResearch.WordTrace tailWord_5896161 prefixEnd_5896161 3027564609294410976671555 := by
  unfold tailWord_5896161
  simp only [CollatzResearch.WordTrace]
  refine ⟨215050658792223155973808337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143367105861482103982538891 215050658792223155973808337)
  ·
    refine ⟨161287994094167366980356253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215050658792223155973808337 161287994094167366980356253)
    ·
      refine ⟨60482997785312762617633595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161287994094167366980356253 60482997785312762617633595)
      ·
        refine ⟨90724496677969143926450393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60482997785312762617633595 90724496677969143926450393)
        ·
          refine ⟨68043372508476857944837795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90724496677969143926450393 68043372508476857944837795)
          ·
            refine ⟨102065058762715286917256693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68043372508476857944837795 102065058762715286917256693)
            ·
              refine ⟨9568599259004558148492815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102065058762715286917256693 9568599259004558148492815)
              ·
                refine ⟨14352898888506837222739223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568599259004558148492815 14352898888506837222739223)
                ·
                  refine ⟨21529348332760255834108835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14352898888506837222739223 21529348332760255834108835)
                  ·
                    refine ⟨32294022499140383751163253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21529348332760255834108835 32294022499140383751163253)
                    ·
                      refine ⟨3027564609294410976671555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32294022499140383751163253 3027564609294410976671555)
                      ·
                        rfl

theorem cell23_5896161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_5896161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896161 prefixEnd_5896161 := by exact prefixLift 5896161
  have htrace : WordTrace (prefixWord ++ tailWord_5896161) baseStart_5896161 baseEnd_5896161 := by
    simpa [prefixWord, tailWord_5896161, baseEnd_5896161] using wordTrace_append hprefix tailTrace_5896161
  have hstable : (prefixWord ++ tailWord_5896161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896161).length < 2 ^ (prefixWord ++ tailWord_5896161).sum := by decide
  have hdescent : baseEnd_5896161 < baseStart_5896161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896184 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_5896184 : Nat := 118140960795 + 5896184 * 2 ^ 59
def prefixEnd_5896184 : Nat := 4983230072969 + 3 ^ 40 * 5896184 * 2
def baseEnd_5896184 : Nat := 3027576419349464386683949

theorem tailTrace_5896184 : CollatzResearch.WordTrace tailWord_5896184 prefixEnd_5896184 3027576419349464386683949 := by
  unfold tailWord_5896184
  simp only [CollatzResearch.WordTrace]
  refine ⟨107525748835569915450947803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143367665114093220601263737 107525748835569915450947803)
  ·
    refine ⟨161288623253354873176421705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107525748835569915450947803 161288623253354873176421705)
    ·
      refine ⟨120966467440016154882316279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161288623253354873176421705 120966467440016154882316279)
      ·
        refine ⟨181449701160024232323474419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120966467440016154882316279 181449701160024232323474419)
        ·
          refine ⟨272174551740036348485211629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181449701160024232323474419 272174551740036348485211629)
          ·
            refine ⟨102065456902513630681954361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272174551740036348485211629 102065456902513630681954361)
            ·
              refine ⟨76549092676885223011465771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102065456902513630681954361 76549092676885223011465771)
              ·
                refine ⟨114823639015327834517198657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76549092676885223011465771 114823639015327834517198657)
                ·
                  refine ⟨86117729261495875887898993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114823639015327834517198657 86117729261495875887898993)
                  ·
                    refine ⟨64588296946121906915924245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86117729261495875887898993 64588296946121906915924245)
                    ·
                      refine ⟨3027576419349464386683949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64588296946121906915924245 3027576419349464386683949)
                      ·
                        rfl

theorem cell23_5896184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_5896184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896184 prefixEnd_5896184 := by exact prefixLift 5896184
  have htrace : WordTrace (prefixWord ++ tailWord_5896184) baseStart_5896184 baseEnd_5896184 := by
    simpa [prefixWord, tailWord_5896184, baseEnd_5896184] using wordTrace_append hprefix tailTrace_5896184
  have hstable : (prefixWord ++ tailWord_5896184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896184).length < 2 ^ (prefixWord ++ tailWord_5896184).sum := by decide
  have hdescent : baseEnd_5896184 < baseStart_5896184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896225 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5896225 : Nat := 118140960795 + 5896225 * 2 ^ 59
def prefixEnd_5896225 : Nat := 4983230072969 + 3 ^ 40 * 5896225 * 2
def baseEnd_5896225 : Nat := 3027597472056298726271261

theorem tailTrace_5896225 : CollatzResearch.WordTrace tailWord_5896225 prefixEnd_5896225 3027597472056298726271261 := by
  unfold tailWord_5896225
  simp only [CollatzResearch.WordTrace]
  refine ⟨215052993063991294904138129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143368662042660863269425419 215052993063991294904138129)
  ·
    refine ⟨161289744797993471178103597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215052993063991294904138129 161289744797993471178103597)
    ·
      refine ⟨60483654299247551691788849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161289744797993471178103597 60483654299247551691788849)
      ·
        refine ⟨45362740724435663768841637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60483654299247551691788849 45362740724435663768841637)
        ·
          refine ⟨8505513885831686956657807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45362740724435663768841637 8505513885831686956657807)
          ·
            refine ⟨12758270828747530434986711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505513885831686956657807 12758270828747530434986711)
            ·
              refine ⟨19137406243121295652480067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12758270828747530434986711 19137406243121295652480067)
              ·
                refine ⟨28706109364681943478720101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19137406243121295652480067 28706109364681943478720101)
                ·
                  refine ⟨5382395505877864402260019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28706109364681943478720101 5382395505877864402260019)
                  ·
                    refine ⟨8073593258816796603390029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5382395505877864402260019 8073593258816796603390029)
                    ·
                      refine ⟨3027597472056298726271261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073593258816796603390029 3027597472056298726271261)
                      ·
                        rfl

theorem cell23_5896225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5896225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896225 prefixEnd_5896225 := by exact prefixLift 5896225
  have htrace : WordTrace (prefixWord ++ tailWord_5896225) baseStart_5896225 baseEnd_5896225 := by
    simpa [prefixWord, tailWord_5896225, baseEnd_5896225] using wordTrace_append hprefix tailTrace_5896225
  have hstable : (prefixWord ++ tailWord_5896225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896225).length < 2 ^ (prefixWord ++ tailWord_5896225).sum := by decide
  have hdescent : baseEnd_5896225 < baseStart_5896225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896241 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_5896241 : Nat := 118140960795 + 5896241 * 2 ^ 59
def prefixEnd_5896241 : Nat := 4983230072969 + 3 ^ 40 * 5896241 * 2
def baseEnd_5896241 : Nat := 1009201895915590221223729

theorem tailTrace_5896241 : CollatzResearch.WordTrace tailWord_5896241 prefixEnd_5896241 1009201895915590221223729 := by
  unfold tailWord_5896241
  simp only [CollatzResearch.WordTrace]
  refine ⟨215053576631933329636720577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143369051087955553091147051 215053576631933329636720577)
  ·
    refine ⟨161290182473949997227540433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215053576631933329636720577 161290182473949997227540433)
    ·
      refine ⟨120967636855462497920655325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161290182473949997227540433 120967636855462497920655325)
      ·
        refine ⟨45362863820798436720245747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120967636855462497920655325 45362863820798436720245747)
        ·
          refine ⟨68044295731197655080368621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45362863820798436720245747 68044295731197655080368621)
          ·
            refine ⟨25516610899199120655138233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68044295731197655080368621 25516610899199120655138233)
            ·
              refine ⟨19137458174399340491353675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25516610899199120655138233 19137458174399340491353675)
              ·
                refine ⟨28706187261599010737030513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19137458174399340491353675 28706187261599010737030513)
                ·
                  refine ⟨21529640446199258052772885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28706187261599010737030513 21529640446199258052772885)
                  ·
                    refine ⟨1009201895915590221223729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21529640446199258052772885 1009201895915590221223729)
                    ·
                      rfl

theorem cell23_5896241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_5896241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896241 prefixEnd_5896241 := by exact prefixLift 5896241
  have htrace : WordTrace (prefixWord ++ tailWord_5896241) baseStart_5896241 baseEnd_5896241 := by
    simpa [prefixWord, tailWord_5896241, baseEnd_5896241] using wordTrace_append hprefix tailTrace_5896241
  have hstable : (prefixWord ++ tailWord_5896241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896241).length < 2 ^ (prefixWord ++ tailWord_5896241).sum := by decide
  have hdescent : baseEnd_5896241 < baseStart_5896241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896242 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_5896242 : Nat := 118140960795 + 5896242 * 2 ^ 59
def prefixEnd_5896242 : Nat := 4983230072969 + 3 ^ 40 * 5896242 * 2
def baseEnd_5896242 : Nat := 3027606201227425159758683

theorem tailTrace_5896242 : CollatzResearch.WordTrace tailWord_5896242 prefixEnd_5896242 3027606201227425159758683 := by
  unfold tailWord_5896242
  simp only [CollatzResearch.WordTrace]
  refine ⟨53763403276232426701876745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143369075403286471205004653 53763403276232426701876745)
  ·
    refine ⟨40322552457174320026407559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53763403276232426701876745 40322552457174320026407559)
    ·
      refine ⟨60483828685761480039611339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40322552457174320026407559 60483828685761480039611339)
      ·
        refine ⟨90725743028642220059417009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60483828685761480039611339 90725743028642220059417009)
        ·
          refine ⟨68044307271481665044562757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90725743028642220059417009 68044307271481665044562757)
          ·
            refine ⟨12758307613402812195855517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68044307271481665044562757 12758307613402812195855517)
            ·
              refine ⟨4784365355026054573445819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12758307613402812195855517 4784365355026054573445819)
              ·
                refine ⟨7176548032539081860168729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784365355026054573445819 7176548032539081860168729)
                ·
                  refine ⟨5382411024404311395126547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7176548032539081860168729 5382411024404311395126547)
                  ·
                    refine ⟨8073616536606467092689821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5382411024404311395126547 8073616536606467092689821)
                    ·
                      refine ⟨3027606201227425159758683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073616536606467092689821 3027606201227425159758683)
                      ·
                        rfl

theorem cell23_5896242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_5896242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896242 prefixEnd_5896242 := by exact prefixLift 5896242
  have htrace : WordTrace (prefixWord ++ tailWord_5896242) baseStart_5896242 baseEnd_5896242 := by
    simpa [prefixWord, tailWord_5896242, baseEnd_5896242] using wordTrace_append hprefix tailTrace_5896242
  have hstable : (prefixWord ++ tailWord_5896242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896242).length < 2 ^ (prefixWord ++ tailWord_5896242).sum := by decide
  have hdescent : baseEnd_5896242 < baseStart_5896242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896288 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 7]
def baseStart_5896288 : Nat := 118140960795 + 5896288 * 2 ^ 59
def prefixEnd_5896288 : Nat := 4983230072969 + 3 ^ 40 * 5896288 * 2
def baseEnd_5896288 : Nat := 336403313481947997753719

theorem tailTrace_5896288 : CollatzResearch.WordTrace tailWord_5896288 prefixEnd_5896288 336403313481947997753719 := by
  unfold tailWord_5896288
  simp only [CollatzResearch.WordTrace]
  refine ⟨107527645431381528331840759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143370193908508704442454345 107527645431381528331840759)
  ·
    refine ⟨161291468147072292497761139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107527645431381528331840759 161291468147072292497761139)
    ·
      refine ⟨241937202220608438746641709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161291468147072292497761139 241937202220608438746641709)
      ·
        refine ⟨90726450832728164529990641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241937202220608438746641709 90726450832728164529990641)
        ·
          refine ⟨68044838124546123397492981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90726450832728164529990641 68044838124546123397492981)
          ·
            refine ⟨6379203574176199068514967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68044838124546123397492981 6379203574176199068514967)
            ·
              refine ⟨9568805361264298602772451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6379203574176199068514967 9568805361264298602772451)
              ·
                refine ⟨14353208041896447904158677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568805361264298602772451 14353208041896447904158677)
                ·
                  refine ⟨336403313481947997753719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14353208041896447904158677 336403313481947997753719)
                  ·
                    rfl

theorem cell23_5896288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_5896288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896288 prefixEnd_5896288 := by exact prefixLift 5896288
  have htrace : WordTrace (prefixWord ++ tailWord_5896288) baseStart_5896288 baseEnd_5896288 := by
    simpa [prefixWord, tailWord_5896288, baseEnd_5896288] using wordTrace_append hprefix tailTrace_5896288
  have hstable : (prefixWord ++ tailWord_5896288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896288).length < 2 ^ (prefixWord ++ tailWord_5896288).sum := by decide
  have hdescent : baseEnd_5896288 < baseStart_5896288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896328 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5896328 : Nat := 118140960795 + 5896328 * 2 ^ 59
def prefixEnd_5896328 : Nat := 4983230072969 + 3 ^ 40 * 5896328 * 2
def baseEnd_5896328 : Nat := 3027650360563711823283287

theorem tailTrace_5896328 : CollatzResearch.WordTrace tailWord_5896328 prefixEnd_5896328 3027650360563711823283287 := by
  unfold tailWord_5896328
  simp only [CollatzResearch.WordTrace]
  refine ⟨107528374891309071747568819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143371166521745428996758425 107528374891309071747568819)
  ·
    refine ⟨161292562336963607621353229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107528374891309071747568819 161292562336963607621353229)
    ·
      refine ⟨60484710876361352858007461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161292562336963607621353229 60484710876361352858007461)
      ·
        refine ⟨11340883289317753660876399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60484710876361352858007461 11340883289317753660876399)
        ·
          refine ⟨17011324933976630491314599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11340883289317753660876399 17011324933976630491314599)
          ·
            refine ⟨25516987400964945736971899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17011324933976630491314599 25516987400964945736971899)
            ·
              refine ⟨38275481101447418605457849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25516987400964945736971899 38275481101447418605457849)
              ·
                refine ⟨28706610826085563954093387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38275481101447418605457849 28706610826085563954093387)
                ·
                  refine ⟨43059916239128345931140081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28706610826085563954093387 43059916239128345931140081)
                  ·
                    refine ⟨32294937179346259448355061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43059916239128345931140081 32294937179346259448355061)
                    ·
                      refine ⟨3027650360563711823283287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32294937179346259448355061 3027650360563711823283287)
                      ·
                        rfl

theorem cell23_5896328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5896328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896328 prefixEnd_5896328 := by exact prefixLift 5896328
  have htrace : WordTrace (prefixWord ++ tailWord_5896328) baseStart_5896328 baseEnd_5896328 := by
    simpa [prefixWord, tailWord_5896328, baseEnd_5896328] using wordTrace_append hprefix tailTrace_5896328
  have hstable : (prefixWord ++ tailWord_5896328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896328).length < 2 ^ (prefixWord ++ tailWord_5896328).sum := by decide
  have hdescent : baseEnd_5896328 < baseStart_5896328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896341 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_5896341 : Nat := 118140960795 + 5896341 * 2 ^ 59
def prefixEnd_5896341 : Nat := 4983230072969 + 3 ^ 40 * 5896341 * 2
def baseEnd_5896341 : Nat := 3027657035812220272420727

theorem tailTrace_5896341 : CollatzResearch.WordTrace tailWord_5896341 prefixEnd_5896341 3027657035812220272420727 := by
  unfold tailWord_5896341
  simp only [CollatzResearch.WordTrace]
  refine ⟨215057223931571046715360877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143371482621047364476907251 215057223931571046715360877)
  ·
    refine ⟨80646458974339142518260329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215057223931571046715360877 80646458974339142518260329)
    ·
      refine ⟨60484844230754356888695247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80646458974339142518260329 60484844230754356888695247)
      ·
        refine ⟨90727266346131535333042871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60484844230754356888695247 90727266346131535333042871)
        ·
          refine ⟨136090899519197302999564307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90727266346131535333042871 136090899519197302999564307)
          ·
            refine ⟨204136349278795954499346461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136090899519197302999564307 204136349278795954499346461)
            ·
              refine ⟨76551130979548482937254923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204136349278795954499346461 76551130979548482937254923)
              ·
                refine ⟨114826696469322724405882385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76551130979548482937254923 114826696469322724405882385)
                ·
                  refine ⟨86120022351992043304411789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114826696469322724405882385 86120022351992043304411789)
                  ·
                    refine ⟨32295008381997016239154421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86120022351992043304411789 32295008381997016239154421)
                    ·
                      refine ⟨3027657035812220272420727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32295008381997016239154421 3027657035812220272420727)
                      ·
                        rfl

theorem cell23_5896341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_5896341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896341 prefixEnd_5896341 := by exact prefixLift 5896341
  have htrace : WordTrace (prefixWord ++ tailWord_5896341) baseStart_5896341 baseEnd_5896341 := by
    simpa [prefixWord, tailWord_5896341, baseEnd_5896341] using wordTrace_append hprefix tailTrace_5896341
  have hstable : (prefixWord ++ tailWord_5896341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896341).length < 2 ^ (prefixWord ++ tailWord_5896341).sum := by decide
  have hdescent : baseEnd_5896341 < baseStart_5896341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896365 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_5896365 : Nat := 118140960795 + 5896365 * 2 ^ 59
def prefixEnd_5896365 : Nat := 4983230072969 + 3 ^ 40 * 5896365 * 2
def baseEnd_5896365 : Nat := 1009223119782642726173539

theorem tailTrace_5896365 : CollatzResearch.WordTrace tailWord_5896365 prefixEnd_5896365 1009223119782642726173539 := by
  unfold tailWord_5896365
  simp only [CollatzResearch.WordTrace]
  refine ⟨215058099283484098814234549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143372066188989399209489699 215058099283484098814234549)
  ·
    refine ⟨20161696807826634263834489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215058099283484098814234549 20161696807826634263834489)
    ·
      refine ⟨15121272605869975697875867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20161696807826634263834489 15121272605869975697875867)
      ·
        refine ⟨22681908908804963546813801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15121272605869975697875867 22681908908804963546813801)
        ·
          refine ⟨17011431681603722660110351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22681908908804963546813801 17011431681603722660110351)
          ·
            refine ⟨25517147522405583990165527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17011431681603722660110351 25517147522405583990165527)
            ·
              refine ⟨38275721283608375985248291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25517147522405583990165527 38275721283608375985248291)
              ·
                refine ⟨57413581925412563977872437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38275721283608375985248291 57413581925412563977872437)
                ·
                  refine ⟨5382523305507427872925541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57413581925412563977872437 5382523305507427872925541)
                  ·
                    refine ⟨1009223119782642726173539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5382523305507427872925541 1009223119782642726173539)
                    ·
                      rfl

theorem cell23_5896365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_5896365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896365 prefixEnd_5896365 := by exact prefixLift 5896365
  have htrace : WordTrace (prefixWord ++ tailWord_5896365) baseStart_5896365 baseEnd_5896365 := by
    simpa [prefixWord, tailWord_5896365, baseEnd_5896365] using wordTrace_append hprefix tailTrace_5896365
  have hstable : (prefixWord ++ tailWord_5896365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896365).length < 2 ^ (prefixWord ++ tailWord_5896365).sum := by decide
  have hdescent : baseEnd_5896365 < baseStart_5896365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896375 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_5896375 : Nat := 118140960795 + 5896375 * 2 ^ 59
def prefixEnd_5896375 : Nat := 4983230072969 + 3 ^ 40 * 5896375 * 2
def baseEnd_5896375 : Nat := 3027674494154473139395571

theorem tailTrace_5896375 : CollatzResearch.WordTrace tailWord_5896375 prefixEnd_5896375 3027674494154473139395571 := by
  unfold tailWord_5896375
  simp only [CollatzResearch.WordTrace]
  refine ⟨215058464013447870522098579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143372309342298580348065719 215058464013447870522098579)
  ·
    refine ⟨322587696020171805783147869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215058464013447870522098579 322587696020171805783147869)
    ·
      refine ⟨120970386007564427168680451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322587696020171805783147869 120970386007564427168680451)
      ·
        refine ⟨181455579011346640753020677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120970386007564427168680451 181455579011346640753020677)
        ·
          refine ⟨34022921064627495141191377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181455579011346640753020677 34022921064627495141191377)
          ·
            refine ⟨25517190798470621355893533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34022921064627495141191377 25517190798470621355893533)
            ·
              refine ⟨9568946549426483008460075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25517190798470621355893533 9568946549426483008460075)
              ·
                refine ⟨14353419824139724512690113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568946549426483008460075 14353419824139724512690113)
                ·
                  refine ⟨10765064868104793384517585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14353419824139724512690113 10765064868104793384517585)
                  ·
                    refine ⟨8073798651078595038388189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10765064868104793384517585 8073798651078595038388189)
                    ·
                      refine ⟨3027674494154473139395571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073798651078595038388189 3027674494154473139395571)
                      ·
                        rfl

theorem cell23_5896375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_5896375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896375 prefixEnd_5896375 := by exact prefixLift 5896375
  have htrace : WordTrace (prefixWord ++ tailWord_5896375) baseStart_5896375 baseEnd_5896375 := by
    simpa [prefixWord, tailWord_5896375, baseEnd_5896375] using wordTrace_append hprefix tailTrace_5896375
  have hstable : (prefixWord ++ tailWord_5896375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896375).length < 2 ^ (prefixWord ++ tailWord_5896375).sum := by decide
  have hdescent : baseEnd_5896375 < baseStart_5896375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896398 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5896398 : Nat := 118140960795 + 5896398 * 2 ^ 59
def prefixEnd_5896398 : Nat := 4983230072969 + 3 ^ 40 * 5896398 * 2
def baseEnd_5896398 : Nat := 3027686304209526549407965

theorem tailTrace_5896398 : CollatzResearch.WordTrace tailWord_5896398 prefixEnd_5896398 3027686304209526549407965 := by
  unfold tailWord_5896398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26882412861545568181273231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143372868594909696966790565 26882412861545568181273231)
  ·
    refine ⟨40323619292318352271909847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26882412861545568181273231 40323619292318352271909847)
    ·
      refine ⟨60485428938477528407864771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40323619292318352271909847 60485428938477528407864771)
      ·
        refine ⟨90728143407716292611797157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60485428938477528407864771 90728143407716292611797157)
        ·
          refine ⟨17011526888946804864711967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90728143407716292611797157 17011526888946804864711967)
          ·
            refine ⟨25517290333420207297067951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17011526888946804864711967 25517290333420207297067951)
            ·
              refine ⟨38275935500130310945601927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25517290333420207297067951 38275935500130310945601927)
              ·
                refine ⟨57413903250195466418402891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38275935500130310945601927 57413903250195466418402891)
                ·
                  refine ⟨86120854875293199627604337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57413903250195466418402891 86120854875293199627604337)
                  ·
                    refine ⟨64590641156469899720703253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86120854875293199627604337 64590641156469899720703253)
                    ·
                      refine ⟨3027686304209526549407965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64590641156469899720703253 3027686304209526549407965)
                      ·
                        rfl

theorem cell23_5896398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5896398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896398 prefixEnd_5896398 := by exact prefixLift 5896398
  have htrace : WordTrace (prefixWord ++ tailWord_5896398) baseStart_5896398 baseEnd_5896398 := by
    simpa [prefixWord, tailWord_5896398, baseEnd_5896398] using wordTrace_append hprefix tailTrace_5896398
  have hstable : (prefixWord ++ tailWord_5896398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896398).length < 2 ^ (prefixWord ++ tailWord_5896398).sum := by decide
  have hdescent : baseEnd_5896398 < baseStart_5896398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896448 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_5896448 : Nat := 118140960795 + 5896448 * 2 ^ 59
def prefixEnd_5896448 : Nat := 4983230072969 + 3 ^ 40 * 5896448 * 2
def baseEnd_5896448 : Nat := 3027711978242251353782735

theorem tailTrace_5896448 : CollatzResearch.WordTrace tailWord_5896448 prefixEnd_5896448 3027711978242251353782735 := by
  unfold tailWord_5896448
  simp only [CollatzResearch.WordTrace]
  refine ⟨107530563271091701994752999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143374084361455602659670665 107530563271091701994752999)
  ·
    refine ⟨161295844906637552992129499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107530563271091701994752999 161295844906637552992129499)
    ·
      refine ⟨241943767359956329488194249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161295844906637552992129499 241943767359956329488194249)
      ·
        refine ⟨181457825519967247116145687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241943767359956329488194249 181457825519967247116145687)
        ·
          refine ⟨272186738279950870674218531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181457825519967247116145687 272186738279950870674218531)
          ·
            refine ⟨408280107419926306011327797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272186738279950870674218531 408280107419926306011327797)
            ·
              refine ⟨38276260070618091188561981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408280107419926306011327797 38276260070618091188561981)
              ·
                refine ⟨14353597526481784195710743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38276260070618091188561981 14353597526481784195710743)
                ·
                  refine ⟨21530396289722676293566115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14353597526481784195710743 21530396289722676293566115)
                  ·
                    refine ⟨32295594434584014440349173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21530396289722676293566115 32295594434584014440349173)
                    ·
                      refine ⟨3027711978242251353782735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32295594434584014440349173 3027711978242251353782735)
                      ·
                        rfl

theorem cell23_5896448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_5896448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896448 prefixEnd_5896448 := by exact prefixLift 5896448
  have htrace : WordTrace (prefixWord ++ tailWord_5896448) baseStart_5896448 baseEnd_5896448 := by
    simpa [prefixWord, tailWord_5896448, baseEnd_5896448] using wordTrace_append hprefix tailTrace_5896448
  have hstable : (prefixWord ++ tailWord_5896448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896448).length < 2 ^ (prefixWord ++ tailWord_5896448).sum := by decide
  have hdescent : baseEnd_5896448 < baseStart_5896448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896456 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_5896456 : Nat := 118140960795 + 5896456 * 2 ^ 59
def prefixEnd_5896456 : Nat := 4983230072969 + 3 ^ 40 * 5896456 * 2
def baseEnd_5896456 : Nat := 3027716086087487322482699

theorem tailTrace_5896456 : CollatzResearch.WordTrace tailWord_5896456 prefixEnd_5896456 3027716086087487322482699 := by
  unfold tailWord_5896456
  simp only [CollatzResearch.WordTrace]
  refine ⟨107530709163077210677898611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143374278884102947570531481 107530709163077210677898611)
  ·
    refine ⟨161296063744615816016847917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107530709163077210677898611 161296063744615816016847917)
    ·
      refine ⟨60486023904230931006317969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161296063744615816016847917 60486023904230931006317969)
      ·
        refine ⟨45364517928173198254738477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60486023904230931006317969 45364517928173198254738477)
        ·
          refine ⟨17011694223064949345526929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45364517928173198254738477 17011694223064949345526929)
          ·
            refine ⟨12758770667298712009145197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17011694223064949345526929 12758770667298712009145197)
            ·
              refine ⟨4784539000237017003429449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12758770667298712009145197 4784539000237017003429449)
              ·
                refine ⟨3588404250177762752572087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4784539000237017003429449 3588404250177762752572087)
                ·
                  refine ⟨5382606375266644128858131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588404250177762752572087 5382606375266644128858131)
                  ·
                    refine ⟨8073909562899966193287197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5382606375266644128858131 8073909562899966193287197)
                    ·
                      refine ⟨3027716086087487322482699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073909562899966193287197 3027716086087487322482699)
                      ·
                        rfl

theorem cell23_5896456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_5896456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896456 prefixEnd_5896456 := by exact prefixLift 5896456
  have htrace : WordTrace (prefixWord ++ tailWord_5896456) baseStart_5896456 baseEnd_5896456 := by
    simpa [prefixWord, tailWord_5896456, baseEnd_5896456] using wordTrace_append hprefix tailTrace_5896456
  have hstable : (prefixWord ++ tailWord_5896456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896456).length < 2 ^ (prefixWord ++ tailWord_5896456).sum := by decide
  have hdescent : baseEnd_5896456 < baseStart_5896456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896458 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5896458 : Nat := 118140960795 + 5896458 * 2 ^ 59
def prefixEnd_5896458 : Nat := 4983230072969 + 3 ^ 40 * 5896458 * 2
def baseEnd_5896458 : Nat := 3027717113048796314657689

theorem tailTrace_5896458 : CollatzResearch.WordTrace tailWord_5896458 prefixEnd_5896458 3027717113048796314657689 := by
  unfold tailWord_5896458
  simp only [CollatzResearch.WordTrace]
  refine ⟨53765372818036793924342507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143374327514764783798246685 53765372818036793924342507)
  ·
    refine ⟨80648059227055190886513761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53765372818036793924342507 80648059227055190886513761)
    ·
      refine ⟨60486044420291393164885321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80648059227055190886513761 60486044420291393164885321)
      ·
        refine ⟨45364533315218544873663991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60486044420291393164885321 45364533315218544873663991)
        ·
          refine ⟨68046799972827817310495987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45364533315218544873663991 68046799972827817310495987)
          ·
            refine ⟨102070199959241725965743981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68046799972827817310495987 102070199959241725965743981)
            ·
              refine ⟨38276324984715647237153993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102070199959241725965743981 38276324984715647237153993)
              ·
                refine ⟨28707243738536735427865495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38276324984715647237153993 28707243738536735427865495)
                ·
                  refine ⟨43060865607805103141798243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28707243738536735427865495 43060865607805103141798243)
                  ·
                    refine ⟨64591298411707654712697365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43060865607805103141798243 64591298411707654712697365)
                    ·
                      refine ⟨3027717113048796314657689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64591298411707654712697365 3027717113048796314657689)
                      ·
                        rfl

theorem cell23_5896458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5896458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896458 prefixEnd_5896458 := by exact prefixLift 5896458
  have htrace : WordTrace (prefixWord ++ tailWord_5896458) baseStart_5896458 baseEnd_5896458 := by
    simpa [prefixWord, tailWord_5896458, baseEnd_5896458] using wordTrace_append hprefix tailTrace_5896458
  have hstable : (prefixWord ++ tailWord_5896458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896458).length < 2 ^ (prefixWord ++ tailWord_5896458).sum := by decide
  have hdescent : baseEnd_5896458 < baseStart_5896458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896482 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_5896482 : Nat := 118140960795 + 5896482 * 2 ^ 59
def prefixEnd_5896482 : Nat := 4983230072969 + 3 ^ 40 * 5896482 * 2
def baseEnd_5896482 : Nat := 3027729436584504220757579

theorem tailTrace_5896482 : CollatzResearch.WordTrace tailWord_5896482 prefixEnd_5896482 3027729436584504220757579 := by
  unfold tailWord_5896482
  simp only [CollatzResearch.WordTrace]
  refine ⟨53765591656015056949060925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143374911082706818530829133 53765591656015056949060925)
  ·
    refine ⟨20162096871005646355897847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53765591656015056949060925 20162096871005646355897847)
    ·
      refine ⟨30243145306508469533846771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20162096871005646355897847 30243145306508469533846771)
      ·
        refine ⟨45364717959762704300770157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30243145306508469533846771 45364717959762704300770157)
        ·
          refine ⟨17011769234911014112788809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45364717959762704300770157 17011769234911014112788809)
          ·
            refine ⟨12758826926183260584591607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17011769234911014112788809 12758826926183260584591607)
            ·
              refine ⟨19138240389274890876887411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12758826926183260584591607 19138240389274890876887411)
              ·
                refine ⟨28707360583912336315331117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19138240389274890876887411 28707360583912336315331117)
                ·
                  refine ⟨10765260218967126118249169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28707360583912336315331117 10765260218967126118249169)
                  ·
                    refine ⟨8073945164225344588686877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10765260218967126118249169 8073945164225344588686877)
                    ·
                      refine ⟨3027729436584504220757579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073945164225344588686877 3027729436584504220757579)
                      ·
                        rfl

theorem cell23_5896482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_5896482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896482 prefixEnd_5896482 := by exact prefixLift 5896482
  have htrace : WordTrace (prefixWord ++ tailWord_5896482) baseStart_5896482 baseEnd_5896482 := by
    simpa [prefixWord, tailWord_5896482, baseEnd_5896482] using wordTrace_append hprefix tailTrace_5896482
  have hstable : (prefixWord ++ tailWord_5896482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896482).length < 2 ^ (prefixWord ++ tailWord_5896482).sum := by decide
  have hdescent : baseEnd_5896482 < baseStart_5896482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896495 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 3]
def baseStart_5896495 : Nat := 118140960795 + 5896495 * 2 ^ 59
def prefixEnd_5896495 : Nat := 4983230072969 + 3 ^ 40 * 5896495 * 2
def baseEnd_5896495 : Nat := 3027736111833012669895019

theorem tailTrace_5896495 : CollatzResearch.WordTrace tailWord_5896495 prefixEnd_5896495 3027736111833012669895019 := by
  unfold tailWord_5896495
  simp only [CollatzResearch.WordTrace]
  refine ⟨215062840773013131016466939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143375227182008754010977959 215062840773013131016466939)
  ·
    refine ⟨322594261159519696524700409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215062840773013131016466939 322594261159519696524700409)
    ·
      refine ⟨241945695869639772393525307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322594261159519696524700409 241945695869639772393525307)
      ·
        refine ⟨362918543804459658590287961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241945695869639772393525307 362918543804459658590287961)
        ·
          refine ⟨272188907853344743942715971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362918543804459658590287961 272188907853344743942715971)
          ·
            refine ⟨408283361780017115914073957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272188907853344743942715971 408283361780017115914073957)
            ·
              refine ⟨76553130333753209233888867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 408283361780017115914073957 76553130333753209233888867)
              ·
                refine ⟨114829695500629813850833301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76553130333753209233888867 114829695500629813850833301)
                ·
                  refine ⟨5382641976592022524257811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114829695500629813850833301 5382641976592022524257811)
                  ·
                    refine ⟨8073962964888033786386717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5382641976592022524257811 8073962964888033786386717)
                    ·
                      refine ⟨3027736111833012669895019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8073962964888033786386717 3027736111833012669895019)
                      ·
                        rfl

theorem cell23_5896495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_5896495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896495 prefixEnd_5896495 := by exact prefixLift 5896495
  have htrace : WordTrace (prefixWord ++ tailWord_5896495) baseStart_5896495 baseEnd_5896495 := by
    simpa [prefixWord, tailWord_5896495, baseEnd_5896495] using wordTrace_append hprefix tailTrace_5896495
  have hstable : (prefixWord ++ tailWord_5896495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896495).length < 2 ^ (prefixWord ++ tailWord_5896495).sum := by decide
  have hdescent : baseEnd_5896495 < baseStart_5896495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896513 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5896513 : Nat := 118140960795 + 5896513 * 2 ^ 59
def prefixEnd_5896513 : Nat := 4983230072969 + 3 ^ 40 * 5896513 * 2
def baseEnd_5896513 : Nat := 3027745354484793599469937

theorem tailTrace_5896513 : CollatzResearch.WordTrace tailWord_5896513 prefixEnd_5896513 3027745354484793599469937 := by
  unfold tailWord_5896513
  simp only [CollatzResearch.WordTrace]
  refine ⟨215063497286947920090622193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143375664857965280060414795 215063497286947920090622193)
  ·
    refine ⟨161297622965210940067966645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215063497286947920090622193 161297622965210940067966645)
    ·
      refine ⟨15121652152988525631371873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161297622965210940067966645 15121652152988525631371873)
      ·
        refine ⟨11341239114741394223528905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15121652152988525631371873 11341239114741394223528905)
        ·
          refine ⟨8505929336056045667646679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11341239114741394223528905 8505929336056045667646679)
          ·
            refine ⟨12758894004084068501470019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505929336056045667646679 12758894004084068501470019)
            ·
              refine ⟨19138341006126102752205029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12758894004084068501470019 19138341006126102752205029)
              ·
                refine ⟨3588438938648644266038443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19138341006126102752205029 3588438938648644266038443)
                ·
                  refine ⟨5382658407972966399057665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588438938648644266038443 5382658407972966399057665)
                  ·
                    refine ⟨4036993805979724799293249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5382658407972966399057665 4036993805979724799293249)
                    ·
                      refine ⟨3027745354484793599469937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4036993805979724799293249 3027745354484793599469937)
                      ·
                        rfl

theorem cell23_5896513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5896513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896513 prefixEnd_5896513 := by exact prefixLift 5896513
  have htrace : WordTrace (prefixWord ++ tailWord_5896513) baseStart_5896513 baseEnd_5896513 := by
    simpa [prefixWord, tailWord_5896513, baseEnd_5896513] using wordTrace_append hprefix tailTrace_5896513
  have hstable : (prefixWord ++ tailWord_5896513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896513).length < 2 ^ (prefixWord ++ tailWord_5896513).sum := by decide
  have hdescent : baseEnd_5896513 < baseStart_5896513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896528 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_5896528 : Nat := 118140960795 + 5896528 * 2 ^ 59
def prefixEnd_5896528 : Nat := 4983230072969 + 3 ^ 40 * 5896528 * 2
def baseEnd_5896528 : Nat := 1009251018898203680260789

theorem tailTrace_5896528 : CollatzResearch.WordTrace tailWord_5896528 prefixEnd_5896528 1009251018898203680260789 := by
  unfold tailWord_5896528
  simp only [CollatzResearch.WordTrace]
  refine ⟨107532022190946788826209119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143376029587929051768278825 107532022190946788826209119)
  ·
    refine ⟨161298033286420183239313679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107532022190946788826209119 161298033286420183239313679)
    ·
      refine ⟨241947049929630274858970519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161298033286420183239313679 241947049929630274858970519)
      ·
        refine ⟨362920574894445412288455779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241947049929630274858970519 362920574894445412288455779)
        ·
          refine ⟨544380862341668118432683669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362920574894445412288455779 544380862341668118432683669)
          ·
            refine ⟨25517852922265693051532047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 544380862341668118432683669 25517852922265693051532047)
            ·
              refine ⟨38276779383398539577298071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25517852922265693051532047 38276779383398539577298071)
              ·
                refine ⟨57415169075097809365947107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38276779383398539577298071 57415169075097809365947107)
                ·
                  refine ⟨86122753612646714048920661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57415169075097809365947107 86122753612646714048920661)
                  ·
                    refine ⟨1009251018898203680260789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86122753612646714048920661 1009251018898203680260789)
                    ·
                      rfl

theorem cell23_5896528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_5896528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896528 prefixEnd_5896528 := by exact prefixLift 5896528
  have htrace : WordTrace (prefixWord ++ tailWord_5896528) baseStart_5896528 baseEnd_5896528 := by
    simpa [prefixWord, tailWord_5896528, baseEnd_5896528] using wordTrace_append hprefix tailTrace_5896528
  have hstable : (prefixWord ++ tailWord_5896528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896528).length < 2 ^ (prefixWord ++ tailWord_5896528).sum := by decide
  have hdescent : baseEnd_5896528 < baseStart_5896528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896635 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 9, 4]
def baseStart_5896635 : Nat := 118140960795 + 5896635 * 2 ^ 59
def prefixEnd_5896635 : Nat := 4983230072969 + 3 ^ 40 * 5896635 * 2
def baseEnd_5896635 : Nat := 1009269333041547374048125

theorem tailTrace_5896635 : CollatzResearch.WordTrace tailWord_5896635 prefixEnd_5896635 1009269333041547374048125 := by
  unfold tailWord_5896635
  simp only [CollatzResearch.WordTrace]
  refine ⟨215067946992505934926563359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143378631328337289951042239 215067946992505934926563359)
  ·
    refine ⟨322601920488758902389845039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215067946992505934926563359 322601920488758902389845039)
    ·
      refine ⟨483902880733138353584767559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322601920488758902389845039 483902880733138353584767559)
      ·
        refine ⟨725854321099707530377151339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483902880733138353584767559 725854321099707530377151339)
        ·
          refine ⟨1088781481649561295565727009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725854321099707530377151339 1088781481649561295565727009)
          ·
            refine ⟨816586111237170971674295257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088781481649561295565727009 816586111237170971674295257)
            ·
              refine ⟨612439583427878228755721443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816586111237170971674295257 612439583427878228755721443)
              ·
                refine ⟨918659375141817343133582165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612439583427878228755721443 918659375141817343133582165)
                ·
                  refine ⟨5382769776221585994923333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 918659375141817343133582165 5382769776221585994923333)
                  ·
                    refine ⟨1009269333041547374048125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5382769776221585994923333 1009269333041547374048125)
                    ·
                      rfl

theorem cell23_5896635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 4].length) (baseStart_5896635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896635 prefixEnd_5896635 := by exact prefixLift 5896635
  have htrace : WordTrace (prefixWord ++ tailWord_5896635) baseStart_5896635 baseEnd_5896635 := by
    simpa [prefixWord, tailWord_5896635, baseEnd_5896635] using wordTrace_append hprefix tailTrace_5896635
  have hstable : (prefixWord ++ tailWord_5896635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896635).length < 2 ^ (prefixWord ++ tailWord_5896635).sum := by decide
  have hdescent : baseEnd_5896635 < baseStart_5896635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896682 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_5896682 : Nat := 118140960795 + 5896682 * 2 ^ 59
def prefixEnd_5896682 : Nat := 4983230072969 + 3 ^ 40 * 5896682 * 2
def baseEnd_5896682 : Nat := 336425792523933715361851

theorem tailTrace_5896682 : CollatzResearch.WordTrace tailWord_5896682 prefixEnd_5896682 336425792523933715361851 := by
  unfold tailWord_5896682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53767415305833915488381075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143379774148890441302349533 53767415305833915488381075)
  ·
    refine ⟨80651122958750873232571613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53767415305833915488381075 80651122958750873232571613)
    ·
      refine ⟨30244171109531577462214355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80651122958750873232571613 30244171109531577462214355)
      ·
        refine ⟨45366256664297366193321533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30244171109531577462214355 45366256664297366193321533)
        ·
          refine ⟨17012346249111512322495575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45366256664297366193321533 17012346249111512322495575)
          ·
            refine ⟨25518519373667268483743363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17012346249111512322495575 25518519373667268483743363)
            ·
              refine ⟨38277779060500902725615045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25518519373667268483743363 38277779060500902725615045)
              ·
                refine ⟨7177083573843919261052821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38277779060500902725615045 7177083573843919261052821)
                ·
                  refine ⟨336425792523933715361851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7177083573843919261052821 336425792523933715361851)
                  ·
                    rfl

theorem cell23_5896682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_5896682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896682 prefixEnd_5896682 := by exact prefixLift 5896682
  have htrace : WordTrace (prefixWord ++ tailWord_5896682) baseStart_5896682 baseEnd_5896682 := by
    simpa [prefixWord, tailWord_5896682, baseEnd_5896682] using wordTrace_append hprefix tailTrace_5896682
  have hstable : (prefixWord ++ tailWord_5896682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896682).length < 2 ^ (prefixWord ++ tailWord_5896682).sum := by decide
  have hdescent : baseEnd_5896682 < baseStart_5896682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896686 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_5896686 : Nat := 118140960795 + 5896686 * 2 ^ 59
def prefixEnd_5896686 : Nat := 4983230072969 + 3 ^ 40 * 5896686 * 2
def baseEnd_5896686 : Nat := 1009278062212673807535547

theorem tailTrace_5896686 : CollatzResearch.WordTrace tailWord_5896686 prefixEnd_5896686 1009278062212673807535547 := by
  unfold tailWord_5896686
  simp only [CollatzResearch.WordTrace]
  refine ⟨26883725889415146329583739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143379871410214113757779941 26883725889415146329583739)
  ·
    refine ⟨40325588834122719494375609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26883725889415146329583739 40325588834122719494375609)
    ·
      refine ⟨30244191625592039620781707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40325588834122719494375609 30244191625592039620781707)
      ·
        refine ⟨45366287438388059431172561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30244191625592039620781707 45366287438388059431172561)
        ·
          refine ⟨34024715578791044573379421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45366287438388059431172561 34024715578791044573379421)
          ·
            refine ⟨12759268342046641715017283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34024715578791044573379421 12759268342046641715017283)
            ·
              refine ⟨19138902513069962572525925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12759268342046641715017283 19138902513069962572525925)
              ·
                refine ⟨3588544221200617982348611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19138902513069962572525925 3588544221200617982348611)
                ·
                  refine ⟨5382816331800926973522917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588544221200617982348611 5382816331800926973522917)
                  ·
                    refine ⟨1009278062212673807535547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5382816331800926973522917 1009278062212673807535547)
                    ·
                      rfl

theorem cell23_5896686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_5896686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896686 prefixEnd_5896686 := by exact prefixLift 5896686
  have htrace : WordTrace (prefixWord ++ tailWord_5896686) baseStart_5896686 baseEnd_5896686 := by
    simpa [prefixWord, tailWord_5896686, baseEnd_5896686] using wordTrace_append hprefix tailTrace_5896686
  have hstable : (prefixWord ++ tailWord_5896686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896686).length < 2 ^ (prefixWord ++ tailWord_5896686).sum := by decide
  have hdescent : baseEnd_5896686 < baseStart_5896686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896710 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5896710 : Nat := 118140960795 + 5896710 * 2 ^ 59
def prefixEnd_5896710 : Nat := 4983230072969 + 3 ^ 40 * 5896710 * 2
def baseEnd_5896710 : Nat := 3027846510173729328706531

theorem tailTrace_5896710 : CollatzResearch.WordTrace tailWord_5896710 prefixEnd_5896710 3027846510173729328706531 := by
  unfold tailWord_5896710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720958827101069460485737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143380454978156148490362389 6720958827101069460485737)
  ·
    refine ⟨5040719120325802095364303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6720958827101069460485737 5040719120325802095364303)
    ·
      refine ⟨7561078680488703143046455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040719120325802095364303 7561078680488703143046455)
      ·
        refine ⟨11341618020733054714569683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561078680488703143046455 11341618020733054714569683)
        ·
          refine ⟨17012427031099582071854525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11341618020733054714569683 17012427031099582071854525)
          ·
            refine ⟨6379660136662343276945447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17012427031099582071854525 6379660136662343276945447)
            ·
              refine ⟨9569490204993514915418171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6379660136662343276945447 9569490204993514915418171)
              ·
                refine ⟨14354235307490272373127257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9569490204993514915418171 14354235307490272373127257)
                ·
                  refine ⟨10765676480617704279845443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14354235307490272373127257 10765676480617704279845443)
                  ·
                    refine ⟨16148514720926556419768165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10765676480617704279845443 16148514720926556419768165)
                    ·
                      refine ⟨3027846510173729328706531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16148514720926556419768165 3027846510173729328706531)
                      ·
                        rfl

theorem cell23_5896710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5896710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896710 prefixEnd_5896710 := by exact prefixLift 5896710
  have htrace : WordTrace (prefixWord ++ tailWord_5896710) baseStart_5896710 baseEnd_5896710 := by
    simpa [prefixWord, tailWord_5896710, baseEnd_5896710] using wordTrace_append hprefix tailTrace_5896710
  have hstable : (prefixWord ++ tailWord_5896710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896710).length < 2 ^ (prefixWord ++ tailWord_5896710).sum := by decide
  have hdescent : baseEnd_5896710 < baseStart_5896710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896712 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 1, 5]
def baseStart_5896712 : Nat := 118140960795 + 5896712 * 2 ^ 59
def prefixEnd_5896712 : Nat := 4983230072969 + 3 ^ 40 * 5896712 * 2
def baseEnd_5896712 : Nat := 1009282512378346106960507

theorem tailTrace_5896712 : CollatzResearch.WordTrace tailWord_5896712 prefixEnd_5896712 1009282512378346106960507 := by
  unfold tailWord_5896712
  simp only [CollatzResearch.WordTrace]
  refine ⟨107535377706613488538558195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143380503608817984718077593 107535377706613488538558195)
  ·
    refine ⟨161303066559920232807837293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107535377706613488538558195 161303066559920232807837293)
    ·
      refine ⟨60488649959970087302938985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161303066559920232807837293 60488649959970087302938985)
      ·
        refine ⟨45366487469977565477204239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60488649959970087302938985 45366487469977565477204239)
        ·
          refine ⟨68049731204966348215806359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45366487469977565477204239 68049731204966348215806359)
          ·
            refine ⟨102074596807449522323709539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68049731204966348215806359 102074596807449522323709539)
            ·
              refine ⟨153111895211174283485564309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102074596807449522323709539 153111895211174283485564309)
              ·
                refine ⟨7177120088023794538385827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153111895211174283485564309 7177120088023794538385827)
                ·
                  refine ⟨10765680132035691807578741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177120088023794538385827 10765680132035691807578741)
                  ·
                    refine ⟨1009282512378346106960507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10765680132035691807578741 1009282512378346106960507)
                    ·
                      rfl

theorem cell23_5896712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_5896712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896712 prefixEnd_5896712 := by exact prefixLift 5896712
  have htrace : WordTrace (prefixWord ++ tailWord_5896712) baseStart_5896712 baseEnd_5896712 := by
    simpa [prefixWord, tailWord_5896712, baseEnd_5896712] using wordTrace_append hprefix tailTrace_5896712
  have hstable : (prefixWord ++ tailWord_5896712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896712).length < 2 ^ (prefixWord ++ tailWord_5896712).sum := by decide
  have hdescent : baseEnd_5896712 < baseStart_5896712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896752 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_5896752 : Nat := 118140960795 + 5896752 * 2 ^ 59
def prefixEnd_5896752 : Nat := 4983230072969 + 3 ^ 40 * 5896752 * 2
def baseEnd_5896752 : Nat := 3027868076361218164381337

theorem tailTrace_5896752 : CollatzResearch.WordTrace tailWord_5896752 prefixEnd_5896752 3027868076361218164381337 := by
  unfold tailWord_5896752
  simp only [CollatzResearch.WordTrace]
  refine ⟨107536107166541031954286255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143381476222054709272381673 107536107166541031954286255)
  ·
    refine ⟨161304160749811547931429383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107536107166541031954286255 161304160749811547931429383)
    ·
      refine ⟨241956241124717321897144075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161304160749811547931429383 241956241124717321897144075)
      ·
        refine ⟨362934361687075982845716113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241956241124717321897144075 362934361687075982845716113)
        ·
          refine ⟨272200771265306987134287085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362934361687075982845716113 272200771265306987134287085)
          ·
            refine ⟨102075289224490120175357657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272200771265306987134287085 102075289224490120175357657)
            ·
              refine ⟨76556466918367590131518243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102075289224490120175357657 76556466918367590131518243)
              ·
                refine ⟨114834700377551385197277365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76556466918367590131518243 114834700377551385197277365)
                ·
                  refine ⟨10765753160395442362244753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114834700377551385197277365 10765753160395442362244753)
                  ·
                    refine ⟨8074314870296581771683565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10765753160395442362244753 8074314870296581771683565)
                    ·
                      refine ⟨3027868076361218164381337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8074314870296581771683565 3027868076361218164381337)
                      ·
                        rfl

theorem cell23_5896752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_5896752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896752 prefixEnd_5896752 := by exact prefixLift 5896752
  have htrace : WordTrace (prefixWord ++ tailWord_5896752) baseStart_5896752 baseEnd_5896752 := by
    simpa [prefixWord, tailWord_5896752, baseEnd_5896752] using wordTrace_append hprefix tailTrace_5896752
  have hstable : (prefixWord ++ tailWord_5896752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896752).length < 2 ^ (prefixWord ++ tailWord_5896752).sum := by decide
  have hdescent : baseEnd_5896752 < baseStart_5896752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896755 : List Nat := [1, 1, 1, 2, 4, 2, 2, 10]
def baseStart_5896755 : Nat := 118140960795 + 5896755 * 2 ^ 59
def prefixEnd_5896755 : Nat := 4983230072969 + 3 ^ 40 * 5896755 * 2
def baseEnd_5896755 : Nat := 112143319140858579727549

theorem tailTrace_5896755 : CollatzResearch.WordTrace tailWord_5896755 prefixEnd_5896755 112143319140858579727549 := by
  unfold tailWord_5896755
  simp only [CollatzResearch.WordTrace]
  refine ⟨215072323752071195420931719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143381549168047463613954479 215072323752071195420931719)
  ·
    refine ⟨322608485628106793131397579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215072323752071195420931719 322608485628106793131397579)
    ·
      refine ⟨483912728442160189697096369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322608485628106793131397579 483912728442160189697096369)
      ·
        refine ⟨362934546331620142272822277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483912728442160189697096369 362934546331620142272822277)
        ·
          refine ⟨68050227437178776676154177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362934546331620142272822277 68050227437178776676154177)
          ·
            refine ⟨51037670577884082507115633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68050227437178776676154177 51037670577884082507115633)
            ·
              refine ⟨38278252933413061880336725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51037670577884082507115633 38278252933413061880336725)
              ·
                refine ⟨112143319140858579727549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38278252933413061880336725 112143319140858579727549)
                ·
                  rfl

theorem cell23_5896755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 10].length) (baseStart_5896755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896755 prefixEnd_5896755 := by exact prefixLift 5896755
  have htrace : WordTrace (prefixWord ++ tailWord_5896755) baseStart_5896755 baseEnd_5896755 := by
    simpa [prefixWord, tailWord_5896755, baseEnd_5896755] using wordTrace_append hprefix tailTrace_5896755
  have hstable : (prefixWord ++ tailWord_5896755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896755).length < 2 ^ (prefixWord ++ tailWord_5896755).sum := by decide
  have hdescent : baseEnd_5896755 < baseStart_5896755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896762 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_5896762 : Nat := 118140960795 + 5896762 * 2 ^ 59
def prefixEnd_5896762 : Nat := 4983230072969 + 3 ^ 40 * 5896762 * 2
def baseEnd_5896762 : Nat := 3027873211167763125256291

theorem tailTrace_5896762 : CollatzResearch.WordTrace tailWord_5896762 prefixEnd_5896762 3027873211167763125256291 := by
  unfold tailWord_5896762
  simp only [CollatzResearch.WordTrace]
  refine ⟨53768144765761458904109135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143381719375363890410957693 53768144765761458904109135)
  ·
    refine ⟨80652217148642188356163703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53768144765761458904109135 80652217148642188356163703)
    ·
      refine ⟨120978325722963282534245555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80652217148642188356163703 120978325722963282534245555)
      ·
        refine ⟨181467488584444923801368333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120978325722963282534245555 181467488584444923801368333)
        ·
          refine ⟨68050308219166846425513125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181467488584444923801368333 68050308219166846425513125)
          ·
            refine ⟨12759432791093783704783711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68050308219166846425513125 12759432791093783704783711)
            ·
              refine ⟨19139149186640675557175567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12759432791093783704783711 19139149186640675557175567)
              ·
                refine ⟨28708723779961013335763351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19139149186640675557175567 28708723779961013335763351)
                ·
                  refine ⟨43063085669941520003645027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28708723779961013335763351 43063085669941520003645027)
                  ·
                    refine ⟨64594628504912280005467541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43063085669941520003645027 64594628504912280005467541)
                    ·
                      refine ⟨3027873211167763125256291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64594628504912280005467541 3027873211167763125256291)
                      ·
                        rfl

theorem cell23_5896762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_5896762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896762 prefixEnd_5896762 := by exact prefixLift 5896762
  have htrace : WordTrace (prefixWord ++ tailWord_5896762) baseStart_5896762 baseEnd_5896762 := by
    simpa [prefixWord, tailWord_5896762, baseEnd_5896762] using wordTrace_append hprefix tailTrace_5896762
  have hstable : (prefixWord ++ tailWord_5896762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896762).length < 2 ^ (prefixWord ++ tailWord_5896762).sum := by decide
  have hdescent : baseEnd_5896762 < baseStart_5896762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896783 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 1, 2, 2]
def baseStart_5896783 : Nat := 118140960795 + 5896783 * 2 ^ 59
def prefixEnd_5896783 : Nat := 4983230072969 + 3 ^ 40 * 5896783 * 2
def baseEnd_5896783 : Nat := 3027883994261507543093695

theorem tailTrace_5896783 : CollatzResearch.WordTrace tailWord_5896783 prefixEnd_5896783 3027883994261507543093695 := by
  unfold tailWord_5896783
  simp only [CollatzResearch.WordTrace]
  refine ⟨215073344995969756202951003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143382229997313170801967335 215073344995969756202951003)
  ·
    refine ⟨322610017493954634304426505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215073344995969756202951003 322610017493954634304426505)
    ·
      refine ⟨241957513120465975728319879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322610017493954634304426505 241957513120465975728319879)
      ·
        refine ⟨362936269680698963592479819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241957513120465975728319879 362936269680698963592479819)
        ·
          refine ⟨544404404521048445388719729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362936269680698963592479819 544404404521048445388719729)
          ·
            refine ⟨408303303390786334041539797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544404404521048445388719729 408303303390786334041539797)
            ·
              refine ⟨9569608673221554704098589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 408303303390786334041539797 9569608673221554704098589)
              ·
                refine ⟨3588603252458083014036971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9569608673221554704098589 3588603252458083014036971)
                ·
                  refine ⟨5382904878687124521055457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588603252458083014036971 5382904878687124521055457)
                  ·
                    refine ⟨4037178659015343390791593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5382904878687124521055457 4037178659015343390791593)
                    ·
                      refine ⟨3027883994261507543093695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037178659015343390791593 3027883994261507543093695)
                      ·
                        rfl

theorem cell23_5896783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 2, 2].length) (baseStart_5896783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896783 prefixEnd_5896783 := by exact prefixLift 5896783
  have htrace : WordTrace (prefixWord ++ tailWord_5896783) baseStart_5896783 baseEnd_5896783 := by
    simpa [prefixWord, tailWord_5896783, baseEnd_5896783] using wordTrace_append hprefix tailTrace_5896783
  have hstable : (prefixWord ++ tailWord_5896783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896783).length < 2 ^ (prefixWord ++ tailWord_5896783).sum := by decide
  have hdescent : baseEnd_5896783 < baseStart_5896783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896809 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 3, 3, 2]
def baseStart_5896809 : Nat := 118140960795 + 5896809 * 2 ^ 59
def prefixEnd_5896809 : Nat := 4983230072969 + 3 ^ 40 * 5896809 * 2
def baseEnd_5896809 : Nat := 3027897344758524441368575

theorem tailTrace_5896809 : CollatzResearch.WordTrace tailWord_5896809 prefixEnd_5896809 3027897344758524441368575 := by
  unfold tailWord_5896809
  simp only [CollatzResearch.WordTrace]
  refine ⟨215074293293875562643397481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143382862195917041762264987 215074293293875562643397481)
  ·
    refine ⟨161305719970406671982548111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215074293293875562643397481 161305719970406671982548111)
    ·
      refine ⟨241958579955610007973822167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161305719970406671982548111 241958579955610007973822167)
      ·
        refine ⟨362937869933415011960733251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241958579955610007973822167 362937869933415011960733251)
        ·
          refine ⟨544406804900122517941099877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362937869933415011960733251 544406804900122517941099877)
          ·
            refine ⟨102076275918772972113956227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 544406804900122517941099877 102076275918772972113956227)
            ·
              refine ⟨153114413878159458170934341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102076275918772972113956227 153114413878159458170934341)
              ·
                refine ⟨28708952602154898407050189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153114413878159458170934341 28708952602154898407050189)
                ·
                  refine ⟨10765857225808086902643821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28708952602154898407050189 10765857225808086902643821)
                  ·
                    refine ⟨4037196459678032588491433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10765857225808086902643821 4037196459678032588491433)
                    ·
                      refine ⟨3027897344758524441368575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037196459678032588491433 3027897344758524441368575)
                      ·
                        rfl

theorem cell23_5896809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 3, 2].length) (baseStart_5896809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896809 prefixEnd_5896809 := by exact prefixLift 5896809
  have htrace : WordTrace (prefixWord ++ tailWord_5896809) baseStart_5896809 baseEnd_5896809 := by
    simpa [prefixWord, tailWord_5896809, baseEnd_5896809] using wordTrace_append hprefix tailTrace_5896809
  have hstable : (prefixWord ++ tailWord_5896809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896809).length < 2 ^ (prefixWord ++ tailWord_5896809).sum := by decide
  have hdescent : baseEnd_5896809 < baseStart_5896809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896896 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 5]
def baseStart_5896896 : Nat := 118140960795 + 5896896 * 2 ^ 59
def prefixEnd_5896896 : Nat := 4983230072969 + 3 ^ 40 * 5896896 * 2
def baseEnd_5896896 : Nat := 336438001952829511220075

theorem tailTrace_5896896 : CollatzResearch.WordTrace tailWord_5896896 prefixEnd_5896896 336438001952829511220075 := by
  unfold tailWord_5896896
  simp only [CollatzResearch.WordTrace]
  refine ⟨107538733222280188250907271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143384977629706917667876361 107538733222280188250907271)
  ·
    refine ⟨161308099833420282376360907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107538733222280188250907271 161308099833420282376360907)
    ·
      refine ⟨241962149750130423564541361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161308099833420282376360907 241962149750130423564541361)
      ·
        refine ⟨181471612312597817673406021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241962149750130423564541361 181471612312597817673406021)
        ·
          refine ⟨34025927308612090813763629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181471612312597817673406021 34025927308612090813763629)
          ·
            refine ⟨12759722740729534055161361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34025927308612090813763629 12759722740729534055161361)
            ·
              refine ⟨9569792055547150541371021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12759722740729534055161361 9569792055547150541371021)
              ·
                refine ⟨3588672020830181453014133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9569792055547150541371021 3588672020830181453014133)
                ·
                  refine ⟨336438001952829511220075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3588672020830181453014133 336438001952829511220075)
                  ·
                    rfl

theorem cell23_5896896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 5].length) (baseStart_5896896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896896 prefixEnd_5896896 := by exact prefixLift 5896896
  have htrace : WordTrace (prefixWord ++ tailWord_5896896) baseStart_5896896 baseEnd_5896896 := by
    simpa [prefixWord, tailWord_5896896, baseEnd_5896896] using wordTrace_append hprefix tailTrace_5896896
  have hstable : (prefixWord ++ tailWord_5896896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896896).length < 2 ^ (prefixWord ++ tailWord_5896896).sum := by decide
  have hdescent : baseEnd_5896896 < baseStart_5896896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896929 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_5896929 : Nat := 118140960795 + 5896929 * 2 ^ 59
def prefixEnd_5896929 : Nat := 4983230072969 + 3 ^ 40 * 5896929 * 2
def baseEnd_5896929 : Nat := 3027958962437063971868023

theorem tailTrace_5896929 : CollatzResearch.WordTrace tailWord_5896929 prefixEnd_5896929 3027958962437063971868023 := by
  unfold tailWord_5896929
  simp only [CollatzResearch.WordTrace]
  refine ⟨215078670053440823137765841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143385780035627215425177227 215078670053440823137765841)
  ·
    refine ⟨161309002540080617353324381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215078670053440823137765841 161309002540080617353324381)
    ·
      refine ⟨60490875952530231507496643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161309002540080617353324381 60490875952530231507496643)
      ·
        refine ⟨90736313928795347261244965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60490875952530231507496643 90736313928795347261244965)
        ·
          refine ⟨17013058861649127611483431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90736313928795347261244965 17013058861649127611483431)
          ·
            refine ⟨25519588292473691417225147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17013058861649127611483431 25519588292473691417225147)
            ·
              refine ⟨38279382438710537125837721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25519588292473691417225147 38279382438710537125837721)
              ·
                refine ⟨28709536829032902844378291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38279382438710537125837721 28709536829032902844378291)
                ·
                  refine ⟨43064305243549354266567437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28709536829032902844378291 43064305243549354266567437)
                  ·
                    refine ⟨16149114466331007849962789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43064305243549354266567437 16149114466331007849962789)
                    ·
                      refine ⟨3027958962437063971868023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16149114466331007849962789 3027958962437063971868023)
                      ·
                        rfl

theorem cell23_5896929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_5896929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896929 prefixEnd_5896929 := by exact prefixLift 5896929
  have htrace : WordTrace (prefixWord ++ tailWord_5896929) baseStart_5896929 baseEnd_5896929 := by
    simpa [prefixWord, tailWord_5896929, baseEnd_5896929] using wordTrace_append hprefix tailTrace_5896929
  have hstable : (prefixWord ++ tailWord_5896929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896929).length < 2 ^ (prefixWord ++ tailWord_5896929).sum := by decide
  have hdescent : baseEnd_5896929 < baseStart_5896929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5896952 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 10]
def baseStart_5896952 : Nat := 118140960795 + 5896952 * 2 ^ 59
def prefixEnd_5896952 : Nat := 4983230072969 + 3 ^ 40 * 5896952 * 2
def baseEnd_5896952 : Nat := 336441196943568597986713

theorem tailTrace_5896952 : CollatzResearch.WordTrace tailWord_5896952 prefixEnd_5896952 336441196943568597986713 := by
  unfold tailWord_5896952
  simp only [CollatzResearch.WordTrace]
  refine ⟨107539754466178749032926555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143386339288238332043902073 107539754466178749032926555)
  ·
    refine ⟨161309631699268123549389833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107539754466178749032926555 161309631699268123549389833)
    ·
      refine ⟨120982223774451092662042375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161309631699268123549389833 120982223774451092662042375)
      ·
        refine ⟨181473335661676638993063563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120982223774451092662042375 181473335661676638993063563)
        ·
          refine ⟨272210003492514958489595345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181473335661676638993063563 272210003492514958489595345)
          ·
            refine ⟨204157502619386218867196509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272210003492514958489595345 204157502619386218867196509)
            ·
              refine ⟨76559063482269832075198691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204157502619386218867196509 76559063482269832075198691)
              ·
                refine ⟨114838595223404748112798037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76559063482269832075198691 114838595223404748112798037)
                ·
                  refine ⟨336441196943568597986713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114838595223404748112798037 336441196943568597986713)
                  ·
                    rfl

theorem cell23_5896952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_5896952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5896952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5896952 prefixEnd_5896952 := by exact prefixLift 5896952
  have htrace : WordTrace (prefixWord ++ tailWord_5896952) baseStart_5896952 baseEnd_5896952 := by
    simpa [prefixWord, tailWord_5896952, baseEnd_5896952] using wordTrace_append hprefix tailTrace_5896952
  have hstable : (prefixWord ++ tailWord_5896952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5896952).length < 2 ^ (prefixWord ++ tailWord_5896952).sum := by decide
  have hdescent : baseEnd_5896952 < baseStart_5896952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5896952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897023 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 2, 3, 2]
def baseStart_5897023 : Nat := 118140960795 + 5897023 * 2 ^ 59
def prefixEnd_5897023 : Nat := 4983230072969 + 3 ^ 40 * 5897023 * 2
def baseEnd_5897023 : Nat := 3028007229618586604092591

theorem tailTrace_5897023 : CollatzResearch.WordTrace tailWord_5897023 prefixEnd_5897023 3028007229618586604092591 := by
  unfold tailWord_5897023
  simp only [CollatzResearch.WordTrace]
  refine ⟨215082098515100277191687723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143388065676733518127791815 215082098515100277191687723)
  ·
    refine ⟨322623147772650415787531585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215082098515100277191687723 322623147772650415787531585)
    ·
      refine ⟨241967360829487811840648689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322623147772650415787531585 241967360829487811840648689)
      ·
        refine ⟨181475520622115858880486517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241967360829487811840648689 181475520622115858880486517)
        ·
          refine ⟨17013330058323361770045611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181475520622115858880486517 17013330058323361770045611)
          ·
            refine ⟨25519995087485042655068417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17013330058323361770045611 25519995087485042655068417)
            ·
              refine ⟨19139996315613781991301313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25519995087485042655068417 19139996315613781991301313)
              ·
                refine ⟨14354997236710336493475985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19139996315613781991301313 14354997236710336493475985)
                ·
                  refine ⟨10766247927532752370106989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14354997236710336493475985 10766247927532752370106989)
                  ·
                    refine ⟨4037342972824782138790121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10766247927532752370106989 4037342972824782138790121)
                    ·
                      refine ⟨3028007229618586604092591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037342972824782138790121 3028007229618586604092591)
                      ·
                        rfl

theorem cell23_5897023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_5897023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897023 prefixEnd_5897023 := by exact prefixLift 5897023
  have htrace : WordTrace (prefixWord ++ tailWord_5897023) baseStart_5897023 baseEnd_5897023 := by
    simpa [prefixWord, tailWord_5897023, baseEnd_5897023] using wordTrace_append hprefix tailTrace_5897023
  have hstable : (prefixWord ++ tailWord_5897023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897023).length < 2 ^ (prefixWord ++ tailWord_5897023).sum := by decide
  have hdescent : baseEnd_5897023 < baseStart_5897023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897036 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5897036 : Nat := 118140960795 + 5897036 * 2 ^ 59
def prefixEnd_5897036 : Nat := 4983230072969 + 3 ^ 40 * 5897036 * 2
def baseEnd_5897036 : Nat := 3028013904867095053230031

theorem tailTrace_5897036 : CollatzResearch.WordTrace tailWord_5897036 prefixEnd_5897036 3028013904867095053230031 := by
  unfold tailWord_5897036
  simp only [CollatzResearch.WordTrace]
  refine ⟨107541286332026590205955481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143388381776035453607940641 107541286332026590205955481)
  ·
    refine ⟨80655964749019942654466611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107541286332026590205955481 80655964749019942654466611)
    ·
      refine ⟨120983947123529913981699917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80655964749019942654466611 120983947123529913981699917)
      ·
        refine ⟨45368980171323717743137469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120983947123529913981699917 45368980171323717743137469)
        ·
          refine ⟨17013367564246394153676551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45368980171323717743137469 17013367564246394153676551)
          ·
            refine ⟨25520051346369591230514827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17013367564246394153676551 25520051346369591230514827)
            ·
              refine ⟨38280077019554386845772241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25520051346369591230514827 38280077019554386845772241)
              ·
                refine ⟨28710057764665790134329181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38280077019554386845772241 28710057764665790134329181)
                ·
                  refine ⟨10766271661749671300373443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28710057764665790134329181 10766271661749671300373443)
                  ·
                    refine ⟨16149407492624506950560165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10766271661749671300373443 16149407492624506950560165)
                    ·
                      refine ⟨3028013904867095053230031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16149407492624506950560165 3028013904867095053230031)
                      ·
                        rfl

theorem cell23_5897036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5897036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897036 prefixEnd_5897036 := by exact prefixLift 5897036
  have htrace : WordTrace (prefixWord ++ tailWord_5897036) baseStart_5897036 baseEnd_5897036 := by
    simpa [prefixWord, tailWord_5897036, baseEnd_5897036] using wordTrace_append hprefix tailTrace_5897036
  have hstable : (prefixWord ++ tailWord_5897036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897036).length < 2 ^ (prefixWord ++ tailWord_5897036).sum := by decide
  have hdescent : baseEnd_5897036 < baseStart_5897036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897056 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_5897056 : Nat := 118140960795 + 5897056 * 2 ^ 59
def prefixEnd_5897056 : Nat := 4983230072969 + 3 ^ 40 * 5897056 * 2
def baseEnd_5897056 : Nat := 3028024174480184974979939

theorem tailTrace_5897056 : CollatzResearch.WordTrace tailWord_5897056 prefixEnd_5897056 3028024174480184974979939 := by
  unfold tailWord_5897056
  simp only [CollatzResearch.WordTrace]
  refine ⟨107541651061990361913819511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143388868082653815885092681 107541651061990361913819511)
  ·
    refine ⟨161312476592985542870729267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107541651061990361913819511 161312476592985542870729267)
    ·
      refine ⟨241968714889478314306093901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161312476592985542870729267 241968714889478314306093901)
      ·
        refine ⟨90738268083554367864785213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241968714889478314306093901 90738268083554367864785213)
        ·
          refine ⟨34026850531332887949294455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90738268083554367864785213 34026850531332887949294455)
          ·
            refine ⟨51040275796999331923941683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34026850531332887949294455 51040275796999331923941683)
            ·
              refine ⟨76560413695498997885912525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51040275796999331923941683 76560413695498997885912525)
              ·
                refine ⟨28710155135812124207217197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76560413695498997885912525 28710155135812124207217197)
                ·
                  refine ⟨10766308175929546577706449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28710155135812124207217197 10766308175929546577706449)
                  ·
                    refine ⟨8074731131947159933279837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10766308175929546577706449 8074731131947159933279837)
                    ·
                      refine ⟨3028024174480184974979939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8074731131947159933279837 3028024174480184974979939)
                      ·
                        rfl

theorem cell23_5897056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_5897056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897056 prefixEnd_5897056 := by exact prefixLift 5897056
  have htrace : WordTrace (prefixWord ++ tailWord_5897056) baseStart_5897056 baseEnd_5897056 := by
    simpa [prefixWord, tailWord_5897056, baseEnd_5897056] using wordTrace_append hprefix tailTrace_5897056
  have hstable : (prefixWord ++ tailWord_5897056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897056).length < 2 ^ (prefixWord ++ tailWord_5897056).sum := by decide
  have hdescent : baseEnd_5897056 < baseStart_5897056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897070 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5897070 : Nat := 118140960795 + 5897070 * 2 ^ 59
def prefixEnd_5897070 : Nat := 4983230072969 + 3 ^ 40 * 5897070 * 2
def baseEnd_5897070 : Nat := 3028031363209347920204875

theorem tailTrace_5897070 : CollatzResearch.WordTrace tailWord_5897070 prefixEnd_5897070 3028031363209347920204875 := by
  unfold tailWord_5897070
  simp only [CollatzResearch.WordTrace]
  refine ⟨26885476593241250527331083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143389208497286669479099109 26885476593241250527331083)
  ·
    refine ⟨40328214889861875790996625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26885476593241250527331083 40328214889861875790996625)
    ·
      refine ⟨30246161167396406843247469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40328214889861875790996625 30246161167396406843247469)
      ·
        refine ⟨11342310437773652566217801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30246161167396406843247469 11342310437773652566217801)
        ·
          refine ⟨8506732828330239424663351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11342310437773652566217801 8506732828330239424663351)
          ·
            refine ⟨12760099242495359136995027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8506732828330239424663351 12760099242495359136995027)
            ·
              refine ⟨19140148863743038705492541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12760099242495359136995027 19140148863743038705492541)
              ·
                refine ⟨7177555823903639514559703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19140148863743038705492541 7177555823903639514559703)
                ·
                  refine ⟨10766333735855459271839555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177555823903639514559703 10766333735855459271839555)
                  ·
                    refine ⟨16149500603783188907759333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10766333735855459271839555 16149500603783188907759333)
                    ·
                      refine ⟨3028031363209347920204875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16149500603783188907759333 3028031363209347920204875)
                      ·
                        rfl

theorem cell23_5897070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5897070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897070 prefixEnd_5897070 := by exact prefixLift 5897070
  have htrace : WordTrace (prefixWord ++ tailWord_5897070) baseStart_5897070 baseEnd_5897070 := by
    simpa [prefixWord, tailWord_5897070, baseEnd_5897070] using wordTrace_append hprefix tailTrace_5897070
  have hstable : (prefixWord ++ tailWord_5897070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897070).length < 2 ^ (prefixWord ++ tailWord_5897070).sum := by decide
  have hdescent : baseEnd_5897070 < baseStart_5897070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897073 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_5897073 : Nat := 118140960795 + 5897073 * 2 ^ 59
def prefixEnd_5897073 : Nat := 4983230072969 + 3 ^ 40 * 5897073 * 2
def baseEnd_5897073 : Nat := 3028032903651311408467361

theorem tailTrace_5897073 : CollatzResearch.WordTrace tailWord_5897073 prefixEnd_5897073 3028032903651311408467361 := by
  unfold tailWord_5897073
  simp only [CollatzResearch.WordTrace]
  refine ⟨215083922164919135731007873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143389281443279423820671915 215083922164919135731007873)
  ·
    refine ⟨161312941623689351798255905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215083922164919135731007873 161312941623689351798255905)
    ·
      refine ⟨120984706217767013848691929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161312941623689351798255905 120984706217767013848691929)
      ·
        refine ⟨90738529663325260386518947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120984706217767013848691929 90738529663325260386518947)
        ·
          refine ⟨136107794494987890579778421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90738529663325260386518947 136107794494987890579778421)
          ·
            refine ⟨12760105733905114741854227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136107794494987890579778421 12760105733905114741854227)
            ·
              refine ⟨19140158600857672112781341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12760105733905114741854227 19140158600857672112781341)
              ·
                refine ⟨7177559475321627042293003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19140158600857672112781341 7177559475321627042293003)
                ·
                  refine ⟨10766339212982440563439505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177559475321627042293003 10766339212982440563439505)
                  ·
                    refine ⟨8074754409736830422579629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10766339212982440563439505 8074754409736830422579629)
                    ·
                      refine ⟨3028032903651311408467361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8074754409736830422579629 3028032903651311408467361)
                      ·
                        rfl

theorem cell23_5897073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_5897073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897073 prefixEnd_5897073 := by exact prefixLift 5897073
  have htrace : WordTrace (prefixWord ++ tailWord_5897073) baseStart_5897073 baseEnd_5897073 := by
    simpa [prefixWord, tailWord_5897073, baseEnd_5897073] using wordTrace_append hprefix tailTrace_5897073
  have hstable : (prefixWord ++ tailWord_5897073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897073).length < 2 ^ (prefixWord ++ tailWord_5897073).sum := by decide
  have hdescent : baseEnd_5897073 < baseStart_5897073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897110 : List Nat := [5, 3, 1, 1, 1, 2, 1, 9]
def baseStart_5897110 : Nat := 118140960795 + 5897110 * 2 ^ 59
def prefixEnd_5897110 : Nat := 4983230072969 + 3 ^ 40 * 5897110 * 2
def baseEnd_5897110 : Nat := 112150070460575102359433

theorem tailTrace_5897110 : CollatzResearch.WordTrace tailWord_5897110 prefixEnd_5897110 112150070460575102359433 := by
  unfold tailWord_5897110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13442829479111568190631549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143390181110523394033403189 13442829479111568190631549)
  ·
    refine ⟨5041061054666838071486831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13442829479111568190631549 5041061054666838071486831)
    ·
      refine ⟨7561591582000257107230247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5041061054666838071486831 7561591582000257107230247)
      ·
        refine ⟨11342387373000385660845371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561591582000257107230247 11342387373000385660845371)
        ·
          refine ⟨17013581059500578491268057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11342387373000385660845371 17013581059500578491268057)
          ·
            refine ⟨12760185794625433868451043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17013581059500578491268057 12760185794625433868451043)
            ·
              refine ⟨19140278691938150802676565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12760185794625433868451043 19140278691938150802676565)
              ·
                refine ⟨112150070460575102359433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19140278691938150802676565 112150070460575102359433)
                ·
                  rfl

theorem cell23_5897110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_5897110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897110 prefixEnd_5897110 := by exact prefixLift 5897110
  have htrace : WordTrace (prefixWord ++ tailWord_5897110) baseStart_5897110 baseEnd_5897110 := by
    simpa [prefixWord, tailWord_5897110, baseEnd_5897110] using wordTrace_append hprefix tailTrace_5897110
  have hstable : (prefixWord ++ tailWord_5897110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897110).length < 2 ^ (prefixWord ++ tailWord_5897110).sum := by decide
  have hdescent : baseEnd_5897110 < baseStart_5897110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897139 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_5897139 : Nat := 118140960795 + 5897139 * 2 ^ 59
def prefixEnd_5897139 : Nat := 4983230072969 + 3 ^ 40 * 5897139 * 2
def baseEnd_5897139 : Nat := 3028066793374508150242057

theorem tailTrace_5897139 : CollatzResearch.WordTrace tailWord_5897139 prefixEnd_5897139 3028066793374508150242057 := by
  unfold tailWord_5897139
  simp only [CollatzResearch.WordTrace]
  refine ⟨215086329382680029002910471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143390886255120019335273647 215086329382680029002910471)
  ·
    refine ⟨322629494074020043504365707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215086329382680029002910471 322629494074020043504365707)
    ·
      refine ⟨483944241111030065256548561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322629494074020043504365707 483944241111030065256548561)
      ·
        refine ⟨362958180833272548942411421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483944241111030065256548561 362958180833272548942411421)
        ·
          refine ⟨136109317812477205853404283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362958180833272548942411421 136109317812477205853404283)
          ·
            refine ⟨204163976718715808780106425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136109317812477205853404283 204163976718715808780106425)
            ·
              refine ⟨153122982539036856585079819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204163976718715808780106425 153122982539036856585079819)
              ·
                refine ⟨229684473808555284877619729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153122982539036856585079819 229684473808555284877619729)
                ·
                  refine ⟨172263355356416463658214797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229684473808555284877619729 172263355356416463658214797)
                  ·
                    refine ⟨64598758258656173871830549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172263355356416463658214797 64598758258656173871830549)
                    ·
                      refine ⟨3028066793374508150242057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64598758258656173871830549 3028066793374508150242057)
                      ·
                        rfl

theorem cell23_5897139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_5897139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897139 prefixEnd_5897139 := by exact prefixLift 5897139
  have htrace : WordTrace (prefixWord ++ tailWord_5897139) baseStart_5897139 baseEnd_5897139 := by
    simpa [prefixWord, tailWord_5897139, baseEnd_5897139] using wordTrace_append hprefix tailTrace_5897139
  have hstable : (prefixWord ++ tailWord_5897139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897139).length < 2 ^ (prefixWord ++ tailWord_5897139).sum := by decide
  have hdescent : baseEnd_5897139 < baseStart_5897139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897146 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_5897146 : Nat := 118140960795 + 5897146 * 2 ^ 59
def prefixEnd_5897146 : Nat := 4983230072969 + 3 ^ 40 * 5897146 * 2
def baseEnd_5897146 : Nat := 3028070387739089622854525

theorem tailTrace_5897146 : CollatzResearch.WordTrace tailWord_5897146 prefixEnd_5897146 3028070387739089622854525 := by
  unfold tailWord_5897146
  simp only [CollatzResearch.WordTrace]
  refine ⟨53771646173413667299603823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143391056462436446132276861 53771646173413667299603823)
  ·
    refine ⟨80657469260120500949405735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53771646173413667299603823 80657469260120500949405735)
    ·
      refine ⟨120986203890180751424108603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80657469260120500949405735 120986203890180751424108603)
      ·
        refine ⟨181479305835271127136162905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120986203890180751424108603 181479305835271127136162905)
        ·
          refine ⟨136109479376453345352122179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181479305835271127136162905 136109479376453345352122179)
          ·
            refine ⟨204164219064680018028183269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136109479376453345352122179 204164219064680018028183269)
            ·
              refine ⟨38280791074627503380284363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204164219064680018028183269 38280791074627503380284363)
              ·
                refine ⟨57421186611941255070426545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38280791074627503380284363 57421186611941255070426545)
                ·
                  refine ⟨43065889958955941302819909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57421186611941255070426545 43065889958955941302819909)
                  ·
                    refine ⟨8074854367304238994278733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43065889958955941302819909 8074854367304238994278733)
                    ·
                      refine ⟨3028070387739089622854525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8074854367304238994278733 3028070387739089622854525)
                      ·
                        rfl

theorem cell23_5897146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_5897146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897146 prefixEnd_5897146 := by exact prefixLift 5897146
  have htrace : WordTrace (prefixWord ++ tailWord_5897146) baseStart_5897146 baseEnd_5897146 := by
    simpa [prefixWord, tailWord_5897146, baseEnd_5897146] using wordTrace_append hprefix tailTrace_5897146
  have hstable : (prefixWord ++ tailWord_5897146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897146).length < 2 ^ (prefixWord ++ tailWord_5897146).sum := by decide
  have hdescent : baseEnd_5897146 < baseStart_5897146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897158 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5897158 : Nat := 118140960795 + 5897158 * 2 ^ 59
def prefixEnd_5897158 : Nat := 4983230072969 + 3 ^ 40 * 5897158 * 2
def baseEnd_5897158 : Nat := 3028076549506943575904471

theorem tailTrace_5897158 : CollatzResearch.WordTrace tailWord_5897158 prefixEnd_5897158 3028076549506943575904471 := by
  unfold tailWord_5897158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721469449050349851495379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143391348246407463498568085 6721469449050349851495379)
  ·
    refine ⟨10082204173575524777243069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721469449050349851495379 10082204173575524777243069)
    ·
      refine ⟨3780826565090821791466151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10082204173575524777243069 3780826565090821791466151)
      ·
        refine ⟨5671239847636232687199227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780826565090821791466151 5671239847636232687199227)
        ·
          refine ⟨8506859771454349030798841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671239847636232687199227 8506859771454349030798841)
          ·
            refine ⟨6380144828590761773099131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8506859771454349030798841 6380144828590761773099131)
            ·
              refine ⟨9570217242886142659648697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6380144828590761773099131 9570217242886142659648697)
              ·
                refine ⟨7177662932164606994736523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9570217242886142659648697 7177662932164606994736523)
                ·
                  refine ⟨10766494398246910492104785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177662932164606994736523 10766494398246910492104785)
                  ·
                    refine ⟨8074870798685182869078589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10766494398246910492104785 8074870798685182869078589)
                    ·
                      refine ⟨3028076549506943575904471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8074870798685182869078589 3028076549506943575904471)
                      ·
                        rfl

theorem cell23_5897158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5897158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897158 prefixEnd_5897158 := by exact prefixLift 5897158
  have htrace : WordTrace (prefixWord ++ tailWord_5897158) baseStart_5897158 baseEnd_5897158 := by
    simpa [prefixWord, tailWord_5897158, baseEnd_5897158] using wordTrace_append hprefix tailTrace_5897158
  have hstable : (prefixWord ++ tailWord_5897158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897158).length < 2 ^ (prefixWord ++ tailWord_5897158).sum := by decide
  have hdescent : baseEnd_5897158 < baseStart_5897158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 13]
def baseStart_5897179 : Nat := 118140960795 + 5897179 * 2 ^ 59
def prefixEnd_5897179 : Nat := 4983230072969 + 3 ^ 40 * 5897179 * 2
def baseEnd_5897179 : Nat := 1009362444200229331247291

theorem tailTrace_5897179 : CollatzResearch.WordTrace tailWord_5897179 prefixEnd_5897179 1009362444200229331247291 := by
  unfold tailWord_5897179
  simp only [CollatzResearch.WordTrace]
  refine ⟨215087788302535115834366591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143391858868356743889577727 215087788302535115834366591)
  ·
    refine ⟨322631682453802673751549887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215087788302535115834366591 322631682453802673751549887)
    ·
      refine ⟨483947523680704010627324831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322631682453802673751549887 483947523680704010627324831)
      ·
        refine ⟨725921285521056015940987247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483947523680704010627324831 725921285521056015940987247)
        ·
          refine ⟨1088881928281584023911480871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725921285521056015940987247 1088881928281584023911480871)
          ·
            refine ⟨1633322892422376035867221307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088881928281584023911480871 1633322892422376035867221307)
            ·
              refine ⟨2449984338633564053800831961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633322892422376035867221307 2449984338633564053800831961)
              ·
                refine ⟨1837488253975173040350623971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2449984338633564053800831961 1837488253975173040350623971)
                ·
                  refine ⟨2756232380962759560525935957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837488253975173040350623971 2756232380962759560525935957)
                  ·
                    refine ⟨1009362444200229331247291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 2756232380962759560525935957 1009362444200229331247291)
                    ·
                      rfl

theorem cell23_5897179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_5897179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897179 prefixEnd_5897179 := by exact prefixLift 5897179
  have htrace : WordTrace (prefixWord ++ tailWord_5897179) baseStart_5897179 baseEnd_5897179 := by
    simpa [prefixWord, tailWord_5897179, baseEnd_5897179] using wordTrace_append hprefix tailTrace_5897179
  have hstable : (prefixWord ++ tailWord_5897179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897179).length < 2 ^ (prefixWord ++ tailWord_5897179).sum := by decide
  have hdescent : baseEnd_5897179 < baseStart_5897179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897204 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5897204 : Nat := 118140960795 + 5897204 * 2 ^ 59
def prefixEnd_5897204 : Nat := 4983230072969 + 3 ^ 40 * 5897204 * 2
def baseEnd_5897204 : Nat := 1009366723205683465309753

theorem tailTrace_5897204 : CollatzResearch.WordTrace tailWord_5897204 prefixEnd_5897204 1009366723205683465309753 := by
  unfold tailWord_5897204
  simp only [CollatzResearch.WordTrace]
  refine ⟨107544350063722272552013333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143392466751629696736017777 107544350063722272552013333)
  ·
    refine ⟨5041141409236981525875625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107544350063722272552013333 5041141409236981525875625)
    ·
      refine ⟨3780856056927736144406719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5041141409236981525875625 3780856056927736144406719)
      ·
        refine ⟨5671284085391604216610079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780856056927736144406719 5671284085391604216610079)
        ·
          refine ⟨8506926128087406324915119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671284085391604216610079 8506926128087406324915119)
          ·
            refine ⟨12760389192131109487372679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8506926128087406324915119 12760389192131109487372679)
            ·
              refine ⟨19140583788196664231059019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12760389192131109487372679 19140583788196664231059019)
              ·
                refine ⟨28710875682294996346588529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19140583788196664231059019 28710875682294996346588529)
                ·
                  refine ⟨21533156761721247259941397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28710875682294996346588529 21533156761721247259941397)
                  ·
                    refine ⟨1009366723205683465309753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21533156761721247259941397 1009366723205683465309753)
                    ·
                      rfl

theorem cell23_5897204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5897204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897204 prefixEnd_5897204 := by exact prefixLift 5897204
  have htrace : WordTrace (prefixWord ++ tailWord_5897204) baseStart_5897204 baseEnd_5897204 := by
    simpa [prefixWord, tailWord_5897204, baseEnd_5897204] using wordTrace_append hprefix tailTrace_5897204
  have hstable : (prefixWord ++ tailWord_5897204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897204).length < 2 ^ (prefixWord ++ tailWord_5897204).sum := by decide
  have hdescent : baseEnd_5897204 < baseStart_5897204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897230 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_5897230 : Nat := 118140960795 + 5897230 * 2 ^ 59
def prefixEnd_5897230 : Nat := 4983230072969 + 3 ^ 40 * 5897230 * 2
def baseEnd_5897230 : Nat := 1009371173371355764734713

theorem tailTrace_5897230 : CollatzResearch.WordTrace tailWord_5897230 prefixEnd_5897230 1009371173371355764734713 := by
  unfold tailWord_5897230
  simp only [CollatzResearch.WordTrace]
  refine ⟨26886206053168793943059143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143393098950233567696315429 26886206053168793943059143)
  ·
    refine ⟨40329309079753190914588715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26886206053168793943059143 40329309079753190914588715)
    ·
      refine ⟨60493963619629786371883073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40329309079753190914588715 60493963619629786371883073)
      ·
        refine ⟨45370472714722339778912305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60493963619629786371883073 45370472714722339778912305)
        ·
          refine ⟨34027854536041754834184229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45370472714722339778912305 34027854536041754834184229)
          ·
            refine ⟨6380222725507829031409543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34027854536041754834184229 6380222725507829031409543)
            ·
              refine ⟨9570334088261743547114315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6380222725507829031409543 9570334088261743547114315)
              ·
                refine ⟨14355501132392615320671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9570334088261743547114315 14355501132392615320671473)
                ·
                  refine ⟨10766625849294461490503605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14355501132392615320671473 10766625849294461490503605)
                  ·
                    refine ⟨1009371173371355764734713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10766625849294461490503605 1009371173371355764734713)
                    ·
                      rfl

theorem cell23_5897230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_5897230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897230 prefixEnd_5897230 := by exact prefixLift 5897230
  have htrace : WordTrace (prefixWord ++ tailWord_5897230) baseStart_5897230 baseEnd_5897230 := by
    simpa [prefixWord, tailWord_5897230, baseEnd_5897230] using wordTrace_append hprefix tailTrace_5897230
  have hstable : (prefixWord ++ tailWord_5897230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897230).length < 2 ^ (prefixWord ++ tailWord_5897230).sum := by decide
  have hdescent : baseEnd_5897230 < baseStart_5897230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897250 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_5897250 : Nat := 118140960795 + 5897250 * 2 ^ 59
def prefixEnd_5897250 : Nat := 4983230072969 + 3 ^ 40 * 5897250 * 2
def baseEnd_5897250 : Nat := 3028123789727157215954047

theorem tailTrace_5897250 : CollatzResearch.WordTrace tailWord_5897250 prefixEnd_5897250 3028123789727157215954047 := by
  unfold tailWord_5897250
  simp only [CollatzResearch.WordTrace]
  refine ⟨53772594471319473740050301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143393585256851929973467469 53772594471319473740050301)
  ·
    refine ⟨20164722926744802652518863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53772594471319473740050301 20164722926744802652518863)
    ·
      refine ⟨30247084390117203978778295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20164722926744802652518863 30247084390117203978778295)
      ·
        refine ⟨45370626585175805968167443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30247084390117203978778295 45370626585175805968167443)
        ·
          refine ⟨68055939877763708952251165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45370626585175805968167443 68055939877763708952251165)
          ·
            refine ⟨25520977454161390857094187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68055939877763708952251165 25520977454161390857094187)
            ·
              refine ⟨38281466181242086285641281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25520977454161390857094187 38281466181242086285641281)
              ·
                refine ⟨28711099635931564714230961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38281466181242086285641281 28711099635931564714230961)
                ·
                  refine ⟨21533324726948673535673221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28711099635931564714230961 21533324726948673535673221)
                  ·
                    refine ⟨4037498386302876287938729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21533324726948673535673221 4037498386302876287938729)
                    ·
                      refine ⟨3028123789727157215954047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037498386302876287938729 3028123789727157215954047)
                      ·
                        rfl

theorem cell23_5897250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_5897250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897250 prefixEnd_5897250 := by exact prefixLift 5897250
  have htrace : WordTrace (prefixWord ++ tailWord_5897250) baseStart_5897250 baseEnd_5897250 := by
    simpa [prefixWord, tailWord_5897250, baseEnd_5897250] using wordTrace_append hprefix tailTrace_5897250
  have hstable : (prefixWord ++ tailWord_5897250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897250).length < 2 ^ (prefixWord ++ tailWord_5897250).sum := by decide
  have hdescent : baseEnd_5897250 < baseStart_5897250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897253 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_5897253 : Nat := 118140960795 + 5897253 * 2 ^ 59
def prefixEnd_5897253 : Nat := 4983230072969 + 3 ^ 40 * 5897253 * 2
def baseEnd_5897253 : Nat := 3028125330169120704216533

theorem tailTrace_5897253 : CollatzResearch.WordTrace tailWord_5897253 prefixEnd_5897253 3028125330169120704216533 := by
  unfold tailWord_5897253
  simp only [CollatzResearch.WordTrace]
  refine ⟨215090487304267026472560413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143393658202844684315040275 215090487304267026472560413)
  ·
    refine ⟨80658932739100134927210155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215090487304267026472560413 80658932739100134927210155)
    ·
      refine ⟨120988399108650202390815233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80658932739100134927210155 120988399108650202390815233)
      ·
        refine ⟨90741299331487651793111425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120988399108650202390815233 90741299331487651793111425)
        ·
          refine ⟨68055974498615738844833569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90741299331487651793111425 68055974498615738844833569)
          ·
            refine ⟨51041980873961804133625177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68055974498615738844833569 51041980873961804133625177)
            ·
              refine ⟨38281485655471353100218883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51041980873961804133625177 38281485655471353100218883)
              ·
                refine ⟨57422228483207029650328325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38281485655471353100218883 57422228483207029650328325)
                ·
                  refine ⟨10766667840601318059436561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57422228483207029650328325 10766667840601318059436561)
                  ·
                    refine ⟨8075000880450988544577421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10766667840601318059436561 8075000880450988544577421)
                    ·
                      refine ⟨3028125330169120704216533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075000880450988544577421 3028125330169120704216533)
                      ·
                        rfl

theorem cell23_5897253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_5897253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897253 prefixEnd_5897253 := by exact prefixLift 5897253
  have htrace : WordTrace (prefixWord ++ tailWord_5897253) baseStart_5897253 baseEnd_5897253 := by
    simpa [prefixWord, tailWord_5897253, baseEnd_5897253] using wordTrace_append hprefix tailTrace_5897253
  have hstable : (prefixWord ++ tailWord_5897253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897253).length < 2 ^ (prefixWord ++ tailWord_5897253).sum := by decide
  have hdescent : baseEnd_5897253 < baseStart_5897253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897260 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_5897260 : Nat := 118140960795 + 5897260 * 2 ^ 59
def prefixEnd_5897260 : Nat := 4983230072969 + 3 ^ 40 * 5897260 * 2
def baseEnd_5897260 : Nat := 1009376308177900725609667

theorem tailTrace_5897260 : CollatzResearch.WordTrace tailWord_5897260 prefixEnd_5897260 1009376308177900725609667 := by
  unfold tailWord_5897260
  simp only [CollatzResearch.WordTrace]
  refine ⟨107545371307620833334032617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143393828410161111112043489 107545371307620833334032617)
  ·
    refine ⟨80659028480715625000524463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107545371307620833334032617 80659028480715625000524463)
    ·
      refine ⟨120988542721073437500786695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80659028480715625000524463 120988542721073437500786695)
      ·
        refine ⟨181482814081610156251180043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120988542721073437500786695 181482814081610156251180043)
        ·
          refine ⟨272224221122415234376770065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181482814081610156251180043 272224221122415234376770065)
          ·
            refine ⟨204168165841811425782577549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272224221122415234376770065 204168165841811425782577549)
            ·
              refine ⟨76563062190679284668466581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204168165841811425782577549 76563062190679284668466581)
              ·
                refine ⟨3588893540188091468834371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76563062190679284668466581 3588893540188091468834371)
                ·
                  refine ⟨5383340310282137203251557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588893540188091468834371 5383340310282137203251557)
                  ·
                    refine ⟨1009376308177900725609667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383340310282137203251557 1009376308177900725609667)
                    ·
                      rfl

theorem cell23_5897260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_5897260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897260 prefixEnd_5897260 := by exact prefixLift 5897260
  have htrace : WordTrace (prefixWord ++ tailWord_5897260) baseStart_5897260 baseEnd_5897260 := by
    simpa [prefixWord, tailWord_5897260, baseEnd_5897260] using wordTrace_append hprefix tailTrace_5897260
  have hstable : (prefixWord ++ tailWord_5897260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897260).length < 2 ^ (prefixWord ++ tailWord_5897260).sum := by decide
  have hdescent : baseEnd_5897260 < baseStart_5897260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897270 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_5897270 : Nat := 118140960795 + 5897270 * 2 ^ 59
def prefixEnd_5897270 : Nat := 4983230072969 + 3 ^ 40 * 5897270 * 2
def baseEnd_5897270 : Nat := 3028134059340247137703955

theorem tailTrace_5897270 : CollatzResearch.WordTrace tailWord_5897270 prefixEnd_5897270 3028134059340247137703955 := by
  unfold tailWord_5897270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13443194209075339898495579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143394071563470292250619509 13443194209075339898495579)
  ·
    refine ⟨20164791313613009847743369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13443194209075339898495579 20164791313613009847743369)
    ·
      refine ⟨15123593485209757385807527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20164791313613009847743369 15123593485209757385807527)
      ·
        refine ⟨22685390227814636078711291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15123593485209757385807527 22685390227814636078711291)
        ·
          refine ⟨34028085341721954118066937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22685390227814636078711291 34028085341721954118066937)
          ·
            refine ⟨25521064006291465588550203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34028085341721954118066937 25521064006291465588550203)
            ·
              refine ⟨38281596009437198382825305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25521064006291465588550203 38281596009437198382825305)
              ·
                refine ⟨28711197007077898787118979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38281596009437198382825305 28711197007077898787118979)
                ·
                  refine ⟨43066795510616848180678469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28711197007077898787118979 43066795510616848180678469)
                  ·
                    refine ⟨8075024158240659033877213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43066795510616848180678469 8075024158240659033877213)
                    ·
                      refine ⟨3028134059340247137703955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075024158240659033877213 3028134059340247137703955)
                      ·
                        rfl

theorem cell23_5897270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_5897270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897270 prefixEnd_5897270 := by exact prefixLift 5897270
  have htrace : WordTrace (prefixWord ++ tailWord_5897270) baseStart_5897270 baseEnd_5897270 := by
    simpa [prefixWord, tailWord_5897270, baseEnd_5897270] using wordTrace_append hprefix tailTrace_5897270
  have hstable : (prefixWord ++ tailWord_5897270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897270).length < 2 ^ (prefixWord ++ tailWord_5897270).sum := by decide
  have hdescent : baseEnd_5897270 < baseStart_5897270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897300 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_5897300 : Nat := 118140960795 + 5897300 * 2 ^ 59
def prefixEnd_5897300 : Nat := 4983230072969 + 3 ^ 40 * 5897300 * 2
def baseEnd_5897300 : Nat := 3028149463759882020328817

theorem tailTrace_5897300 : CollatzResearch.WordTrace tailWord_5897300 prefixEnd_5897300 3028149463759882020328817 := by
  unfold tailWord_5897300
  simp only [CollatzResearch.WordTrace]
  refine ⟨107546100767548376749760677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143394801023397835666347569 107546100767548376749760677)
  ·
    refine ⟨20164893893915320640580127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107546100767548376749760677 20164893893915320640580127)
    ·
      refine ⟨30247340840872980960870191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20164893893915320640580127 30247340840872980960870191)
      ·
        refine ⟨45371011261309471441305287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30247340840872980960870191 45371011261309471441305287)
        ·
          refine ⟨68056516891964207161957931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45371011261309471441305287 68056516891964207161957931)
          ·
            refine ⟨102084775337946310742936897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68056516891964207161957931 102084775337946310742936897)
            ·
              refine ⟨76563581503459733057202673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102084775337946310742936897 76563581503459733057202673)
              ·
                refine ⟨57422686127594799792902005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76563581503459733057202673 57422686127594799792902005)
                ·
                  refine ⟨5383376824462012480584563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57422686127594799792902005 5383376824462012480584563)
                  ·
                    refine ⟨8075065236693018720876845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5383376824462012480584563 8075065236693018720876845)
                    ·
                      refine ⟨3028149463759882020328817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075065236693018720876845 3028149463759882020328817)
                      ·
                        rfl

theorem cell23_5897300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_5897300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897300 prefixEnd_5897300 := by exact prefixLift 5897300
  have htrace : WordTrace (prefixWord ++ tailWord_5897300) baseStart_5897300 baseEnd_5897300 := by
    simpa [prefixWord, tailWord_5897300, baseEnd_5897300] using wordTrace_append hprefix tailTrace_5897300
  have hstable : (prefixWord ++ tailWord_5897300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897300).length < 2 ^ (prefixWord ++ tailWord_5897300).sum := by decide
  have hdescent : baseEnd_5897300 < baseStart_5897300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897337 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 1, 5]
def baseStart_5897337 : Nat := 118140960795 + 5897337 * 2 ^ 59
def prefixEnd_5897337 : Nat := 4983230072969 + 3 ^ 40 * 5897337 * 2
def baseEnd_5897337 : Nat := 1009389487514699458522049

theorem tailTrace_5897337 : CollatzResearch.WordTrace tailWord_5897337 prefixEnd_5897337 1009389487514699458522049 := by
  unfold tailWord_5897337
  simp only [CollatzResearch.WordTrace]
  refine ⟨215093551035962708818618265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143395700690641805879078843 215093551035962708818618265)
  ·
    refine ⟨161320163276972031613963699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215093551035962708818618265 161320163276972031613963699)
    ·
      refine ⟨241980244915458047420945549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161320163276972031613963699 241980244915458047420945549)
      ·
        refine ⟨90742591843296767782854581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241980244915458047420945549 90742591843296767782854581)
        ·
          refine ⟨8507117985309071979642617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90742591843296767782854581 8507117985309071979642617)
          ·
            refine ⟨6380338488981803984731963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8507117985309071979642617 6380338488981803984731963)
            ·
              refine ⟨9570507733472705977097945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6380338488981803984731963 9570507733472705977097945)
              ·
                refine ⟨7177880800104529482823459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9570507733472705977097945 7177880800104529482823459)
                ·
                  refine ⟨10766821200156794224235189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177880800104529482823459 10766821200156794224235189)
                  ·
                    refine ⟨1009389487514699458522049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10766821200156794224235189 1009389487514699458522049)
                    ·
                      rfl

theorem cell23_5897337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_5897337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897337 prefixEnd_5897337 := by exact prefixLift 5897337
  have htrace : WordTrace (prefixWord ++ tailWord_5897337) baseStart_5897337 baseEnd_5897337 := by
    simpa [prefixWord, tailWord_5897337, baseEnd_5897337] using wordTrace_append hprefix tailTrace_5897337
  have hstable : (prefixWord ++ tailWord_5897337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897337).length < 2 ^ (prefixWord ++ tailWord_5897337).sum := by decide
  have hdescent : baseEnd_5897337 < baseStart_5897337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897353 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_5897353 : Nat := 118140960795 + 5897353 * 2 ^ 59
def prefixEnd_5897353 : Nat := 4983230072969 + 3 ^ 40 * 5897353 * 2
def baseEnd_5897353 : Nat := 3028176678234570312966073

theorem tailTrace_5897353 : CollatzResearch.WordTrace tailWord_5897353 prefixEnd_5897353 3028176678234570312966073 := by
  unfold tailWord_5897353
  simp only [CollatzResearch.WordTrace]
  refine ⟨215094134603904743551200713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143396089735936495700800475 215094134603904743551200713)
  ·
    refine ⟨161320600952928557663400535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215094134603904743551200713 161320600952928557663400535)
    ·
      refine ⟨241980901429392836495100803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161320600952928557663400535 241980901429392836495100803)
      ·
        refine ⟨362971352144089254742651205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241980901429392836495100803 362971352144089254742651205)
        ·
          refine ⟨68057128527016735264247101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362971352144089254742651205 68057128527016735264247101)
          ·
            refine ⟨25521423197631275724092663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68057128527016735264247101 25521423197631275724092663)
            ·
              refine ⟨38282134796446913586138995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25521423197631275724092663 38282134796446913586138995)
              ·
                refine ⟨57423202194670370379208493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38282134796446913586138995 57423202194670370379208493)
                ·
                  refine ⟨21533700823001388892203185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57423202194670370379208493 21533700823001388892203185)
                  ·
                    refine ⟨16150275617251041669152389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21533700823001388892203185 16150275617251041669152389)
                    ·
                      refine ⟨3028176678234570312966073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16150275617251041669152389 3028176678234570312966073)
                      ·
                        rfl

theorem cell23_5897353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_5897353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897353 prefixEnd_5897353 := by exact prefixLift 5897353
  have htrace : WordTrace (prefixWord ++ tailWord_5897353) baseStart_5897353 baseEnd_5897353 := by
    simpa [prefixWord, tailWord_5897353, baseEnd_5897353] using wordTrace_append hprefix tailTrace_5897353
  have hstable : (prefixWord ++ tailWord_5897353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897353).length < 2 ^ (prefixWord ++ tailWord_5897353).sum := by decide
  have hdescent : baseEnd_5897353 < baseStart_5897353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897367 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 2, 4]
def baseStart_5897367 : Nat := 118140960795 + 5897367 * 2 ^ 59
def prefixEnd_5897367 : Nat := 4983230072969 + 3 ^ 40 * 5897367 * 2
def baseEnd_5897367 : Nat := 1009394622321244419397003

theorem tailTrace_5897367 : CollatzResearch.WordTrace tailWord_5897367 prefixEnd_5897367 1009394622321244419397003 := by
  unfold tailWord_5897367
  simp only [CollatzResearch.WordTrace]
  refine ⟨215094645225854023942210355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143396430150569349294806903 215094645225854023942210355)
  ·
    refine ⟨322641967838781035913315533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215094645225854023942210355 322641967838781035913315533)
    ·
      refine ⟨120990737939542888467493325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322641967838781035913315533 120990737939542888467493325)
      ·
        refine ⟨45371526727328583175309997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120990737939542888467493325 45371526727328583175309997)
        ·
          refine ⟨17014322522748218690741249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45371526727328583175309997 17014322522748218690741249)
          ·
            refine ⟨12760741892061164018055937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17014322522748218690741249 12760741892061164018055937)
            ·
              refine ⟨9570556419045873013541953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12760741892061164018055937 9570556419045873013541953)
              ·
                refine ⟨7177917314284404760156465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9570556419045873013541953 7177917314284404760156465)
                ·
                  refine ⟨5383437985713303570117349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7177917314284404760156465 5383437985713303570117349)
                  ·
                    refine ⟨1009394622321244419397003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383437985713303570117349 1009394622321244419397003)
                    ·
                      rfl

theorem cell23_5897367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_5897367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897367 prefixEnd_5897367 := by exact prefixLift 5897367
  have htrace : WordTrace (prefixWord ++ tailWord_5897367) baseStart_5897367 baseEnd_5897367 := by
    simpa [prefixWord, tailWord_5897367, baseEnd_5897367] using wordTrace_append hprefix tailTrace_5897367
  have hstable : (prefixWord ++ tailWord_5897367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897367).length < 2 ^ (prefixWord ++ tailWord_5897367).sum := by decide
  have hdescent : baseEnd_5897367 < baseStart_5897367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897380 : List Nat := [2, 3, 1, 2, 3, 3, 1, 8]
def baseStart_5897380 : Nat := 118140960795 + 5897380 * 2 ^ 59
def prefixEnd_5897380 : Nat := 4983230072969 + 3 ^ 40 * 5897380 * 2
def baseEnd_5897380 : Nat := 112155205267120063234387

theorem tailTrace_5897380 : CollatzResearch.WordTrace tailWord_5897380 prefixEnd_5897380 112155205267120063234387 := by
  unfold tailWord_5897380
  simp only [CollatzResearch.WordTrace]
  refine ⟨107547559687403463581216797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143396746249871284774955729 107547559687403463581216797)
  ·
    refine ⟨40330334882776298842956299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107547559687403463581216797 40330334882776298842956299)
    ·
      refine ⟨60495502324164448264434449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40330334882776298842956299 60495502324164448264434449)
      ·
        refine ⟨45371626743123336198325837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60495502324164448264434449 45371626743123336198325837)
        ·
          refine ⟨17014360028671251074372189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45371626743123336198325837 17014360028671251074372189)
          ·
            refine ⟨6380385010751719152889571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17014360028671251074372189 6380385010751719152889571)
            ·
              refine ⟨9570577516127578729334357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6380385010751719152889571 9570577516127578729334357)
              ·
                refine ⟨112155205267120063234387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9570577516127578729334357 112155205267120063234387)
                ·
                  rfl

theorem cell23_5897380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 8].length) (baseStart_5897380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897380 prefixEnd_5897380 := by exact prefixLift 5897380
  have htrace : WordTrace (prefixWord ++ tailWord_5897380) baseStart_5897380 baseEnd_5897380 := by
    simpa [prefixWord, tailWord_5897380, baseEnd_5897380] using wordTrace_append hprefix tailTrace_5897380
  have hstable : (prefixWord ++ tailWord_5897380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897380).length < 2 ^ (prefixWord ++ tailWord_5897380).sum := by decide
  have hdescent : baseEnd_5897380 < baseStart_5897380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897414 : List Nat := [6, 1, 2, 2, 1, 1, 10]
def baseStart_5897414 : Nat := 118140960795 + 5897414 * 2 ^ 59
def prefixEnd_5897414 : Nat := 4983230072969 + 3 ^ 40 * 5897414 * 2
def baseEnd_5897414 : Nat := 37385283957462895979053

theorem tailTrace_5897414 : CollatzResearch.WordTrace tailWord_5897414 prefixEnd_5897414 37385283957462895979053 := by
  unfold tailWord_5897414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721761233021367217786603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143397572971122500646114197 6721761233021367217786603)
  ·
    refine ⟨10082641849532050826679905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721761233021367217786603 10082641849532050826679905)
    ·
      refine ⟨7561981387149038120009929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10082641849532050826679905 7561981387149038120009929)
      ·
        refine ⟨5671486040361778590007447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7561981387149038120009929 5671486040361778590007447)
        ·
          refine ⟨8507229060542667885011171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671486040361778590007447 8507229060542667885011171)
          ·
            refine ⟨12760843590814001827516757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8507229060542667885011171 12760843590814001827516757)
            ·
              refine ⟨37385283957462895979053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12760843590814001827516757 37385283957462895979053)
              ·
                rfl

theorem cell23_5897414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 10].length) (baseStart_5897414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897414 prefixEnd_5897414 := by exact prefixLift 5897414
  have htrace : WordTrace (prefixWord ++ tailWord_5897414) baseStart_5897414 baseEnd_5897414 := by
    simpa [prefixWord, tailWord_5897414, baseEnd_5897414] using wordTrace_append hprefix tailTrace_5897414
  have hstable : (prefixWord ++ tailWord_5897414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897414).length < 2 ^ (prefixWord ++ tailWord_5897414).sum := by decide
  have hdescent : baseEnd_5897414 < baseStart_5897414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897433 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_5897433 : Nat := 118140960795 + 5897433 * 2 ^ 59
def prefixEnd_5897433 : Nat := 4983230072969 + 3 ^ 40 * 5897433 * 2
def baseEnd_5897433 : Nat := 3028217756686929999965705

theorem tailTrace_5897433 : CollatzResearch.WordTrace tailWord_5897433 prefixEnd_5897433 3028217756686929999965705 := by
  unfold tailWord_5897433
  simp only [CollatzResearch.WordTrace]
  refine ⟨215097052443614917214112953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143398034962409944809408635 215097052443614917214112953)
  ·
    refine ⟨161322789332711187910584715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215097052443614917214112953 161322789332711187910584715)
    ·
      refine ⟨241984183999066781865877073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161322789332711187910584715 241984183999066781865877073)
      ·
        refine ⟨181488137999300086399407805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241984183999066781865877073 181488137999300086399407805)
        ·
          refine ⟨68058051749737532399777927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181488137999300086399407805 68058051749737532399777927)
          ·
            refine ⟨102087077624606298599666891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68058051749737532399777927 102087077624606298599666891)
            ·
              refine ⟨153130616436909447899500337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102087077624606298599666891 153130616436909447899500337)
              ·
                refine ⟨114847962327682085924625253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153130616436909447899500337 114847962327682085924625253)
                ·
                  refine ⟨21533992936440391110867235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114847962327682085924625253 21533992936440391110867235)
                  ·
                    refine ⟨32300989404660586666300853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21533992936440391110867235 32300989404660586666300853)
                    ·
                      refine ⟨3028217756686929999965705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32300989404660586666300853 3028217756686929999965705)
                      ·
                        rfl

theorem cell23_5897433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_5897433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897433 prefixEnd_5897433 := by exact prefixLift 5897433
  have htrace : WordTrace (prefixWord ++ tailWord_5897433) baseStart_5897433 baseEnd_5897433 := by
    simpa [prefixWord, tailWord_5897433, baseEnd_5897433] using wordTrace_append hprefix tailTrace_5897433
  have hstable : (prefixWord ++ tailWord_5897433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897433).length < 2 ^ (prefixWord ++ tailWord_5897433).sum := by decide
  have hdescent : baseEnd_5897433 < baseStart_5897433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897498 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2]
def baseStart_5897498 : Nat := 118140960795 + 5897498 * 2 ^ 59
def prefixEnd_5897498 : Nat := 4983230072969 + 3 ^ 40 * 5897498 * 2
def baseEnd_5897498 : Nat := 3028251132929472245652907

theorem tailTrace_5897498 : CollatzResearch.WordTrace tailWord_5897498 prefixEnd_5897498 3028251132929472245652907 := by
  unfold tailWord_5897498
  simp only [CollatzResearch.WordTrace]
  refine ⟨53774855797094858328807287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143399615458919622210152765 53774855797094858328807287)
  ·
    refine ⟨80662283695642287493210931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53774855797094858328807287 80662283695642287493210931)
    ·
      refine ⟨120993425543463431239816397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80662283695642287493210931 120993425543463431239816397)
      ·
        refine ⟨45372534578798786714931149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120993425543463431239816397 45372534578798786714931149)
        ·
          refine ⟨17014700467049545018099181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45372534578798786714931149 17014700467049545018099181)
          ·
            refine ⟨6380512675143579381787193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17014700467049545018099181 6380512675143579381787193)
            ·
              refine ⟨4785384506357684536340395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6380512675143579381787193 4785384506357684536340395)
              ·
                refine ⟨7178076759536526804510593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785384506357684536340395 7178076759536526804510593)
                ·
                  refine ⟨5383557569652395103382945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7178076759536526804510593 5383557569652395103382945)
                  ·
                    refine ⟨4037668177239296327537209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5383557569652395103382945 4037668177239296327537209)
                    ·
                      refine ⟨3028251132929472245652907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037668177239296327537209 3028251132929472245652907)
                      ·
                        rfl

theorem cell23_5897498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_5897498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897498 prefixEnd_5897498 := by exact prefixLift 5897498
  have htrace : WordTrace (prefixWord ++ tailWord_5897498) baseStart_5897498 baseEnd_5897498 := by
    simpa [prefixWord, tailWord_5897498, baseEnd_5897498] using wordTrace_append hprefix tailTrace_5897498
  have hstable : (prefixWord ++ tailWord_5897498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897498).length < 2 ^ (prefixWord ++ tailWord_5897498).sum := by decide
  have hdescent : baseEnd_5897498 < baseStart_5897498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897560 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 6]
def baseStart_5897560 : Nat := 118140960795 + 5897560 * 2 ^ 59
def prefixEnd_5897560 : Nat := 4983230072969 + 3 ^ 40 * 5897560 * 2
def baseEnd_5897560 : Nat := 336475885414450111453069

theorem tailTrace_5897560 : CollatzResearch.WordTrace tailWord_5897560 prefixEnd_5897560 336475885414450111453069 := by
  unfold tailWord_5897560
  simp only [CollatzResearch.WordTrace]
  refine ⟨107550842257077408951993067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143401123009436545269324089 107550842257077408951993067)
  ·
    refine ⟨161326263385616113427989601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107550842257077408951993067 161326263385616113427989601)
    ·
      refine ⟨120994697539212085070992201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161326263385616113427989601 120994697539212085070992201)
      ·
        refine ⟨90746023154409063803244151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120994697539212085070992201 90746023154409063803244151)
        ·
          refine ⟨136119034731613595704866227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90746023154409063803244151 136119034731613595704866227)
          ·
            refine ⟨204178552097420393557299341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136119034731613595704866227 204178552097420393557299341)
            ·
              refine ⟨76566957036532647583987253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204178552097420393557299341 76566957036532647583987253)
              ·
                refine ⟨7178152222174935710998805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76566957036532647583987253 7178152222174935710998805)
                ·
                  refine ⟨336475885414450111453069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7178152222174935710998805 336475885414450111453069)
                  ·
                    rfl

theorem cell23_5897560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 6].length) (baseStart_5897560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897560 prefixEnd_5897560 := by exact prefixLift 5897560
  have htrace : WordTrace (prefixWord ++ tailWord_5897560) baseStart_5897560 baseEnd_5897560 := by
    simpa [prefixWord, tailWord_5897560, baseEnd_5897560] using wordTrace_append hprefix tailTrace_5897560
  have hstable : (prefixWord ++ tailWord_5897560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897560).length < 2 ^ (prefixWord ++ tailWord_5897560).sum := by decide
  have hdescent : baseEnd_5897560 < baseStart_5897560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897581 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_5897581 : Nat := 118140960795 + 5897581 * 2 ^ 59
def prefixEnd_5897581 : Nat := 4983230072969 + 3 ^ 40 * 5897581 * 2
def baseEnd_5897581 : Nat := 1009431250607931806971675

theorem tailTrace_5897581 : CollatzResearch.WordTrace tailWord_5897581 prefixEnd_5897581 1009431250607931806971675 := by
  unfold tailWord_5897581
  simp only [CollatzResearch.WordTrace]
  refine ⟨215102450447078738490500597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143401633631385825660333731 215102450447078738490500597)
  ·
    refine ⟨20165854729413631733484431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215102450447078738490500597 20165854729413631733484431)
    ·
      refine ⟨30248782094120447600226647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20165854729413631733484431 30248782094120447600226647)
      ·
        refine ⟨45373173141180671400339971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30248782094120447600226647 45373173141180671400339971)
        ·
          refine ⟨68059759711771007100509957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45373173141180671400339971 68059759711771007100509957)
          ·
            refine ⟨12761204945957063831345617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68059759711771007100509957 12761204945957063831345617)
            ·
              refine ⟨9570903709467797873509213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12761204945957063831345617 9570903709467797873509213)
              ·
                refine ⟨3589088891050424202565955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9570903709467797873509213 3589088891050424202565955)
                ·
                  refine ⟨5383633336575636303848933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589088891050424202565955 5383633336575636303848933)
                  ·
                    refine ⟨1009431250607931806971675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383633336575636303848933 1009431250607931806971675)
                    ·
                      rfl

theorem cell23_5897581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_5897581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897581 prefixEnd_5897581 := by exact prefixLift 5897581
  have htrace : WordTrace (prefixWord ++ tailWord_5897581) baseStart_5897581 baseEnd_5897581 := by
    simpa [prefixWord, tailWord_5897581, baseEnd_5897581] using wordTrace_append hprefix tailTrace_5897581
  have hstable : (prefixWord ++ tailWord_5897581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897581).length < 2 ^ (prefixWord ++ tailWord_5897581).sum := by decide
  have hdescent : baseEnd_5897581 < baseStart_5897581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897598 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5897598 : Nat := 118140960795 + 5897598 * 2 ^ 59
def prefixEnd_5897598 : Nat := 4983230072969 + 3 ^ 40 * 5897598 * 2
def baseEnd_5897598 : Nat := 1009434160331640618134149

theorem tailTrace_5897598 : CollatzResearch.WordTrace tailWord_5897598 prefixEnd_5897598 1009434160331640618134149 := by
  unfold tailWord_5897598
  simp only [CollatzResearch.WordTrace]
  refine ⟨26887883811002143799233681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143402046992011433595912965 26887883811002143799233681)
  ·
    refine ⟨20165912858251607849425261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26887883811002143799233681 20165912858251607849425261)
    ·
      refine ⟨7562217321844352943534473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20165912858251607849425261 7562217321844352943534473)
      ·
        refine ⟨5671662991383264707650855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7562217321844352943534473 5671662991383264707650855)
        ·
          refine ⟨8507494487074897061476283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671662991383264707650855 8507494487074897061476283)
          ·
            refine ⟨12761241730612345592214425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8507494487074897061476283 12761241730612345592214425)
            ·
              refine ⟨9570931297959259194160819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12761241730612345592214425 9570931297959259194160819)
              ·
                refine ⟨14356396946938888791241229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9570931297959259194160819 14356396946938888791241229)
                ·
                  refine ⟨5383648855102083296715461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14356396946938888791241229 5383648855102083296715461)
                  ·
                    refine ⟨1009434160331640618134149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383648855102083296715461 1009434160331640618134149)
                    ·
                      rfl

theorem cell23_5897598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5897598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897598 prefixEnd_5897598 := by exact prefixLift 5897598
  have htrace : WordTrace (prefixWord ++ tailWord_5897598) baseStart_5897598 baseEnd_5897598 := by
    simpa [prefixWord, tailWord_5897598, baseEnd_5897598] using wordTrace_append hprefix tailTrace_5897598
  have hstable : (prefixWord ++ tailWord_5897598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897598).length < 2 ^ (prefixWord ++ tailWord_5897598).sum := by decide
  have hdescent : baseEnd_5897598 < baseStart_5897598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897604 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_5897604 : Nat := 118140960795 + 5897604 * 2 ^ 59
def prefixEnd_5897604 : Nat := 4983230072969 + 3 ^ 40 * 5897604 * 2
def baseEnd_5897604 : Nat := 3028305561878848830927419

theorem tailTrace_5897604 : CollatzResearch.WordTrace tailWord_5897604 prefixEnd_5897604 3028305561878848830927419 := by
  unfold tailWord_5897604
  simp only [CollatzResearch.WordTrace]
  refine ⟨107551644662997706709293933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143402192883996942279058577 107551644662997706709293933)
  ·
    refine ⟨40331866748624140015985225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107551644662997706709293933 40331866748624140015985225)
    ·
      refine ⟨30248900061468105011988919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40331866748624140015985225 30248900061468105011988919)
      ·
        refine ⟨45373350092202157517983379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30248900061468105011988919 45373350092202157517983379)
        ·
          refine ⟨68060025138303236276975069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45373350092202157517983379 68060025138303236276975069)
          ·
            refine ⟨25522509426863713603865651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68060025138303236276975069 25522509426863713603865651)
            ·
              refine ⟨38283764140295570405798477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25522509426863713603865651 38283764140295570405798477)
              ·
                refine ⟨14356411552610838902174429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38283764140295570405798477 14356411552610838902174429)
                ·
                  refine ⟨5383654332229064588315411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14356411552610838902174429 5383654332229064588315411)
                  ·
                    refine ⟨8075481498343596882473117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5383654332229064588315411 8075481498343596882473117)
                    ·
                      refine ⟨3028305561878848830927419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075481498343596882473117 3028305561878848830927419)
                      ·
                        rfl

theorem cell23_5897604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_5897604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897604 prefixEnd_5897604 := by exact prefixLift 5897604
  have htrace : WordTrace (prefixWord ++ tailWord_5897604) baseStart_5897604 baseEnd_5897604 := by
    simpa [prefixWord, tailWord_5897604, baseEnd_5897604] using wordTrace_append hprefix tailTrace_5897604
  have hstable : (prefixWord ++ tailWord_5897604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897604).length < 2 ^ (prefixWord ++ tailWord_5897604).sum := by decide
  have hdescent : baseEnd_5897604 < baseStart_5897604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897644 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 5, 2, 2]
def baseStart_5897644 : Nat := 118140960795 + 5897644 * 2 ^ 59
def prefixEnd_5897644 : Nat := 4983230072969 + 3 ^ 40 * 5897644 * 2
def baseEnd_5897644 : Nat := 3028326101105028674427235

theorem tailTrace_5897644 : CollatzResearch.WordTrace tailWord_5897644 prefixEnd_5897644 3028326101105028674427235 := by
  unfold tailWord_5897644
  simp only [CollatzResearch.WordTrace]
  refine ⟨107552374122925250125021993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143403165497233666833362657 107552374122925250125021993)
  ·
    refine ⟨80664280592193937593766495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107552374122925250125021993 80664280592193937593766495)
    ·
      refine ⟨120996420888290906390649743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80664280592193937593766495 120996420888290906390649743)
      ·
        refine ⟨181494631332436359585974615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120996420888290906390649743 181494631332436359585974615)
        ·
          refine ⟨272241946998654539378961923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181494631332436359585974615 272241946998654539378961923)
          ·
            refine ⟨408362920497981809068442885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272241946998654539378961923 408362920497981809068442885)
            ·
              refine ⟨76568047593371589200333041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 408362920497981809068442885 76568047593371589200333041)
              ·
                refine ⟨57426035695028691900249781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76568047593371589200333041 57426035695028691900249781)
                ·
                  refine ⟨5383690846408939865648417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57426035695028691900249781 5383690846408939865648417)
                  ·
                    refine ⟨4037768134806704899236313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5383690846408939865648417 4037768134806704899236313)
                    ·
                      refine ⟨3028326101105028674427235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037768134806704899236313 3028326101105028674427235)
                      ·
                        rfl

theorem cell23_5897644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_5897644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897644 prefixEnd_5897644 := by exact prefixLift 5897644
  have htrace : WordTrace (prefixWord ++ tailWord_5897644) baseStart_5897644 baseEnd_5897644 := by
    simpa [prefixWord, tailWord_5897644, baseEnd_5897644] using wordTrace_append hprefix tailTrace_5897644
  have hstable : (prefixWord ++ tailWord_5897644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897644).length < 2 ^ (prefixWord ++ tailWord_5897644).sum := by decide
  have hdescent : baseEnd_5897644 < baseStart_5897644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897680 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_5897680 : Nat := 118140960795 + 5897680 * 2 ^ 59
def prefixEnd_5897680 : Nat := 4983230072969 + 3 ^ 40 * 5897680 * 2
def baseEnd_5897680 : Nat := 1009448195469530177859023

theorem tailTrace_5897680 : CollatzResearch.WordTrace tailWord_5897680 prefixEnd_5897680 1009448195469530177859023 := by
  unfold tailWord_5897680
  simp only [CollatzResearch.WordTrace]
  refine ⟨107553030636860039199177247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143404040849146718932236329 107553030636860039199177247)
  ·
    refine ⟨161329545955290058798765871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107553030636860039199177247 161329545955290058798765871)
    ·
      refine ⟨241994318932935088198148807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161329545955290058798765871 241994318932935088198148807)
      ·
        refine ⟨362991478399402632297223211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241994318932935088198148807 362991478399402632297223211)
        ·
          refine ⟨544487217599103948445834817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362991478399402632297223211 544487217599103948445834817)
          ·
            refine ⟨408365413199327961334376113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544487217599103948445834817 408365413199327961334376113)
            ·
              refine ⟨306274059899495971000782085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408365413199327961334376113 306274059899495971000782085)
              ·
                refine ⟨57426386231155494562646641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306274059899495971000782085 57426386231155494562646641)
                ·
                  refine ⟨43069789673366620921984981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57426386231155494562646641 43069789673366620921984981)
                  ·
                    refine ⟨1009448195469530177859023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43069789673366620921984981 1009448195469530177859023)
                    ·
                      rfl

theorem cell23_5897680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_5897680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897680 prefixEnd_5897680 := by exact prefixLift 5897680
  have htrace : WordTrace (prefixWord ++ tailWord_5897680) baseStart_5897680 baseEnd_5897680 := by
    simpa [prefixWord, tailWord_5897680, baseEnd_5897680] using wordTrace_append hprefix tailTrace_5897680
  have hstable : (prefixWord ++ tailWord_5897680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897680).length < 2 ^ (prefixWord ++ tailWord_5897680).sum := by decide
  have hdescent : baseEnd_5897680 < baseStart_5897680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897737 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_5897737 : Nat := 118140960795 + 5897737 * 2 ^ 59
def prefixEnd_5897737 : Nat := 4983230072969 + 3 ^ 40 * 5897737 * 2
def baseEnd_5897737 : Nat := 3028373854805896810564307

theorem tailTrace_5897737 : CollatzResearch.WordTrace tailWord_5897737 prefixEnd_5897737 3028373854805896810564307 := by
  unfold tailWord_5897737
  simp only [CollatzResearch.WordTrace]
  refine ⟨215108140234513577133179465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143405426823009051422119643 215108140234513577133179465)
  ·
    refine ⟨161331105175885182849884599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215108140234513577133179465 161331105175885182849884599)
    ·
      refine ⟨241996657763827774274826899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161331105175885182849884599 241996657763827774274826899)
      ·
        refine ⟨362994986645741661412240349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241996657763827774274826899 362994986645741661412240349)
        ·
          refine ⟨136123119992153123029590131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362994986645741661412240349 136123119992153123029590131)
          ·
            refine ⟨204184679988229684544385197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136123119992153123029590131 204184679988229684544385197)
            ·
              refine ⟨76569254995586131704144449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204184679988229684544385197 76569254995586131704144449)
              ·
                refine ⟨57426941246689598778108337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76569254995586131704144449 57426941246689598778108337)
                ·
                  refine ⟨43070205935017199083581253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57426941246689598778108337 43070205935017199083581253)
                  ·
                    refine ⟨8075663612815724828171485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43070205935017199083581253 8075663612815724828171485)
                    ·
                      refine ⟨3028373854805896810564307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075663612815724828171485 3028373854805896810564307)
                      ·
                        rfl

theorem cell23_5897737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_5897737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897737 prefixEnd_5897737 := by exact prefixLift 5897737
  have htrace : WordTrace (prefixWord ++ tailWord_5897737) baseStart_5897737 baseEnd_5897737 := by
    simpa [prefixWord, tailWord_5897737, baseEnd_5897737] using wordTrace_append hprefix tailTrace_5897737
  have hstable : (prefixWord ++ tailWord_5897737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897737).length < 2 ^ (prefixWord ++ tailWord_5897737).sum := by decide
  have hdescent : baseEnd_5897737 < baseStart_5897737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897757 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 9]
def baseStart_5897757 : Nat := 118140960795 + 5897757 * 2 ^ 59
def prefixEnd_5897757 : Nat := 4983230072969 + 3 ^ 40 * 5897757 * 2
def baseEnd_5897757 : Nat := 336487124935442970257135

theorem tailTrace_5897757 : CollatzResearch.WordTrace tailWord_5897757 prefixEnd_5897757 336487124935442970257135 := by
  unfold tailWord_5897757
  simp only [CollatzResearch.WordTrace]
  refine ⟨215108869694441120548907525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143405913129627413699271683 215108869694441120548907525)
  ·
    refine ⟨40332913067707710102920161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215108869694441120548907525 40332913067707710102920161)
    ·
      refine ⟨30249684800780782577190121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40332913067707710102920161 30249684800780782577190121)
      ·
        refine ⟨22687263600585586932892591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30249684800780782577190121 22687263600585586932892591)
        ·
          refine ⟨34030895400878380399338887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22687263600585586932892591 34030895400878380399338887)
          ·
            refine ⟨51046343101317570599008331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34030895400878380399338887 51046343101317570599008331)
            ·
              refine ⟨76569514651976355898512497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51046343101317570599008331 76569514651976355898512497)
              ·
                refine ⟨57427135988982266923884373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76569514651976355898512497 57427135988982266923884373)
                ·
                  refine ⟨336487124935442970257135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57427135988982266923884373 336487124935442970257135)
                  ·
                    rfl

theorem cell23_5897757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_5897757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897757 prefixEnd_5897757 := by exact prefixLift 5897757
  have htrace : WordTrace (prefixWord ++ tailWord_5897757) baseStart_5897757 baseEnd_5897757 := by
    simpa [prefixWord, tailWord_5897757, baseEnd_5897757] using wordTrace_append hprefix tailTrace_5897757
  have hstable : (prefixWord ++ tailWord_5897757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897757).length < 2 ^ (prefixWord ++ tailWord_5897757).sum := by decide
  have hdescent : baseEnd_5897757 < baseStart_5897757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897774 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_5897774 : Nat := 118140960795 + 5897774 * 2 ^ 59
def prefixEnd_5897774 : Nat := 4983230072969 + 3 ^ 40 * 5897774 * 2
def baseEnd_5897774 : Nat := 336488094843345907311293

theorem tailTrace_5897774 : CollatzResearch.WordTrace tailWord_5897774 prefixEnd_5897774 336488094843345907311293 := by
  unfold tailWord_5897774
  simp only [CollatzResearch.WordTrace]
  refine ⟨26888686216922441556534547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143406326490253021634850917 26888686216922441556534547)
  ·
    refine ⟨40333029325383662334801821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26888686216922441556534547 40333029325383662334801821)
    ·
      refine ⟨15124885997018873375550683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40333029325383662334801821 15124885997018873375550683)
      ·
        refine ⟨22687328995528310063326025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15124885997018873375550683 22687328995528310063326025)
        ·
          refine ⟨17015496746646232547494519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22687328995528310063326025 17015496746646232547494519)
          ·
            refine ⟨25523245119969348821241779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17015496746646232547494519 25523245119969348821241779)
            ·
              refine ⟨38284867679954023231862669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25523245119969348821241779 38284867679954023231862669)
              ·
                refine ⟨14356825379982758711948501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38284867679954023231862669 14356825379982758711948501)
                ·
                  refine ⟨336488094843345907311293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14356825379982758711948501 336488094843345907311293)
                  ·
                    rfl

theorem cell23_5897774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_5897774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897774 prefixEnd_5897774 := by exact prefixLift 5897774
  have htrace : WordTrace (prefixWord ++ tailWord_5897774) baseStart_5897774 baseEnd_5897774 := by
    simpa [prefixWord, tailWord_5897774, baseEnd_5897774] using wordTrace_append hprefix tailTrace_5897774
  have hstable : (prefixWord ++ tailWord_5897774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897774).length < 2 ^ (prefixWord ++ tailWord_5897774).sum := by decide
  have hdescent : baseEnd_5897774 < baseStart_5897774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897784 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_5897784 : Nat := 118140960795 + 5897784 * 2 ^ 59
def prefixEnd_5897784 : Nat := 4983230072969 + 3 ^ 40 * 5897784 * 2
def baseEnd_5897784 : Nat := 3028397988396658126676591

theorem tailTrace_5897784 : CollatzResearch.WordTrace tailWord_5897784 prefixEnd_5897784 3028397988396658126676591 := by
  unfold tailWord_5897784
  simp only [CollatzResearch.WordTrace]
  refine ⟨107554927232671652080070203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143406569643562202773426937 107554927232671652080070203)
  ·
    refine ⟨161332390849007478120105305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107554927232671652080070203 161332390849007478120105305)
    ·
      refine ⟨120999293136755608590078979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161332390849007478120105305 120999293136755608590078979)
      ·
        refine ⟨181498939705133412885118469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120999293136755608590078979 181498939705133412885118469)
        ·
          refine ⟨34031051194712514915959713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181498939705133412885118469 34031051194712514915959713)
          ·
            refine ⟨25523288396034386186969785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34031051194712514915959713 25523288396034386186969785)
            ·
              refine ⟨19142466297025789640227339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25523288396034386186969785 19142466297025789640227339)
              ·
                refine ⟨28713699445538684460341009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19142466297025789640227339 28713699445538684460341009)
                ·
                  refine ⟨21535274584154013345255757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28713699445538684460341009 21535274584154013345255757)
                  ·
                    refine ⟨8075727969057755004470909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21535274584154013345255757 8075727969057755004470909)
                    ·
                      refine ⟨3028397988396658126676591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075727969057755004470909 3028397988396658126676591)
                      ·
                        rfl

theorem cell23_5897784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_5897784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897784 prefixEnd_5897784 := by exact prefixLift 5897784
  have htrace : WordTrace (prefixWord ++ tailWord_5897784) baseStart_5897784 baseEnd_5897784 := by
    simpa [prefixWord, tailWord_5897784, baseEnd_5897784] using wordTrace_append hprefix tailTrace_5897784
  have hstable : (prefixWord ++ tailWord_5897784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897784).length < 2 ^ (prefixWord ++ tailWord_5897784).sum := by decide
  have hdescent : baseEnd_5897784 < baseStart_5897784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897785 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5897785 : Nat := 118140960795 + 5897785 * 2 ^ 59
def prefixEnd_5897785 : Nat := 4983230072969 + 3 ^ 40 * 5897785 * 2
def baseEnd_5897785 : Nat := 3028398501877312622764087

theorem tailTrace_5897785 : CollatzResearch.WordTrace tailWord_5897785 prefixEnd_5897785 3028398501877312622764087 := by
  unfold tailWord_5897785
  simp only [CollatzResearch.WordTrace]
  refine ⟨215109890938339681330926809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143406593958893120887284539 215109890938339681330926809)
  ·
    refine ⟨161332418203754760998195107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215109890938339681330926809 161332418203754760998195107)
    ·
      refine ⟨241998627305632141497292661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161332418203754760998195107 241998627305632141497292661)
      ·
        refine ⟨22687371309903013265371187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241998627305632141497292661 22687371309903013265371187)
        ·
          refine ⟨34031056964854519898056781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22687371309903013265371187 34031056964854519898056781)
          ·
            refine ⟨12761646361820444961771293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34031056964854519898056781 12761646361820444961771293)
            ·
              refine ⟨4785617385682666860664235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12761646361820444961771293 4785617385682666860664235)
              ·
                refine ⟨7178426078524000290996353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785617385682666860664235 7178426078524000290996353)
                ·
                  refine ⟨5383819558893000218247265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7178426078524000290996353 5383819558893000218247265)
                  ·
                    refine ⟨4037864669169750163685449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5383819558893000218247265 4037864669169750163685449)
                    ·
                      refine ⟨3028398501877312622764087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037864669169750163685449 3028398501877312622764087)
                      ·
                        rfl

theorem cell23_5897785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5897785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897785 prefixEnd_5897785 := by exact prefixLift 5897785
  have htrace : WordTrace (prefixWord ++ tailWord_5897785) baseStart_5897785 baseEnd_5897785 := by
    simpa [prefixWord, tailWord_5897785, baseEnd_5897785] using wordTrace_append hprefix tailTrace_5897785
  have hstable : (prefixWord ++ tailWord_5897785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897785).length < 2 ^ (prefixWord ++ tailWord_5897785).sum := by decide
  have hdescent : baseEnd_5897785 < baseStart_5897785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897861 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_5897861 : Nat := 118140960795 + 5897861 * 2 ^ 59
def prefixEnd_5897861 : Nat := 4983230072969 + 3 ^ 40 * 5897861 * 2
def baseEnd_5897861 : Nat := 3028437526407054325413737

theorem tailTrace_5897861 : CollatzResearch.WordTrace tailWord_5897861 prefixEnd_5897861 3028437526407054325413737 := by
  unfold tailWord_5897861
  simp only [CollatzResearch.WordTrace]
  refine ⟨215112662886064346310693437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143408441924042897540462291 215112662886064346310693437)
  ·
    refine ⟨80667248582274129866510039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215112662886064346310693437 80667248582274129866510039)
    ·
      refine ⟨121000872873411194799765059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80667248582274129866510039 121000872873411194799765059)
      ·
        refine ⟨181501309310116792199647589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121000872873411194799765059 181501309310116792199647589)
        ·
          refine ⟨34031495495646898537433923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181501309310116792199647589 34031495495646898537433923)
          ·
            refine ⟨51047243243470347806150885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34031495495646898537433923 51047243243470347806150885)
            ·
              refine ⟨9571358108150690213653291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51047243243470347806150885 9571358108150690213653291)
              ·
                refine ⟨14357037162226035320479937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9571358108150690213653291 14357037162226035320479937)
                ·
                  refine ⟨10767777871669526490359953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14357037162226035320479937 10767777871669526490359953)
                  ·
                    refine ⟨8075833403752144867769965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10767777871669526490359953 8075833403752144867769965)
                    ·
                      refine ⟨3028437526407054325413737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075833403752144867769965 3028437526407054325413737)
                      ·
                        rfl

theorem cell23_5897861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_5897861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897861 prefixEnd_5897861 := by exact prefixLift 5897861
  have htrace : WordTrace (prefixWord ++ tailWord_5897861) baseStart_5897861 baseEnd_5897861 := by
    simpa [prefixWord, tailWord_5897861, baseEnd_5897861] using wordTrace_append hprefix tailTrace_5897861
  have hstable : (prefixWord ++ tailWord_5897861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897861).length < 2 ^ (prefixWord ++ tailWord_5897861).sum := by decide
  have hdescent : baseEnd_5897861 < baseStart_5897861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897891 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 3]
def baseStart_5897891 : Nat := 118140960795 + 5897891 * 2 ^ 59
def prefixEnd_5897891 : Nat := 4983230072969 + 3 ^ 40 * 5897891 * 2
def baseEnd_5897891 : Nat := 3028452930826689208038599

theorem tailTrace_5897891 : CollatzResearch.WordTrace tailWord_5897891 prefixEnd_5897891 3028452930826689208038599 := by
  unfold tailWord_5897891
  simp only [CollatzResearch.WordTrace]
  refine ⟨215113757075955661434285527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143409171383970440956190351 215113757075955661434285527)
  ·
    refine ⟨322670635613933492151428291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215113757075955661434285527 322670635613933492151428291)
    ·
      refine ⟨484005953420900238227142437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322670635613933492151428291 484005953420900238227142437)
      ·
        refine ⟨90751116266418794667589207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 484005953420900238227142437 90751116266418794667589207)
        ·
          refine ⟨136126674399628192001383811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90751116266418794667589207 136126674399628192001383811)
          ·
            refine ⟨204190011599442288002075717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136126674399628192001383811 204190011599442288002075717)
            ·
              refine ⟨38285627174895429000389197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204190011599442288002075717 38285627174895429000389197)
              ·
                refine ⟨14357110190585785875145949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38285627174895429000389197 14357110190585785875145949)
                ·
                  refine ⟨5383916321469669703179731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14357110190585785875145949 5383916321469669703179731)
                  ·
                    refine ⟨8075874482204504554769597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5383916321469669703179731 8075874482204504554769597)
                    ·
                      refine ⟨3028452930826689208038599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8075874482204504554769597 3028452930826689208038599)
                      ·
                        rfl

theorem cell23_5897891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_5897891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897891 prefixEnd_5897891 := by exact prefixLift 5897891
  have htrace : WordTrace (prefixWord ++ tailWord_5897891) baseStart_5897891 baseEnd_5897891 := by
    simpa [prefixWord, tailWord_5897891, baseEnd_5897891] using wordTrace_append hprefix tailTrace_5897891
  have hstable : (prefixWord ++ tailWord_5897891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897891).length < 2 ^ (prefixWord ++ tailWord_5897891).sum := by decide
  have hdescent : baseEnd_5897891 < baseStart_5897891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897918 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_5897918 : Nat := 118140960795 + 5897918 * 2 ^ 59
def prefixEnd_5897918 : Nat := 4983230072969 + 3 ^ 40 * 5897918 * 2
def baseEnd_5897918 : Nat := 3028466794804360602400975

theorem tailTrace_5897918 : CollatzResearch.WordTrace tailWord_5897918 prefixEnd_5897918 3028466794804360602400975 := by
  unfold tailWord_5897918
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889342730857230630689801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143409827897905230030345605 26889342730857230630689801)
  ·
    refine ⟨20167007048142922973017351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26889342730857230630689801 20167007048142922973017351)
    ·
      refine ⟨30250510572214384459526027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167007048142922973017351 30250510572214384459526027)
      ·
        refine ⟨45375765858321576689289041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30250510572214384459526027 45375765858321576689289041)
        ·
          refine ⟨34031824393741182516966781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45375765858321576689289041 34031824393741182516966781)
          ·
            refine ⟨12761934147652943443862543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34031824393741182516966781 12761934147652943443862543)
            ·
              refine ⟨19142901221479415165793815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12761934147652943443862543 19142901221479415165793815)
              ·
                refine ⟨28714351832219122748690723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19142901221479415165793815 28714351832219122748690723)
                ·
                  refine ⟨43071527748328684123036085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28714351832219122748690723 43071527748328684123036085)
                  ·
                    refine ⟨4037955726405814136534633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43071527748328684123036085 4037955726405814136534633)
                    ·
                      refine ⟨3028466794804360602400975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037955726405814136534633 3028466794804360602400975)
                      ·
                        rfl

theorem cell23_5897918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_5897918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897918 prefixEnd_5897918 := by exact prefixLift 5897918
  have htrace : WordTrace (prefixWord ++ tailWord_5897918) baseStart_5897918 baseEnd_5897918 := by
    simpa [prefixWord, tailWord_5897918, baseEnd_5897918] using wordTrace_append hprefix tailTrace_5897918
  have hstable : (prefixWord ++ tailWord_5897918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897918).length < 2 ^ (prefixWord ++ tailWord_5897918).sum := by decide
  have hdescent : baseEnd_5897918 < baseStart_5897918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897944 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_5897944 : Nat := 118140960795 + 5897944 * 2 ^ 59
def prefixEnd_5897944 : Nat := 4983230072969 + 3 ^ 40 * 5897944 * 2
def baseEnd_5897944 : Nat := 3028480145301377500675855

theorem tailTrace_5897944 : CollatzResearch.WordTrace tailWord_5897944 prefixEnd_5897944 3028480145301377500675855 := by
  unfold tailWord_5897944
  simp only [CollatzResearch.WordTrace]
  refine ⟨107557845072381825742982443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143410460096509100990643257 107557845072381825742982443)
  ·
    refine ⟨161336767608572738614473665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107557845072381825742982443 161336767608572738614473665)
    ·
      refine ⟨121002575706429553960855249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161336767608572738614473665 121002575706429553960855249)
      ·
        refine ⟨90751931779822165470641437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121002575706429553960855249 90751931779822165470641437)
        ·
          refine ⟨34031974417433312051490539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90751931779822165470641437 34031974417433312051490539)
          ·
            refine ⟨51047961626149968077235809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34031974417433312051490539 51047961626149968077235809)
            ·
              refine ⟨38285971219612476057926857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51047961626149968077235809 38285971219612476057926857)
              ·
                refine ⟨28714478414709357043445143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38285971219612476057926857 28714478414709357043445143)
                ·
                  refine ⟨43071717622064035565167715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28714478414709357043445143 43071717622064035565167715)
                  ·
                    refine ⟨64607576433096053347751573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43071717622064035565167715 64607576433096053347751573)
                    ·
                      refine ⟨3028480145301377500675855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64607576433096053347751573 3028480145301377500675855)
                      ·
                        rfl

theorem cell23_5897944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_5897944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897944 prefixEnd_5897944 := by exact prefixLift 5897944
  have htrace : WordTrace (prefixWord ++ tailWord_5897944) baseStart_5897944 baseEnd_5897944 := by
    simpa [prefixWord, tailWord_5897944, baseEnd_5897944] using wordTrace_append hprefix tailTrace_5897944
  have hstable : (prefixWord ++ tailWord_5897944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897944).length < 2 ^ (prefixWord ++ tailWord_5897944).sum := by decide
  have hdescent : baseEnd_5897944 < baseStart_5897944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897965 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_5897965 : Nat := 118140960795 + 5897965 * 2 ^ 59
def prefixEnd_5897965 : Nat := 4983230072969 + 3 ^ 40 * 5897965 * 2
def baseEnd_5897965 : Nat := 3028490928395121918513259

theorem tailTrace_5897965 : CollatzResearch.WordTrace tailWord_5897965 prefixEnd_5897965 3028490928395121918513259 := by
  unfold tailWord_5897965
  simp only [CollatzResearch.WordTrace]
  refine ⟨215116456077687572072479349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143410970718458381381652899 215116456077687572072479349)
  ·
    refine ⟨20167167757283209881794939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215116456077687572072479349 20167167757283209881794939)
    ·
      refine ⟨30250751635924814822692409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167167757283209881794939 30250751635924814822692409)
      ·
        refine ⟨22688063726943611117019307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30250751635924814822692409 22688063726943611117019307)
        ·
          refine ⟨34032095590415416675528961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22688063726943611117019307 34032095590415416675528961)
          ·
            refine ⟨25524071692811562506646721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34032095590415416675528961 25524071692811562506646721)
            ·
              refine ⟨19143053769608671879985041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25524071692811562506646721 19143053769608671879985041)
              ·
                refine ⟨14357290327206503909988781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19143053769608671879985041 14357290327206503909988781)
                ·
                  refine ⟨5383983872702438966245793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14357290327206503909988781 5383983872702438966245793)
                  ·
                    refine ⟨4037987904526829224684345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5383983872702438966245793 4037987904526829224684345)
                    ·
                      refine ⟨3028490928395121918513259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4037987904526829224684345 3028490928395121918513259)
                      ·
                        rfl

theorem cell23_5897965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_5897965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897965 prefixEnd_5897965 := by exact prefixLift 5897965
  have htrace : WordTrace (prefixWord ++ tailWord_5897965) baseStart_5897965 baseEnd_5897965 := by
    simpa [prefixWord, tailWord_5897965, baseEnd_5897965] using wordTrace_append hprefix tailTrace_5897965
  have hstable : (prefixWord ++ tailWord_5897965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897965).length < 2 ^ (prefixWord ++ tailWord_5897965).sum := by decide
  have hdescent : baseEnd_5897965 < baseStart_5897965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5897998 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_5897998 : Nat := 118140960795 + 5897998 * 2 ^ 59
def prefixEnd_5897998 : Nat := 4983230072969 + 3 ^ 40 * 5897998 * 2
def baseEnd_5897998 : Nat := 3028507873256720289400607

theorem tailTrace_5897998 : CollatzResearch.WordTrace tailWord_5897998 prefixEnd_5897998 3028507873256720289400607 := by
  unfold tailWord_5897998
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889707460821002338553831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143411773124378679138953765 26889707460821002338553831)
  ·
    refine ⟨40334561191231503507830747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26889707460821002338553831 40334561191231503507830747)
    ·
      refine ⟨60501841786847255261746121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40334561191231503507830747 60501841786847255261746121)
      ·
        refine ⟨45376381340135441446309591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60501841786847255261746121 45376381340135441446309591)
        ·
          refine ⟨68064572010203162169464387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45376381340135441446309591 68064572010203162169464387)
          ·
            refine ⟨102096858015304743254196581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68064572010203162169464387 102096858015304743254196581)
            ·
              refine ⟨19143160877869639360161859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102096858015304743254196581 19143160877869639360161859)
              ·
                refine ⟨28714741316804459040242789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19143160877869639360161859 28714741316804459040242789)
                ·
                  refine ⟨5384013996900836070045523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28714741316804459040242789 5384013996900836070045523)
                  ·
                    refine ⟨8076020995351254105068285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5384013996900836070045523 8076020995351254105068285)
                    ·
                      refine ⟨3028507873256720289400607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8076020995351254105068285 3028507873256720289400607)
                      ·
                        rfl

theorem cell23_5897998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_5897998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5897998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5897998 prefixEnd_5897998 := by exact prefixLift 5897998
  have htrace : WordTrace (prefixWord ++ tailWord_5897998) baseStart_5897998 baseEnd_5897998 := by
    simpa [prefixWord, tailWord_5897998, baseEnd_5897998] using wordTrace_append hprefix tailTrace_5897998
  have hstable : (prefixWord ++ tailWord_5897998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5897998).length < 2 ^ (prefixWord ++ tailWord_5897998).sum := by decide
  have hdescent : baseEnd_5897998 < baseStart_5897998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5897998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898042 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2]
def baseStart_5898042 : Nat := 118140960795 + 5898042 * 2 ^ 59
def prefixEnd_5898042 : Nat := 4983230072969 + 3 ^ 40 * 5898042 * 2
def baseEnd_5898042 : Nat := 3028530466405518117250405

theorem tailTrace_5898042 : CollatzResearch.WordTrace tailWord_5898042 prefixEnd_5898042 3028530466405518117250405 := by
  unfold tailWord_5898042
  simp only [CollatzResearch.WordTrace]
  refine ⟨53779816124602153555758095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143412842998939076148688253 53779816124602153555758095)
  ·
    refine ⟨80669724186903230333637143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53779816124602153555758095 80669724186903230333637143)
    ·
      refine ⟨121004586280354845500455715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80669724186903230333637143 121004586280354845500455715)
      ·
        refine ⟨181506879420532268250683573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121004586280354845500455715 181506879420532268250683573)
        ·
          refine ⟨17016269945674900148501585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181506879420532268250683573 17016269945674900148501585)
          ·
            refine ⟨12762202459256175111376189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17016269945674900148501585 12762202459256175111376189)
            ·
              refine ⟨4785825922221065666766071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12762202459256175111376189 4785825922221065666766071)
              ·
                refine ⟨7178738883331598500149107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785825922221065666766071 7178738883331598500149107)
                ·
                  refine ⟨10768108324997397750223661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7178738883331598500149107 10768108324997397750223661)
                  ·
                    refine ⟨4038040621874024156333873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10768108324997397750223661 4038040621874024156333873)
                    ·
                      refine ⟨3028530466405518117250405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038040621874024156333873 3028530466405518117250405)
                      ·
                        rfl

theorem cell23_5898042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_5898042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898042 prefixEnd_5898042 := by exact prefixLift 5898042
  have htrace : WordTrace (prefixWord ++ tailWord_5898042) baseStart_5898042 baseEnd_5898042 := by
    simpa [prefixWord, tailWord_5898042, baseEnd_5898042] using wordTrace_append hprefix tailTrace_5898042
  have hstable : (prefixWord ++ tailWord_5898042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898042).length < 2 ^ (prefixWord ++ tailWord_5898042).sum := by decide
  have hdescent : baseEnd_5898042 < baseStart_5898042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898055 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_5898055 : Nat := 118140960795 + 5898055 * 2 ^ 59
def prefixEnd_5898055 : Nat := 4983230072969 + 3 ^ 40 * 5898055 * 2
def baseEnd_5898055 : Nat := 3028537141654026566387845

theorem tailTrace_5898055 : CollatzResearch.WordTrace tailWord_5898055 prefixEnd_5898055 3028537141654026566387845 := by
  unfold tailWord_5898055
  simp only [CollatzResearch.WordTrace]
  refine ⟨215119738647361517443255619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143413159098241011628837079 215119738647361517443255619)
  ·
    refine ⟨322679607971042276164883429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215119738647361517443255619 322679607971042276164883429)
    ·
      refine ⟨60502426494570426780915643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322679607971042276164883429 60502426494570426780915643)
      ·
        refine ⟨90753639741855640171373465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60502426494570426780915643 90753639741855640171373465)
        ·
          refine ⟨68065229806391730128530099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90753639741855640171373465 68065229806391730128530099)
          ·
            refine ⟨102097844709587595192795149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68065229806391730128530099 102097844709587595192795149)
            ·
              refine ⟨38286691766095348197298181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102097844709587595192795149 38286691766095348197298181)
              ·
                refine ⟨7178754706142877786993409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38286691766095348197298181 7178754706142877786993409)
                ·
                  refine ⟨5384066029607158340245057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7178754706142877786993409 5384066029607158340245057)
                  ·
                    refine ⟨4038049522205368755183793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384066029607158340245057 4038049522205368755183793)
                    ·
                      refine ⟨3028537141654026566387845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038049522205368755183793 3028537141654026566387845)
                      ·
                        rfl

theorem cell23_5898055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_5898055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898055 prefixEnd_5898055 := by exact prefixLift 5898055
  have htrace : WordTrace (prefixWord ++ tailWord_5898055) baseStart_5898055 baseEnd_5898055 := by
    simpa [prefixWord, tailWord_5898055, baseEnd_5898055] using wordTrace_append hprefix tailTrace_5898055
  have hstable : (prefixWord ++ tailWord_5898055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898055).length < 2 ^ (prefixWord ++ tailWord_5898055).sum := by decide
  have hdescent : baseEnd_5898055 < baseStart_5898055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898064 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_5898064 : Nat := 118140960795 + 5898064 * 2 ^ 59
def prefixEnd_5898064 : Nat := 4983230072969 + 3 ^ 40 * 5898064 * 2
def baseEnd_5898064 : Nat := 3028541762979917031175303

theorem tailTrace_5898064 : CollatzResearch.WordTrace tailWord_5898064 prefixEnd_5898064 3028541762979917031175303 := by
  unfold tailWord_5898064
  simp only [CollatzResearch.WordTrace]
  refine ⟨107560033452164455990166623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143413377936219274653555497 107560033452164455990166623)
  ·
    refine ⟨161340050178246683985249935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107560033452164455990166623 161340050178246683985249935)
    ·
      refine ⟨242010075267370025977874903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161340050178246683985249935 242010075267370025977874903)
      ·
        refine ⟨363015112901055038966812355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242010075267370025977874903 363015112901055038966812355)
        ·
          refine ⟨544522669351582558450218533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363015112901055038966812355 544522669351582558450218533)
          ·
            refine ⟨102098000503421729709415975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 544522669351582558450218533 102098000503421729709415975)
            ·
              refine ⟨153147000755132594564123963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102098000503421729709415975 153147000755132594564123963)
              ·
                refine ⟨229720501132698891846185945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153147000755132594564123963 229720501132698891846185945)
                ·
                  refine ⟨172290375849524168884639459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229720501132698891846185945 172290375849524168884639459)
                  ·
                    refine ⟨258435563774286253326959189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172290375849524168884639459 258435563774286253326959189)
                    ·
                      refine ⟨3028541762979917031175303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 258435563774286253326959189 3028541762979917031175303)
                      ·
                        rfl

theorem cell23_5898064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_5898064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898064 prefixEnd_5898064 := by exact prefixLift 5898064
  have htrace : WordTrace (prefixWord ++ tailWord_5898064) baseStart_5898064 baseEnd_5898064 := by
    simpa [prefixWord, tailWord_5898064, baseEnd_5898064] using wordTrace_append hprefix tailTrace_5898064
  have hstable : (prefixWord ++ tailWord_5898064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898064).length < 2 ^ (prefixWord ++ tailWord_5898064).sum := by decide
  have hdescent : baseEnd_5898064 < baseStart_5898064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
