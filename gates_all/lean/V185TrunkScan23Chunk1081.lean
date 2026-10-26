import V185TrunkScan23Chunk1080

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6399908 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_6399908 : Nat := 118140960795 + 6399908 * 2 ^ 59
def prefixEnd_6399908 : Nat := 4983230072969 + 3 ^ 40 * 6399908 * 2
def baseEnd_6399908 : Nat := 3286228948554851564217365

theorem tailTrace_6399908 : CollatzResearch.WordTrace tailWord_6399908 prefixEnd_6399908 3286228948554851564217365 := by
  unfold tailWord_6399908
  simp only [CollatzResearch.WordTrace]
  refine ⟨116711910649116904055980189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155615880865489205407973585 116711910649116904055980189)
  ·
    refine ⟨43766966493418839020992571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116711910649116904055980189 43766966493418839020992571)
    ·
      refine ⟨65650449740128258531488857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43766966493418839020992571 65650449740128258531488857)
      ·
        refine ⟨49237837305096193898616643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65650449740128258531488857 49237837305096193898616643)
        ·
          refine ⟨73856755957644290847924965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49237837305096193898616643 73856755957644290847924965)
          ·
            refine ⟨13848141742058304533985931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73856755957644290847924965 13848141742058304533985931)
            ·
              refine ⟨20772212613087456800978897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13848141742058304533985931 20772212613087456800978897)
              ·
                refine ⟨15579159459815592600734173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20772212613087456800978897 15579159459815592600734173)
                ·
                  refine ⟨5842184797430847225275315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15579159459815592600734173 5842184797430847225275315)
                  ·
                    refine ⟨8763277196146270837912973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5842184797430847225275315 8763277196146270837912973)
                    ·
                      refine ⟨3286228948554851564217365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8763277196146270837912973 3286228948554851564217365)
                      ·
                        rfl

theorem cell23_6399908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_6399908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399908 prefixEnd_6399908 := by exact prefixLift 6399908
  have htrace : WordTrace (prefixWord ++ tailWord_6399908) baseStart_6399908 baseEnd_6399908 := by
    simpa [prefixWord, tailWord_6399908, baseEnd_6399908] using wordTrace_append hprefix tailTrace_6399908
  have hstable : (prefixWord ++ tailWord_6399908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399908).length < 2 ^ (prefixWord ++ tailWord_6399908).sum := by decide
  have hdescent : baseEnd_6399908 < baseStart_6399908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399911 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6399911 : Nat := 118140960795 + 6399911 * 2 ^ 59
def prefixEnd_6399911 : Nat := 4983230072969 + 3 ^ 40 * 6399911 * 2
def baseEnd_6399911 : Nat := 1095410162998938350826617

theorem tailTrace_6399911 : CollatzResearch.WordTrace tailWord_6399911 prefixEnd_6399911 1095410162998938350826617 := by
  unfold tailWord_6399911
  simp only [CollatzResearch.WordTrace]
  refine ⟨233423930717222939624319587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155615953811481959749546391 233423930717222939624319587)
  ·
    refine ⟨350135896075834409436479381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233423930717222939624319587 350135896075834409436479381)
    ·
      refine ⟨16412620128554737942334971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 350135896075834409436479381 16412620128554737942334971)
      ·
        refine ⟨24618930192832106913502457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16412620128554737942334971 24618930192832106913502457)
        ·
          refine ⟨18464197644624080185126843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24618930192832106913502457 18464197644624080185126843)
          ·
            refine ⟨27696296466936120277690265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18464197644624080185126843 27696296466936120277690265)
            ·
              refine ⟨20772222350202090208267699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27696296466936120277690265 20772222350202090208267699)
              ·
                refine ⟨31158333525303135312401549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20772222350202090208267699 31158333525303135312401549)
                ·
                  refine ⟨11684375071988675742150581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31158333525303135312401549 11684375071988675742150581)
                  ·
                    refine ⟨1095410162998938350826617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11684375071988675742150581 1095410162998938350826617)
                    ·
                      rfl

theorem cell23_6399911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6399911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399911 prefixEnd_6399911 := by exact prefixLift 6399911
  have htrace : WordTrace (prefixWord ++ tailWord_6399911) baseStart_6399911 baseEnd_6399911 := by
    simpa [prefixWord, tailWord_6399911, baseEnd_6399911] using wordTrace_append hprefix tailTrace_6399911
  have hstable : (prefixWord ++ tailWord_6399911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399911).length < 2 ^ (prefixWord ++ tailWord_6399911).sum := by decide
  have hdescent : baseEnd_6399911 < baseStart_6399911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399912 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6399912 : Nat := 118140960795 + 6399912 * 2 ^ 59
def prefixEnd_6399912 : Nat := 4983230072969 + 3 ^ 40 * 6399912 * 2
def baseEnd_6399912 : Nat := 3286231002477469548567347

theorem tailTrace_6399912 : CollatzResearch.WordTrace tailWord_6399912 prefixEnd_6399912 3286231002477469548567347 := by
  unfold tailWord_6399912
  simp only [CollatzResearch.WordTrace]
  refine ⟨116711983595109658397552995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155615978126812877863403993 116711983595109658397552995)
  ·
    refine ⟨175067975392664487596329493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116711983595109658397552995 175067975392664487596329493)
    ·
      refine ⟨8206311346531147856077945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175067975392664487596329493 8206311346531147856077945)
      ·
        refine ⟨6154733509898360892058459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8206311346531147856077945 6154733509898360892058459)
        ·
          refine ⟨9232100264847541338087689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154733509898360892058459 9232100264847541338087689)
          ·
            refine ⟨6924075198635656003565767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9232100264847541338087689 6924075198635656003565767)
            ·
              refine ⟨10386112797953484005348651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924075198635656003565767 10386112797953484005348651)
              ·
                refine ⟨15579169196930226008022977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10386112797953484005348651 15579169196930226008022977)
                ·
                  refine ⟨11684376897697669506017233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15579169196930226008022977 11684376897697669506017233)
                  ·
                    refine ⟨8763282673273252129512925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11684376897697669506017233 8763282673273252129512925)
                    ·
                      refine ⟨3286231002477469548567347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8763282673273252129512925 3286231002477469548567347)
                      ·
                        rfl

theorem cell23_6399912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6399912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399912 prefixEnd_6399912 := by exact prefixLift 6399912
  have htrace : WordTrace (prefixWord ++ tailWord_6399912) baseStart_6399912 baseEnd_6399912 := by
    simpa [prefixWord, tailWord_6399912, baseEnd_6399912] using wordTrace_append hprefix tailTrace_6399912
  have hstable : (prefixWord ++ tailWord_6399912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399912).length < 2 ^ (prefixWord ++ tailWord_6399912).sum := by decide
  have hdescent : baseEnd_6399912 < baseStart_6399912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399925 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_6399925 : Nat := 118140960795 + 6399925 * 2 ^ 59
def prefixEnd_6399925 : Nat := 4983230072969 + 3 ^ 40 * 6399925 * 2
def baseEnd_6399925 : Nat := 3286237677725977997704787

theorem tailTrace_6399925 : CollatzResearch.WordTrace tailWord_6399925 prefixEnd_6399925 3286237677725977997704787 := by
  unfold tailWord_6399925
  simp only [CollatzResearch.WordTrace]
  refine ⟨233424441339172220015329229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155616294226114813343552819 233424441339172220015329229)
  ·
    refine ⟨87534165502189582505748461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233424441339172220015329229 87534165502189582505748461)
    ·
      refine ⟨32825312063321093439655673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87534165502189582505748461 32825312063321093439655673)
      ·
        refine ⟨24618984047490820079741755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32825312063321093439655673 24618984047490820079741755)
        ·
          refine ⟨36928476071236230119612633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24618984047490820079741755 36928476071236230119612633)
          ·
            refine ⟨27696357053427172589709475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36928476071236230119612633 27696357053427172589709475)
            ·
              refine ⟨41544535580140758884564213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27696357053427172589709475 41544535580140758884564213)
              ·
                refine ⟨3894800210638196145427895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41544535580140758884564213 3894800210638196145427895)
                ·
                  refine ⟨5842200315957294218141843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894800210638196145427895 5842200315957294218141843)
                  ·
                    refine ⟨8763300473935941327212765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5842200315957294218141843 8763300473935941327212765)
                    ·
                      refine ⟨3286237677725977997704787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8763300473935941327212765 3286237677725977997704787)
                      ·
                        rfl

theorem cell23_6399925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_6399925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399925 prefixEnd_6399925 := by exact prefixLift 6399925
  have htrace : WordTrace (prefixWord ++ tailWord_6399925) baseStart_6399925 baseEnd_6399925 := by
    simpa [prefixWord, tailWord_6399925, baseEnd_6399925] using wordTrace_append hprefix tailTrace_6399925
  have hstable : (prefixWord ++ tailWord_6399925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399925).length < 2 ^ (prefixWord ++ tailWord_6399925).sum := by decide
  have hdescent : baseEnd_6399925 < baseStart_6399925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399941 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_6399941 : Nat := 118140960795 + 6399941 * 2 ^ 59
def prefixEnd_6399941 : Nat := 4983230072969 + 3 ^ 40 * 6399941 * 2
def baseEnd_6399941 : Nat := 1095415297805483311701571

theorem tailTrace_6399941 : CollatzResearch.WordTrace tailWord_6399941 prefixEnd_6399941 1095415297805483311701571 := by
  unfold tailWord_6399941
  simp only [CollatzResearch.WordTrace]
  refine ⟨233425024907114254747911677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155616683271409503165274451 233425024907114254747911677)
  ·
    refine ⟨87534384340167845530466879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233425024907114254747911677 87534384340167845530466879)
    ·
      refine ⟨131301576510251768295700319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87534384340167845530466879 131301576510251768295700319)
      ·
        refine ⟨196952364765377652443550479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131301576510251768295700319 196952364765377652443550479)
        ·
          refine ⟨295428547148066478665325719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196952364765377652443550479 295428547148066478665325719)
          ·
            refine ⟨443142820722099717997988579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295428547148066478665325719 443142820722099717997988579)
            ·
              refine ⟨664714231083149576996982869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443142820722099717997988579 664714231083149576996982869)
              ·
                refine ⟨7789619895505659105433393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 664714231083149576996982869 7789619895505659105433393)
                ·
                  refine ⟨5842214921629244329075045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789619895505659105433393 5842214921629244329075045)
                  ·
                    refine ⟨1095415297805483311701571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842214921629244329075045 1095415297805483311701571)
                    ·
                      rfl

theorem cell23_6399941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_6399941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399941 prefixEnd_6399941 := by exact prefixLift 6399941
  have htrace : WordTrace (prefixWord ++ tailWord_6399941) baseStart_6399941 baseEnd_6399941 := by
    simpa [prefixWord, tailWord_6399941, baseEnd_6399941] using wordTrace_append hprefix tailTrace_6399941
  have hstable : (prefixWord ++ tailWord_6399941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399941).length < 2 ^ (prefixWord ++ tailWord_6399941).sum := by decide
  have hdescent : baseEnd_6399941 < baseStart_6399941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399961 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_6399961 : Nat := 118140960795 + 6399961 * 2 ^ 59
def prefixEnd_6399961 : Nat := 4983230072969 + 3 ^ 40 * 6399961 * 2
def baseEnd_6399961 : Nat := 3286256163029539856854621

theorem tailTrace_6399961 : CollatzResearch.WordTrace tailWord_6399961 prefixEnd_6399961 3286256163029539856854621 := by
  unfold tailWord_6399961
  simp only [CollatzResearch.WordTrace]
  refine ⟨233425754367041798163639737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155617169578027865442426491 233425754367041798163639737)
  ·
    refine ⟨175069315775281348622729803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233425754367041798163639737 175069315775281348622729803)
    ·
      refine ⟨262603973662922022934094705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175069315775281348622729803 262603973662922022934094705)
      ·
        refine ⟨196952980247191517200571029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262603973662922022934094705 196952980247191517200571029)
        ·
          refine ⟨9232170949087102368776767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196952980247191517200571029 9232170949087102368776767)
          ·
            refine ⟨13848256423630653553165151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232170949087102368776767 13848256423630653553165151)
            ·
              refine ⟨20772384635445980329747727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13848256423630653553165151 20772384635445980329747727)
              ·
                refine ⟨31158576953168970494621591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20772384635445980329747727 31158576953168970494621591)
                ·
                  refine ⟨46737865429753455741932387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31158576953168970494621591 46737865429753455741932387)
                  ·
                    refine ⟨70106798144630183612898581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46737865429753455741932387 70106798144630183612898581)
                    ·
                      refine ⟨3286256163029539856854621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70106798144630183612898581 3286256163029539856854621)
                      ·
                        rfl

theorem cell23_6399961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_6399961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399961 prefixEnd_6399961 := by exact prefixLift 6399961
  have htrace : WordTrace (prefixWord ++ tailWord_6399961) baseStart_6399961 baseEnd_6399961 := by
    simpa [prefixWord, tailWord_6399961, baseEnd_6399961] using wordTrace_append hprefix tailTrace_6399961
  have hstable : (prefixWord ++ tailWord_6399961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399961).length < 2 ^ (prefixWord ++ tailWord_6399961).sum := by decide
  have hdescent : baseEnd_6399961 < baseStart_6399961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399965 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_6399965 : Nat := 118140960795 + 6399965 * 2 ^ 59
def prefixEnd_6399965 : Nat := 4983230072969 + 3 ^ 40 * 6399965 * 2
def baseEnd_6399965 : Nat := 3286258216952157841204603

theorem tailTrace_6399965 : CollatzResearch.WordTrace tailWord_6399965 prefixEnd_6399965 3286258216952157841204603 := by
  unfold tailWord_6399965
  simp only [CollatzResearch.WordTrace]
  refine ⟨233425900259027306846785349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155617266839351537897856899 233425900259027306846785349)
  ·
    refine ⟨43767356298567620033772253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233425900259027306846785349 43767356298567620033772253)
    ·
      refine ⟨16412758611962857512664595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43767356298567620033772253 16412758611962857512664595)
      ·
        refine ⟨24619137917944286268996893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16412758611962857512664595 24619137917944286268996893)
        ·
          refine ⟨9232176719229107350873835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24619137917944286268996893 9232176719229107350873835)
          ·
            refine ⟨13848265078843661026310753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232176719229107350873835 13848265078843661026310753)
            ·
              refine ⟨10386198809132745769733065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13848265078843661026310753 10386198809132745769733065)
              ·
                refine ⟨7789649106849559327299799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10386198809132745769733065 7789649106849559327299799)
                ·
                  refine ⟨11684473660274338990949699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7789649106849559327299799 11684473660274338990949699)
                  ·
                    refine ⟨17526710490411508486424549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11684473660274338990949699 17526710490411508486424549)
                    ·
                      refine ⟨3286258216952157841204603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17526710490411508486424549 3286258216952157841204603)
                      ·
                        rfl

theorem cell23_6399965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_6399965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399965 prefixEnd_6399965 := by exact prefixLift 6399965
  have htrace : WordTrace (prefixWord ++ tailWord_6399965) baseStart_6399965 baseEnd_6399965 := by
    simpa [prefixWord, tailWord_6399965, baseEnd_6399965] using wordTrace_append hprefix tailTrace_6399965
  have hstable : (prefixWord ++ tailWord_6399965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399965).length < 2 ^ (prefixWord ++ tailWord_6399965).sum := by decide
  have hdescent : baseEnd_6399965 < baseStart_6399965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399971 : List Nat := [1, 1, 1, 6, 1, 2, 4, 7]
def baseStart_6399971 : Nat := 118140960795 + 6399971 * 2 ^ 59
def prefixEnd_6399971 : Nat := 4983230072969 + 3 ^ 40 * 6399971 * 2
def baseEnd_6399971 : Nat := 121713381401336474730725

theorem tailTrace_6399971 : CollatzResearch.WordTrace tailWord_6399971 prefixEnd_6399971 121713381401336474730725 := by
  unfold tailWord_6399971
  simp only [CollatzResearch.WordTrace]
  refine ⟨233426119097005569871503767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155617412731337046581002511 233426119097005569871503767)
  ·
    refine ⟨350139178645508354807255651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233426119097005569871503767 350139178645508354807255651)
    ·
      refine ⟨525208767968262532210883477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350139178645508354807255651 525208767968262532210883477)
      ·
        refine ⟨24619160998512306197385163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 525208767968262532210883477 24619160998512306197385163)
        ·
          refine ⟨36928741497768459296077745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24619160998512306197385163 36928741497768459296077745)
          ·
            refine ⟨27696556123326344472058309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36928741497768459296077745 27696556123326344472058309)
            ·
              refine ⟨5193104273123689588510933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27696556123326344472058309 5193104273123689588510933)
              ·
                refine ⟨121713381401336474730725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5193104273123689588510933 121713381401336474730725)
                ·
                  rfl

theorem cell23_6399971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 7].length) (baseStart_6399971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399971 prefixEnd_6399971 := by exact prefixLift 6399971
  have htrace : WordTrace (prefixWord ++ tailWord_6399971) baseStart_6399971 baseEnd_6399971 := by
    simpa [prefixWord, tailWord_6399971, baseEnd_6399971] using wordTrace_append hprefix tailTrace_6399971
  have hstable : (prefixWord ++ tailWord_6399971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399971).length < 2 ^ (prefixWord ++ tailWord_6399971).sum := by decide
  have hdescent : baseEnd_6399971 < baseStart_6399971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400008 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_6400008 : Nat := 118140960795 + 6400008 * 2 ^ 59
def prefixEnd_6400008 : Nat := 4983230072969 + 3 ^ 40 * 6400008 * 2
def baseEnd_6400008 : Nat := 3286280296620301172966905

theorem tailTrace_6400008 : CollatzResearch.WordTrace tailWord_6400008 prefixEnd_6400008 3286280296620301172966905 := by
  unfold tailWord_6400008
  simp only [CollatzResearch.WordTrace]
  refine ⟨116713734298935762595300339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155618312398581016793733785 116713734298935762595300339)
  ·
    refine ⟨175070601448403643892950509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116713734298935762595300339 175070601448403643892950509)
    ·
      refine ⟨65651475543151366459856441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175070601448403643892950509 65651475543151366459856441)
      ·
        refine ⟨49238606657363524844892331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65651475543151366459856441 49238606657363524844892331)
        ·
          refine ⟨73857909986045287267338497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49238606657363524844892331 73857909986045287267338497)
          ·
            refine ⟨55393432489533965450503873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73857909986045287267338497 55393432489533965450503873)
            ·
              refine ⟨41545074367150474087877905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55393432489533965450503873 41545074367150474087877905)
              ·
                refine ⟨31158805775362855565908429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41545074367150474087877905 31158805775362855565908429)
                ·
                  refine ⟨11684552165761070837215661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31158805775362855565908429 11684552165761070837215661)
                  ·
                    refine ⟨4381707062160401563955873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11684552165761070837215661 4381707062160401563955873)
                    ·
                      refine ⟨3286280296620301172966905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381707062160401563955873 3286280296620301172966905)
                      ·
                        rfl

theorem cell23_6400008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_6400008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400008 prefixEnd_6400008 := by exact prefixLift 6400008
  have htrace : WordTrace (prefixWord ++ tailWord_6400008) baseStart_6400008 baseEnd_6400008 := by
    simpa [prefixWord, tailWord_6400008, baseEnd_6400008] using wordTrace_append hprefix tailTrace_6400008
  have hstable : (prefixWord ++ tailWord_6400008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400008).length < 2 ^ (prefixWord ++ tailWord_6400008).sum := by decide
  have hdescent : baseEnd_6400008 < baseStart_6400008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400044 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 11]
def baseStart_6400044 : Nat := 118140960795 + 6400044 * 2 ^ 59
def prefixEnd_6400044 : Nat := 4983230072969 + 3 ^ 40 * 6400044 * 2
def baseEnd_6400044 : Nat := 365144309102651448012971

theorem tailTrace_6400044 : CollatzResearch.WordTrace tailWord_6400044 prefixEnd_6400044 365144309102651448012971 := by
  unfold tailWord_6400044
  simp only [CollatzResearch.WordTrace]
  refine ⟨116714390812870551669455593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155619187750494068892607457 116714390812870551669455593)
  ·
    refine ⟨87535793109652913752091695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116714390812870551669455593 87535793109652913752091695)
    ·
      refine ⟨131303689664479370628137543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87535793109652913752091695 131303689664479370628137543)
      ·
        refine ⟨196955534496719055942206315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131303689664479370628137543 196955534496719055942206315)
        ·
          refine ⟨295433301745078583913309473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196955534496719055942206315 295433301745078583913309473)
          ·
            refine ⟨221574976308808937934982105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295433301745078583913309473 221574976308808937934982105)
            ·
              refine ⟨166181232231606703451236579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221574976308808937934982105 166181232231606703451236579)
              ·
                refine ⟨249271848347410055176854869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166181232231606703451236579 249271848347410055176854869)
                ·
                  refine ⟨365144309102651448012971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 249271848347410055176854869 365144309102651448012971)
                  ·
                    rfl

theorem cell23_6400044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_6400044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400044 prefixEnd_6400044 := by exact prefixLift 6400044
  have htrace : WordTrace (prefixWord ++ tailWord_6400044) baseStart_6400044 baseEnd_6400044 := by
    simpa [prefixWord, tailWord_6400044, baseEnd_6400044] using wordTrace_append hprefix tailTrace_6400044
  have hstable : (prefixWord ++ tailWord_6400044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400044).length < 2 ^ (prefixWord ++ tailWord_6400044).sum := by decide
  have hdescent : baseEnd_6400044 < baseStart_6400044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400055 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 2, 2, 2]
def baseStart_6400055 : Nat := 118140960795 + 6400055 * 2 ^ 59
def prefixEnd_6400055 : Nat := 4983230072969 + 3 ^ 40 * 6400055 * 2
def baseEnd_6400055 : Nat := 3286304430211062489079189

theorem tailTrace_6400055 : CollatzResearch.WordTrace tailWord_6400055 prefixEnd_6400055 3286304430211062489079189 := by
  unfold tailWord_6400055
  simp only [CollatzResearch.WordTrace]
  refine ⟨233429182828701252217561619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155619455219134168145041079 233429182828701252217561619)
  ·
    refine ⟨350143774243051878326342429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233429182828701252217561619 350143774243051878326342429)
    ·
      refine ⟨131303915341144454372378411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350143774243051878326342429 131303915341144454372378411)
      ·
        refine ⟨196955873011716681558567617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131303915341144454372378411 196955873011716681558567617)
        ·
          refine ⟨147716904758787511168925713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196955873011716681558567617 147716904758787511168925713)
          ·
            refine ⟨110787678569090633376694285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147716904758787511168925713 110787678569090633376694285)
            ·
              refine ⟨41545379463408987516260357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110787678569090633376694285 41545379463408987516260357)
              ·
                refine ⟨7789758649389185159298817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41545379463408987516260357 7789758649389185159298817)
                ·
                  refine ⟨5842318987041888869474113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789758649389185159298817 5842318987041888869474113)
                  ·
                    refine ⟨4381739240281416652105585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5842318987041888869474113 4381739240281416652105585)
                    ·
                      refine ⟨3286304430211062489079189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381739240281416652105585 3286304430211062489079189)
                      ·
                        rfl

theorem cell23_6400055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_6400055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400055 prefixEnd_6400055 := by exact prefixLift 6400055
  have htrace : WordTrace (prefixWord ++ tailWord_6400055) baseStart_6400055 baseEnd_6400055 := by
    simpa [prefixWord, tailWord_6400055, baseEnd_6400055] using wordTrace_append hprefix tailTrace_6400055
  have hstable : (prefixWord ++ tailWord_6400055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400055).length < 2 ^ (prefixWord ++ tailWord_6400055).sum := by decide
  have hdescent : baseEnd_6400055 < baseStart_6400055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400061 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 7]
def baseStart_6400061 : Nat := 118140960795 + 6400061 * 2 ^ 59
def prefixEnd_6400061 : Nat := 4983230072969 + 3 ^ 40 * 6400061 * 2
def baseEnd_6400061 : Nat := 365145279010554385067129

theorem tailTrace_6400061 : CollatzResearch.WordTrace tailWord_6400061 prefixEnd_6400061 365145279010554385067129 := by
  unfold tailWord_6400061
  simp only [CollatzResearch.WordTrace]
  refine ⟨233429401666679515242280037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155619601111119676828186691 233429401666679515242280037)
  ·
    refine ⟨43768012812502409107927507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233429401666679515242280037 43768012812502409107927507)
    ·
      refine ⟨65652019218753613661891261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43768012812502409107927507 65652019218753613661891261)
      ·
        refine ⟨24619507207032605123209223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65652019218753613661891261 24619507207032605123209223)
        ·
          refine ⟨36929260810548907684813835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24619507207032605123209223 36929260810548907684813835)
          ·
            refine ⟨55393891215823361527220753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36929260810548907684813835 55393891215823361527220753)
            ·
              refine ⟨41545418411867521145415565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55393891215823361527220753 41545418411867521145415565)
              ·
                refine ⟨15579531904450320429530837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41545418411867521145415565 15579531904450320429530837)
                ·
                  refine ⟨365145279010554385067129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15579531904450320429530837 365145279010554385067129)
                  ·
                    rfl

theorem cell23_6400061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_6400061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400061 prefixEnd_6400061 := by exact prefixLift 6400061
  have htrace : WordTrace (prefixWord ++ tailWord_6400061) baseStart_6400061 baseEnd_6400061 := by
    simpa [prefixWord, tailWord_6400061, baseEnd_6400061] using wordTrace_append hprefix tailTrace_6400061
  have hstable : (prefixWord ++ tailWord_6400061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400061).length < 2 ^ (prefixWord ++ tailWord_6400061).sum := by decide
  have hdescent : baseEnd_6400061 < baseStart_6400061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400106 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_6400106 : Nat := 118140960795 + 6400106 * 2 ^ 59
def prefixEnd_6400106 : Nat := 4983230072969 + 3 ^ 40 * 6400106 * 2
def baseEnd_6400106 : Nat := 3286330617724441789541455

theorem tailTrace_6400106 : CollatzResearch.WordTrace tailWord_6400106 prefixEnd_6400106 3286330617724441789541455 := by
  unfold tailWord_6400106
  simp only [CollatzResearch.WordTrace]
  refine ⟨58357760737879121981917043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155620695301010991951778781 58357760737879121981917043)
  ·
    refine ⟨87536641106818682972875565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58357760737879121981917043 87536641106818682972875565)
    ·
      refine ⟨32826240415057006114828337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87536641106818682972875565 32826240415057006114828337)
      ·
        refine ⟨24619680311292754586121253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32826240415057006114828337 24619680311292754586121253)
        ·
          refine ⟨4616190058367391484897735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24619680311292754586121253 4616190058367391484897735)
          ·
            refine ⟨6924285087551087227346603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4616190058367391484897735 6924285087551087227346603)
            ·
              refine ⟨10386427631326630841019905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924285087551087227346603 10386427631326630841019905)
              ·
                refine ⟨7789820723494973130764929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10386427631326630841019905 7789820723494973130764929)
                ·
                  refine ⟨5842365542621229848073697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789820723494973130764929 5842365542621229848073697)
                  ·
                    refine ⟨4381774156965922386055273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5842365542621229848073697 4381774156965922386055273)
                    ·
                      refine ⟨3286330617724441789541455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381774156965922386055273 3286330617724441789541455)
                      ·
                        rfl

theorem cell23_6400106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_6400106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400106 prefixEnd_6400106 := by exact prefixLift 6400106
  have htrace : WordTrace (prefixWord ++ tailWord_6400106) baseStart_6400106 baseEnd_6400106 := by
    simpa [prefixWord, tailWord_6400106, baseEnd_6400106] using wordTrace_append hprefix tailTrace_6400106
  have hstable : (prefixWord ++ tailWord_6400106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400106).length < 2 ^ (prefixWord ++ tailWord_6400106).sum := by decide
  have hdescent : baseEnd_6400106 < baseStart_6400106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400229 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6400229 : Nat := 118140960795 + 6400229 * 2 ^ 59
def prefixEnd_6400229 : Nat := 4983230072969 + 3 ^ 40 * 6400229 * 2
def baseEnd_6400229 : Nat := 3286393775844944808303389

theorem tailTrace_6400229 : CollatzResearch.WordTrace tailWord_6400229 prefixEnd_6400229 3286393775844944808303389 := by
  unfold tailWord_6400229
  simp only [CollatzResearch.WordTrace]
  refine ⟨233435529130070879934395741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155623686086713919956263827 233435529130070879934395741)
  ·
    refine ⟨87538323423776579975398403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233435529130070879934395741 87538323423776579975398403)
    ·
      refine ⟨131307485135664869963097605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87538323423776579975398403 131307485135664869963097605)
      ·
        refine ⟨24620153462937163118080801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131307485135664869963097605 24620153462937163118080801)
        ·
          refine ⟨18465115097202872338560601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24620153462937163118080801 18465115097202872338560601)
          ·
            refine ⟨13848836322902154253920451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18465115097202872338560601 13848836322902154253920451)
            ·
              refine ⟨20773254484353231380880677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13848836322902154253920451 20773254484353231380880677)
              ·
                refine ⟨3894985215816230883915127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20773254484353231380880677 3894985215816230883915127)
                ·
                  refine ⟨5842477823724346325872691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894985215816230883915127 5842477823724346325872691)
                  ·
                    refine ⟨8763716735586519488809037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5842477823724346325872691 8763716735586519488809037)
                    ·
                      refine ⟨3286393775844944808303389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8763716735586519488809037 3286393775844944808303389)
                      ·
                        rfl

theorem cell23_6400229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6400229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400229 prefixEnd_6400229 := by exact prefixLift 6400229
  have htrace : WordTrace (prefixWord ++ tailWord_6400229) baseStart_6400229 baseEnd_6400229 := by
    simpa [prefixWord, tailWord_6400229, baseEnd_6400229] using wordTrace_append hprefix tailTrace_6400229
  have hstable : (prefixWord ++ tailWord_6400229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400229).length < 2 ^ (prefixWord ++ tailWord_6400229).sum := by decide
  have hdescent : baseEnd_6400229 < baseStart_6400229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400238 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6400238 : Nat := 118140960795 + 6400238 * 2 ^ 59
def prefixEnd_6400238 : Nat := 4983230072969 + 3 ^ 40 * 6400238 * 2
def baseEnd_6400238 : Nat := 3286398397170835273090847

theorem tailTrace_6400238 : CollatzResearch.WordTrace tailWord_6400238 prefixEnd_6400238 3286398397170835273090847 := by
  unfold tailWord_6400238
  simp only [CollatzResearch.WordTrace]
  refine ⟨29179482173379784308934171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155623904924692182980982245 29179482173379784308934171)
  ·
    refine ⟨43769223260069676463401257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29179482173379784308934171 43769223260069676463401257)
    ·
      refine ⟨32826917445052257347550943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43769223260069676463401257 32826917445052257347550943)
      ·
        refine ⟨49240376167578386021326415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32826917445052257347550943 49240376167578386021326415)
        ·
          refine ⟨73860564251367579031989623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49240376167578386021326415 73860564251367579031989623)
          ·
            refine ⟨110790846377051368547984435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73860564251367579031989623 110790846377051368547984435)
            ·
              refine ⟨166186269565577052821976653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110790846377051368547984435 166186269565577052821976653)
              ·
                refine ⟨62319851087091394808241245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166186269565577052821976653 62319851087091394808241245)
                ·
                  refine ⟨23369944157659273053090467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62319851087091394808241245 23369944157659273053090467)
                  ·
                    refine ⟨35054916236488909579635701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23369944157659273053090467 35054916236488909579635701)
                    ·
                      refine ⟨3286398397170835273090847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35054916236488909579635701 3286398397170835273090847)
                      ·
                        rfl

theorem cell23_6400238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6400238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400238 prefixEnd_6400238 := by exact prefixLift 6400238
  have htrace : WordTrace (prefixWord ++ tailWord_6400238) baseStart_6400238 baseEnd_6400238 := by
    simpa [prefixWord, tailWord_6400238, baseEnd_6400238] using wordTrace_append hprefix tailTrace_6400238
  have hstable : (prefixWord ++ tailWord_6400238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400238).length < 2 ^ (prefixWord ++ tailWord_6400238).sum := by decide
  have hdescent : baseEnd_6400238 < baseStart_6400238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400251 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_6400251 : Nat := 118140960795 + 6400251 * 2 ^ 59
def prefixEnd_6400251 : Nat := 4983230072969 + 3 ^ 40 * 6400251 * 2
def baseEnd_6400251 : Nat := 3286405072419343722228287

theorem tailTrace_6400251 : CollatzResearch.WordTrace tailWord_6400251 prefixEnd_6400251 3286405072419343722228287 := by
  unfold tailWord_6400251
  simp only [CollatzResearch.WordTrace]
  refine ⟨233436331535991177691696607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155624221023994118461131071 233436331535991177691696607)
  ·
    refine ⟨350154497303986766537544911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233436331535991177691696607 350154497303986766537544911)
    ·
      refine ⟨525231745955980149806317367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350154497303986766537544911 525231745955980149806317367)
      ·
        refine ⟨787847618933970224709476051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525231745955980149806317367 787847618933970224709476051)
        ·
          refine ⟨1181771428400955337064214077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787847618933970224709476051 1181771428400955337064214077)
          ·
            refine ⟨443164285650358251399080279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1181771428400955337064214077 443164285650358251399080279)
            ·
              refine ⟨664746428475537377098620419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443164285650358251399080279 664746428475537377098620419)
              ·
                refine ⟨997119642713306065647930629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664746428475537377098620419 997119642713306065647930629)
                ·
                  refine ⟨186959933008744887308986993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997119642713306065647930629 186959933008744887308986993)
                  ·
                    refine ⟨140219949756558665481740245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186959933008744887308986993 140219949756558665481740245)
                    ·
                      refine ⟨3286405072419343722228287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140219949756558665481740245 3286405072419343722228287)
                      ·
                        rfl

theorem cell23_6400251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_6400251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400251 prefixEnd_6400251 := by exact prefixLift 6400251
  have htrace : WordTrace (prefixWord ++ tailWord_6400251) baseStart_6400251 baseEnd_6400251 := by
    simpa [prefixWord, tailWord_6400251, baseEnd_6400251] using wordTrace_append hprefix tailTrace_6400251
  have hstable : (prefixWord ++ tailWord_6400251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400251).length < 2 ^ (prefixWord ++ tailWord_6400251).sum := by decide
  have hdescent : baseEnd_6400251 < baseStart_6400251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400252 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_6400252 : Nat := 118140960795 + 6400252 * 2 ^ 59
def prefixEnd_6400252 : Nat := 4983230072969 + 3 ^ 40 * 6400252 * 2
def baseEnd_6400252 : Nat := 3286405585899998218315783

theorem tailTrace_6400252 : CollatzResearch.WordTrace tailWord_6400252 prefixEnd_6400252 3286405585899998218315783 := by
  unfold tailWord_6400252
  simp only [CollatzResearch.WordTrace]
  refine ⟨116718184004493777431241505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155624245339325036574988673 116718184004493777431241505)
  ·
    refine ⟨87538638003370333073431129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116718184004493777431241505 87538638003370333073431129)
    ·
      refine ⟨65653978502527749805073347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87538638003370333073431129 65653978502527749805073347)
      ·
        refine ⟨98480967753791624707610021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65653978502527749805073347 98480967753791624707610021)
        ·
          refine ⟨18465181453835929632676879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98480967753791624707610021 18465181453835929632676879)
          ·
            refine ⟨27697772180753894449015319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18465181453835929632676879 27697772180753894449015319)
            ·
              refine ⟨41546658271130841673522979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27697772180753894449015319 41546658271130841673522979)
              ·
                refine ⟨62319987406696262510284469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41546658271130841673522979 62319987406696262510284469)
                ·
                  refine ⟨5842498819377774610339169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62319987406696262510284469 5842498819377774610339169)
                  ·
                    refine ⟨4381874114533330957754377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5842498819377774610339169 4381874114533330957754377)
                    ·
                      refine ⟨3286405585899998218315783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381874114533330957754377 3286405585899998218315783)
                      ·
                        rfl

theorem cell23_6400252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_6400252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400252 prefixEnd_6400252 := by exact prefixLift 6400252
  have htrace : WordTrace (prefixWord ++ tailWord_6400252) baseStart_6400252 baseEnd_6400252 := by
    simpa [prefixWord, tailWord_6400252, baseEnd_6400252] using wordTrace_append hprefix tailTrace_6400252
  have hstable : (prefixWord ++ tailWord_6400252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400252).length < 2 ^ (prefixWord ++ tailWord_6400252).sum := by decide
  have hdescent : baseEnd_6400252 < baseStart_6400252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400255 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 3]
def baseStart_6400255 : Nat := 118140960795 + 6400255 * 2 ^ 59
def prefixEnd_6400255 : Nat := 4983230072969 + 3 ^ 40 * 6400255 * 2
def baseEnd_6400255 : Nat := 3286407126341961706578269

theorem tailTrace_6400255 : CollatzResearch.WordTrace tailWord_6400255 prefixEnd_6400255 3286407126341961706578269 := by
  unfold tailWord_6400255
  simp only [CollatzResearch.WordTrace]
  refine ⟨233436477427976686374842219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155624318285317790916561479 233436477427976686374842219)
  ·
    refine ⟨350154716141965029562263329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233436477427976686374842219 350154716141965029562263329)
    ·
      refine ⟨262616037106473772171697497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350154716141965029562263329 262616037106473772171697497)
      ·
        refine ⟨196962027829855329128773123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262616037106473772171697497 196962027829855329128773123)
        ·
          refine ⟨295443041744782993693159685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196962027829855329128773123 295443041744782993693159685)
          ·
            refine ⟨55395570327146811317467441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295443041744782993693159685 55395570327146811317467441)
            ·
              refine ⟨41546677745360108488100581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55395570327146811317467441 41546677745360108488100581)
              ·
                refine ⟨7790002077255020341518859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41546677745360108488100581 7790002077255020341518859)
                ·
                  refine ⟨11685003115882530512278289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7790002077255020341518859 11685003115882530512278289)
                  ·
                    refine ⟨8763752336911897884208717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11685003115882530512278289 8763752336911897884208717)
                    ·
                      refine ⟨3286407126341961706578269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8763752336911897884208717 3286407126341961706578269)
                      ·
                        rfl

theorem cell23_6400255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_6400255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400255 prefixEnd_6400255 := by exact prefixLift 6400255
  have htrace : WordTrace (prefixWord ++ tailWord_6400255) baseStart_6400255 baseEnd_6400255 := by
    simpa [prefixWord, tailWord_6400255, baseEnd_6400255] using wordTrace_append hprefix tailTrace_6400255
  have hstable : (prefixWord ++ tailWord_6400255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400255).length < 2 ^ (prefixWord ++ tailWord_6400255).sum := by decide
  have hdescent : baseEnd_6400255 < baseStart_6400255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400286 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6400286 : Nat := 118140960795 + 6400286 * 2 ^ 59
def prefixEnd_6400286 : Nat := 4983230072969 + 3 ^ 40 * 6400286 * 2
def baseEnd_6400286 : Nat := 3286423044242251085290627

theorem tailTrace_6400286 : CollatzResearch.WordTrace tailWord_6400286 prefixEnd_6400286 3286423044242251085290627 := by
  unfold tailWord_6400286
  simp only [CollatzResearch.WordTrace]
  refine ⟨29179701011358047333652589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155625072060576252446147141 29179701011358047333652589)
  ·
    refine ⟨10942387879259267750119721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29179701011358047333652589 10942387879259267750119721)
    ·
      refine ⟨8206790909444450812589791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10942387879259267750119721 8206790909444450812589791)
      ·
        refine ⟨12310186364166676218884687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8206790909444450812589791 12310186364166676218884687)
        ·
          refine ⟨18465279546250014328327031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310186364166676218884687 18465279546250014328327031)
          ·
            refine ⟨27697919319375021492490547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18465279546250014328327031 27697919319375021492490547)
            ·
              refine ⟨41546878979062532238735821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27697919319375021492490547 41546878979062532238735821)
              ·
                refine ⟨15580079617148449589525933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41546878979062532238735821 15580079617148449589525933)
                ·
                  refine ⟨5842529856430668596072225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15580079617148449589525933 5842529856430668596072225)
                  ·
                    refine ⟨4381897392323001447054169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5842529856430668596072225 4381897392323001447054169)
                    ·
                      refine ⟨3286423044242251085290627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381897392323001447054169 3286423044242251085290627)
                      ·
                        rfl

theorem cell23_6400286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6400286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400286 prefixEnd_6400286 := by exact prefixLift 6400286
  have htrace : WordTrace (prefixWord ++ tailWord_6400286) baseStart_6400286 baseEnd_6400286 := by
    simpa [prefixWord, tailWord_6400286, baseEnd_6400286] using wordTrace_append hprefix tailTrace_6400286
  have hstable : (prefixWord ++ tailWord_6400286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400286).length < 2 ^ (prefixWord ++ tailWord_6400286).sum := by decide
  have hdescent : baseEnd_6400286 < baseStart_6400286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400312 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 1, 3, 2]
def baseStart_6400312 : Nat := 118140960795 + 6400312 * 2 ^ 59
def prefixEnd_6400312 : Nat := 4983230072969 + 3 ^ 40 * 6400312 * 2
def baseEnd_6400312 : Nat := 3286436394739267983565507

theorem tailTrace_6400312 : CollatzResearch.WordTrace tailWord_6400312 prefixEnd_6400312 3286436394739267983565507 := by
  unfold tailWord_6400312
  simp only [CollatzResearch.WordTrace]
  refine ⟨116719278194385092554833595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155625704259180123406444793 116719278194385092554833595)
  ·
    refine ⟨175078917291577638832250393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116719278194385092554833595 175078917291577638832250393)
    ·
      refine ⟨131309187968683229124187795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175078917291577638832250393 131309187968683229124187795)
      ·
        refine ⟨196963781953024843686281693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131309187968683229124187795 196963781953024843686281693)
        ·
          refine ⟨73861418232384316382355635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196963781953024843686281693 73861418232384316382355635)
          ·
            refine ⟨110792127348576474573533453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73861418232384316382355635 110792127348576474573533453)
            ·
              refine ⟨41547047755716177965075045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110792127348576474573533453 41547047755716177965075045)
              ·
                refine ⟨7790071454196783368451571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41547047755716177965075045 7790071454196783368451571)
                ·
                  refine ⟨11685107181295175052677357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7790071454196783368451571 11685107181295175052677357)
                  ·
                    refine ⟨4381915192985690644754009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11685107181295175052677357 4381915192985690644754009)
                    ·
                      refine ⟨3286436394739267983565507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381915192985690644754009 3286436394739267983565507)
                      ·
                        rfl

theorem cell23_6400312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_6400312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400312 prefixEnd_6400312 := by exact prefixLift 6400312
  have htrace : WordTrace (prefixWord ++ tailWord_6400312) baseStart_6400312 baseEnd_6400312 := by
    simpa [prefixWord, tailWord_6400312, baseEnd_6400312] using wordTrace_append hprefix tailTrace_6400312
  have hstable : (prefixWord ++ tailWord_6400312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400312).length < 2 ^ (prefixWord ++ tailWord_6400312).sum := by decide
  have hdescent : baseEnd_6400312 < baseStart_6400312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400328 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_6400328 : Nat := 118140960795 + 6400328 * 2 ^ 59
def prefixEnd_6400328 : Nat := 4983230072969 + 3 ^ 40 * 6400328 * 2
def baseEnd_6400328 : Nat := 3286444610429739920965433

theorem tailTrace_6400328 : CollatzResearch.WordTrace tailWord_6400328 prefixEnd_6400328 3286444610429739920965433 := by
  unfold tailWord_6400328
  simp only [CollatzResearch.WordTrace]
  refine ⟨116719569978356109921124819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155626093304474813228166425 116719569978356109921124819)
  ·
    refine ⟨175079354967534164881687229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116719569978356109921124819 175079354967534164881687229)
    ·
      refine ⟨65654758112825311830632711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175079354967534164881687229 65654758112825311830632711)
      ·
        refine ⟨98482137169237967745949067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65654758112825311830632711 98482137169237967745949067)
        ·
          refine ⟨147723205753856951618923601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98482137169237967745949067 147723205753856951618923601)
          ·
            refine ⟨110792404315392713714192701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147723205753856951618923601 110792404315392713714192701)
            ·
              refine ⟨41547151618272267642822263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110792404315392713714192701 41547151618272267642822263)
              ·
                refine ⟨62320727427408401464233395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41547151618272267642822263 62320727427408401464233395)
                ·
                  refine ⟨93481091141112602196350093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62320727427408401464233395 93481091141112602196350093)
                  ·
                    refine ⟨35055409177917225823631285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93481091141112602196350093 35055409177917225823631285)
                    ·
                      refine ⟨3286444610429739920965433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35055409177917225823631285 3286444610429739920965433)
                      ·
                        rfl

theorem cell23_6400328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_6400328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400328 prefixEnd_6400328 := by exact prefixLift 6400328
  have htrace : WordTrace (prefixWord ++ tailWord_6400328) baseStart_6400328 baseEnd_6400328 := by
    simpa [prefixWord, tailWord_6400328, baseEnd_6400328] using wordTrace_append hprefix tailTrace_6400328
  have hstable : (prefixWord ++ tailWord_6400328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400328).length < 2 ^ (prefixWord ++ tailWord_6400328).sum := by decide
  have hdescent : baseEnd_6400328 < baseStart_6400328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400395 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 2, 5]
def baseStart_6400395 : Nat := 118140960795 + 6400395 * 2 ^ 59
def prefixEnd_6400395 : Nat := 4983230072969 + 3 ^ 40 * 6400395 * 2
def baseEnd_6400395 : Nat := 1095493004544530386275875

theorem tailTrace_6400395 : CollatzResearch.WordTrace tailWord_6400395 prefixEnd_6400395 1095493004544530386275875 := by
  unfold tailWord_6400395
  simp only [CollatzResearch.WordTrace]
  refine ⟨233441583647469490284938639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155627722431646326856625759 233441583647469490284938639)
  ·
    refine ⟨350162375471204235427407959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233441583647469490284938639 350162375471204235427407959)
    ·
      refine ⟨525243563206806353141111939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350162375471204235427407959 525243563206806353141111939)
      ·
        refine ⟨787865344810209529711667909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525243563206806353141111939 787865344810209529711667909)
        ·
          refine ⟨147724752151914286820937733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 787865344810209529711667909 147724752151914286820937733)
          ·
            refine ⟨27698391028483928778925825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147724752151914286820937733 27698391028483928778925825)
            ·
              refine ⟨20773793271362946584194369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27698391028483928778925825 20773793271362946584194369)
              ·
                refine ⟨15580344953522209938145777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20773793271362946584194369 15580344953522209938145777)
                ·
                  refine ⟨11685258715141657453609333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15580344953522209938145777 11685258715141657453609333)
                  ·
                    refine ⟨1095493004544530386275875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11685258715141657453609333 1095493004544530386275875)
                    ·
                      rfl

theorem cell23_6400395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 5].length) (baseStart_6400395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400395 prefixEnd_6400395 := by exact prefixLift 6400395
  have htrace : WordTrace (prefixWord ++ tailWord_6400395) baseStart_6400395 baseEnd_6400395 := by
    simpa [prefixWord, tailWord_6400395, baseEnd_6400395] using wordTrace_append hprefix tailTrace_6400395
  have hstable : (prefixWord ++ tailWord_6400395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400395).length < 2 ^ (prefixWord ++ tailWord_6400395).sum := by decide
  have hdescent : baseEnd_6400395 < baseStart_6400395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400415 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6400415 : Nat := 118140960795 + 6400415 * 2 ^ 59
def prefixEnd_6400415 : Nat := 4983230072969 + 3 ^ 40 * 6400415 * 2
def baseEnd_6400415 : Nat := 3286489283246681080577533

theorem tailTrace_6400415 : CollatzResearch.WordTrace tailWord_6400415 prefixEnd_6400415 3286489283246681080577533 := by
  unfold tailWord_6400415
  simp only [CollatzResearch.WordTrace]
  refine ⟨233442313107397033700666699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155628208738264689133777799 233442313107397033700666699)
  ·
    refine ⟨350163469661095550551000049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233442313107397033700666699 350163469661095550551000049)
    ·
      refine ⟨262622602245821662913250037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350163469661095550551000049 262622602245821662913250037)
      ·
        refine ⟨24620868960545780898117191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262622602245821662913250037 24620868960545780898117191)
        ·
          refine ⟨36931303440818671347175787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24620868960545780898117191 36931303440818671347175787)
          ·
            refine ⟨55396955161228007020763681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36931303440818671347175787 55396955161228007020763681)
            ·
              refine ⟨41547716370921005265572761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55396955161228007020763681 41547716370921005265572761)
              ·
                refine ⟨31160787278190753949179571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41547716370921005265572761 31160787278190753949179571)
                ·
                  refine ⟨46741180917286130923769357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31160787278190753949179571 46741180917286130923769357)
                  ·
                    refine ⟨17527942843982299096413509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46741180917286130923769357 17527942843982299096413509)
                    ·
                      refine ⟨3286489283246681080577533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17527942843982299096413509 3286489283246681080577533)
                      ·
                        rfl

theorem cell23_6400415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6400415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400415 prefixEnd_6400415 := by exact prefixLift 6400415
  have htrace : WordTrace (prefixWord ++ tailWord_6400415) baseStart_6400415 baseEnd_6400415 := by
    simpa [prefixWord, tailWord_6400415, baseEnd_6400415] using wordTrace_append hprefix tailTrace_6400415
  have hstable : (prefixWord ++ tailWord_6400415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400415).length < 2 ^ (prefixWord ++ tailWord_6400415).sum := by decide
  have hdescent : baseEnd_6400415 < baseStart_6400415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400445 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_6400445 : Nat := 118140960795 + 6400445 * 2 ^ 59
def prefixEnd_6400445 : Nat := 4983230072969 + 3 ^ 40 * 6400445 * 2
def baseEnd_6400445 : Nat := 3286504687666315963202395

theorem tailTrace_6400445 : CollatzResearch.WordTrace tailWord_6400445 prefixEnd_6400445 3286504687666315963202395 := by
  unfold tailWord_6400445
  simp only [CollatzResearch.WordTrace]
  refine ⟨233443407297288348824258789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155628938198192232549505859 233443407297288348824258789)
  ·
    refine ⟨43770638868241565404548523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233443407297288348824258789 43770638868241565404548523)
    ·
      refine ⟨65655958302362348106822785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43770638868241565404548523 65655958302362348106822785)
      ·
        refine ⟨49241968726771761080117089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65655958302362348106822785 49241968726771761080117089)
        ·
          refine ⟨36931476545078820810087817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49241968726771761080117089 36931476545078820810087817)
          ·
            refine ⟨27698607408809115607565863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36931476545078820810087817 27698607408809115607565863)
            ·
              refine ⟨41547911113213673411348795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27698607408809115607565863 41547911113213673411348795)
              ·
                refine ⟨62321866669820510117023193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41547911113213673411348795 62321866669820510117023193)
                ·
                  refine ⟨46741400002365382587767395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62321866669820510117023193 46741400002365382587767395)
                  ·
                    refine ⟨70112100003548073881651093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46741400002365382587767395 70112100003548073881651093)
                    ·
                      refine ⟨3286504687666315963202395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70112100003548073881651093 3286504687666315963202395)
                      ·
                        rfl

theorem cell23_6400445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_6400445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400445 prefixEnd_6400445 := by exact prefixLift 6400445
  have htrace : WordTrace (prefixWord ++ tailWord_6400445) baseStart_6400445 baseEnd_6400445 := by
    simpa [prefixWord, tailWord_6400445, baseEnd_6400445] using wordTrace_append hprefix tailTrace_6400445
  have hstable : (prefixWord ++ tailWord_6400445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400445).length < 2 ^ (prefixWord ++ tailWord_6400445).sum := by decide
  have hdescent : baseEnd_6400445 < baseStart_6400445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400455 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 8]
def baseStart_6400455 : Nat := 118140960795 + 6400455 * 2 ^ 59
def prefixEnd_6400455 : Nat := 4983230072969 + 3 ^ 40 * 6400455 * 2
def baseEnd_6400455 : Nat := 365167758052540102675261

theorem tailTrace_6400455 : CollatzResearch.WordTrace tailWord_6400455 prefixEnd_6400455 365167758052540102675261 := by
  unfold tailWord_6400455
  simp only [CollatzResearch.WordTrace]
  refine ⟨233443772027252120532122819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155629181351501413688081879 233443772027252120532122819)
  ·
    refine ⟨350165658040878180798184229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233443772027252120532122819 350165658040878180798184229)
    ·
      refine ⟨65656060882664658899659543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350165658040878180798184229 65656060882664658899659543)
      ·
        refine ⟨98484091323996988349489315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65656060882664658899659543 98484091323996988349489315)
        ·
          refine ⟨147726136985995482524233973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98484091323996988349489315 147726136985995482524233973)
          ·
            refine ⟨13849325342437076486646935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147726136985995482524233973 13849325342437076486646935)
            ·
              refine ⟨20773988013655614729970403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849325342437076486646935 20773988013655614729970403)
              ·
                refine ⟨31160982020483422094955605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20773988013655614729970403 31160982020483422094955605)
                ·
                  refine ⟨365167758052540102675261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31160982020483422094955605 365167758052540102675261)
                  ·
                    rfl

theorem cell23_6400455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 8].length) (baseStart_6400455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400455 prefixEnd_6400455 := by exact prefixLift 6400455
  have htrace : WordTrace (prefixWord ++ tailWord_6400455) baseStart_6400455 baseEnd_6400455 := by
    simpa [prefixWord, tailWord_6400455, baseEnd_6400455] using wordTrace_append hprefix tailTrace_6400455
  have hstable : (prefixWord ++ tailWord_6400455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400455).length < 2 ^ (prefixWord ++ tailWord_6400455).sum := by decide
  have hdescent : baseEnd_6400455 < baseStart_6400455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400492 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 1, 5, 2]
def baseStart_6400492 : Nat := 118140960795 + 6400492 * 2 ^ 59
def prefixEnd_6400492 : Nat := 4983230072969 + 3 ^ 40 * 6400492 * 2
def baseEnd_6400492 : Nat := 3286528821257077279314679

theorem tailTrace_6400492 : CollatzResearch.WordTrace tailWord_6400492 prefixEnd_6400492 3286528821257077279314679 := by
  unfold tailWord_6400492
  simp only [CollatzResearch.WordTrace]
  refine ⟨116722560764059037925609865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155630081018745383900813153 116722560764059037925609865)
  ·
    refine ⟨87541920573044278444207399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116722560764059037925609865 87541920573044278444207399)
    ·
      refine ⟨131312880859566417666311099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87541920573044278444207399 131312880859566417666311099)
      ·
        refine ⟨196969321289349626499466649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131312880859566417666311099 196969321289349626499466649)
        ·
          refine ⟨147726990967012219874599987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196969321289349626499466649 147726990967012219874599987)
          ·
            refine ⟨221590486450518329811899981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147726990967012219874599987 221590486450518329811899981)
            ·
              refine ⟨83096432418944373679462493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221590486450518329811899981 83096432418944373679462493)
              ·
                refine ⟨31161162157104140129798435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83096432418944373679462493 31161162157104140129798435)
                ·
                  refine ⟨46741743235656210194697653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31161162157104140129798435 46741743235656210194697653)
                  ·
                    refine ⟨4382038428342769705752905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46741743235656210194697653 4382038428342769705752905)
                    ·
                      refine ⟨3286528821257077279314679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382038428342769705752905 3286528821257077279314679)
                      ·
                        rfl

theorem cell23_6400492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_6400492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400492 prefixEnd_6400492 := by exact prefixLift 6400492
  have htrace : WordTrace (prefixWord ++ tailWord_6400492) baseStart_6400492 baseEnd_6400492 := by
    simpa [prefixWord, tailWord_6400492, baseEnd_6400492] using wordTrace_append hprefix tailTrace_6400492
  have hstable : (prefixWord ++ tailWord_6400492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400492).length < 2 ^ (prefixWord ++ tailWord_6400492).sum := by decide
  have hdescent : baseEnd_6400492 < baseStart_6400492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400493 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_6400493 : Nat := 118140960795 + 6400493 * 2 ^ 59
def prefixEnd_6400493 : Nat := 4983230072969 + 3 ^ 40 * 6400493 * 2
def baseEnd_6400493 : Nat := 1095509778245910591800725

theorem tailTrace_6400493 : CollatzResearch.WordTrace tailWord_6400493 prefixEnd_6400493 1095509778245910591800725 := by
  unfold tailWord_6400493
  simp only [CollatzResearch.WordTrace]
  refine ⟨233445158001114453022006133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155630105334076302014670755 233445158001114453022006133)
  ·
    refine ⟨21885483562604479970813075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233445158001114453022006133 21885483562604479970813075)
    ·
      refine ⟨32828225343906719956219613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885483562604479970813075 32828225343906719956219613)
      ·
        refine ⟨12310584503965019983582355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32828225343906719956219613 12310584503965019983582355)
        ·
          refine ⟨18465876755947529975373533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310584503965019983582355 18465876755947529975373533)
          ·
            refine ⟨6924703783480323740765075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18465876755947529975373533 6924703783480323740765075)
            ·
              refine ⟨10387055675220485611147613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924703783480323740765075 10387055675220485611147613)
              ·
                refine ⟨3895145878207682104180355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10387055675220485611147613 3895145878207682104180355)
                ·
                  refine ⟨5842718817311523156270533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895145878207682104180355 5842718817311523156270533)
                  ·
                    refine ⟨1095509778245910591800725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842718817311523156270533 1095509778245910591800725)
                    ·
                      rfl

theorem cell23_6400493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_6400493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400493 prefixEnd_6400493 := by exact prefixLift 6400493
  have htrace : WordTrace (prefixWord ++ tailWord_6400493) baseStart_6400493 baseEnd_6400493 := by
    simpa [prefixWord, tailWord_6400493, baseEnd_6400493] using wordTrace_append hprefix tailTrace_6400493
  have hstable : (prefixWord ++ tailWord_6400493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400493).length < 2 ^ (prefixWord ++ tailWord_6400493).sum := by decide
  have hdescent : baseEnd_6400493 < baseStart_6400493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400509 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_6400509 : Nat := 118140960795 + 6400509 * 2 ^ 59
def prefixEnd_6400509 : Nat := 4983230072969 + 3 ^ 40 * 6400509 * 2
def baseEnd_6400509 : Nat := 3286537550428203712802101

theorem tailTrace_6400509 : CollatzResearch.WordTrace tailWord_6400509 prefixEnd_6400509 3286537550428203712802101 := by
  unfold tailWord_6400509
  simp only [CollatzResearch.WordTrace]
  refine ⟨233445741569056487754588581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155630494379370991836392387 233445741569056487754588581)
  ·
    refine ⟨43771076544198091453985359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233445741569056487754588581 43771076544198091453985359)
    ·
      refine ⟨65656614816297137180978039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43771076544198091453985359 65656614816297137180978039)
      ·
        refine ⟨98484922224445705771467059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65656614816297137180978039 98484922224445705771467059)
        ·
          refine ⟨147727383336668558657200589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98484922224445705771467059 147727383336668558657200589)
          ·
            refine ⟨55397768751250709496450221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147727383336668558657200589 55397768751250709496450221)
            ·
              refine ⟨20774163281719016061168833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55397768751250709496450221 20774163281719016061168833)
              ·
                refine ⟨15580622461289262045876625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20774163281719016061168833 15580622461289262045876625)
                ·
                  refine ⟨11685466845966946534407469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15580622461289262045876625 11685466845966946534407469)
                  ·
                    refine ⟨4382050067237604950402801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11685466845966946534407469 4382050067237604950402801)
                    ·
                      refine ⟨3286537550428203712802101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382050067237604950402801 3286537550428203712802101)
                      ·
                        rfl

theorem cell23_6400509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_6400509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400509 prefixEnd_6400509 := by exact prefixLift 6400509
  have htrace : WordTrace (prefixWord ++ tailWord_6400509) baseStart_6400509 baseEnd_6400509 := by
    simpa [prefixWord, tailWord_6400509, baseEnd_6400509] using wordTrace_append hprefix tailTrace_6400509
  have hstable : (prefixWord ++ tailWord_6400509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400509).length < 2 ^ (prefixWord ++ tailWord_6400509).sum := by decide
  have hdescent : baseEnd_6400509 < baseStart_6400509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400516 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6400516 : Nat := 118140960795 + 6400516 * 2 ^ 59
def prefixEnd_6400516 : Nat := 4983230072969 + 3 ^ 40 * 6400516 * 2
def baseEnd_6400516 : Nat := 3286541144792785185414569

theorem tailTrace_6400516 : CollatzResearch.WordTrace tailWord_6400516 prefixEnd_6400516 3286541144792785185414569 := by
  unfold tailWord_6400516
  simp only [CollatzResearch.WordTrace]
  refine ⟨116722998440015563975046701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155630664586687418633395601 116722998440015563975046701)
  ·
    refine ⟨43771124415005836490642513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116722998440015563975046701 43771124415005836490642513)
    ·
      refine ⟨32828343311254377367981885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43771124415005836490642513 32828343311254377367981885)
      ·
        refine ⟨12310628741720391512993207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32828343311254377367981885 12310628741720391512993207)
        ·
          refine ⟨18465943112580587269489811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310628741720391512993207 18465943112580587269489811)
          ·
            refine ⟨27698914668870880904234717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18465943112580587269489811 27698914668870880904234717)
            ·
              refine ⟨10387093000826580339088019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27698914668870880904234717 10387093000826580339088019)
              ·
                refine ⟨15580639501239870508632029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387093000826580339088019 15580639501239870508632029)
                ·
                  refine ⟨5842739812964951440737011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15580639501239870508632029 5842739812964951440737011)
                  ·
                    refine ⟨8764109719447427161105517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5842739812964951440737011 8764109719447427161105517)
                    ·
                      refine ⟨3286541144792785185414569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8764109719447427161105517 3286541144792785185414569)
                      ·
                        rfl

theorem cell23_6400516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6400516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400516 prefixEnd_6400516 := by exact prefixLift 6400516
  have htrace : WordTrace (prefixWord ++ tailWord_6400516) baseStart_6400516 baseEnd_6400516 := by
    simpa [prefixWord, tailWord_6400516, baseEnd_6400516] using wordTrace_append hprefix tailTrace_6400516
  have hstable : (prefixWord ++ tailWord_6400516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400516).length < 2 ^ (prefixWord ++ tailWord_6400516).sum := by decide
  have hdescent : baseEnd_6400516 < baseStart_6400516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400522 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_6400522 : Nat := 118140960795 + 6400522 * 2 ^ 59
def prefixEnd_6400522 : Nat := 4983230072969 + 3 ^ 40 * 6400522 * 2
def baseEnd_6400522 : Nat := 3286544225676712161939541

theorem tailTrace_6400522 : CollatzResearch.WordTrace tailWord_6400522 prefixEnd_6400522 3286544225676712161939541 := by
  unfold tailWord_6400522
  simp only [CollatzResearch.WordTrace]
  refine ⟨58361553929502347743702955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155630810478672927316541213 58361553929502347743702955)
  ·
    refine ⟨87542330894253521615554433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58361553929502347743702955 87542330894253521615554433)
    ·
      refine ⟨65656748170690141211665825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87542330894253521615554433 65656748170690141211665825)
      ·
        refine ⟨49242561128017605908749369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65656748170690141211665825 49242561128017605908749369)
        ·
          refine ⟨36931920846013204431562027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49242561128017605908749369 36931920846013204431562027)
          ·
            refine ⟨55397881269019806647343041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36931920846013204431562027 55397881269019806647343041)
            ·
              refine ⟨41548410951764854985507281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55397881269019806647343041 41548410951764854985507281)
              ·
                refine ⟨31161308213823641239130461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41548410951764854985507281 31161308213823641239130461)
                ·
                  refine ⟨11685490580183865464673923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31161308213823641239130461 11685490580183865464673923)
                  ·
                    refine ⟨17528235870275798197010885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11685490580183865464673923 17528235870275798197010885)
                    ·
                      refine ⟨3286544225676712161939541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17528235870275798197010885 3286544225676712161939541)
                      ·
                        rfl

theorem cell23_6400522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_6400522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400522 prefixEnd_6400522 := by exact prefixLift 6400522
  have htrace : WordTrace (prefixWord ++ tailWord_6400522) baseStart_6400522 baseEnd_6400522 := by
    simpa [prefixWord, tailWord_6400522, baseEnd_6400522] using wordTrace_append hprefix tailTrace_6400522
  have hstable : (prefixWord ++ tailWord_6400522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400522).length < 2 ^ (prefixWord ++ tailWord_6400522).sum := by decide
  have hdescent : baseEnd_6400522 < baseStart_6400522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400545 : List Nat := [1, 2, 3, 2, 2, 1, 1, 11]
def baseStart_6400545 : Nat := 118140960795 + 6400545 * 2 ^ 59
def prefixEnd_6400545 : Nat := 4983230072969 + 3 ^ 40 * 6400545 * 2
def baseEnd_6400545 : Nat := 121724297619695021183405

theorem tailTrace_6400545 : CollatzResearch.WordTrace tailWord_6400545 prefixEnd_6400545 121724297619695021183405 := by
  unfold tailWord_6400545
  simp only [CollatzResearch.WordTrace]
  refine ⟨233447054596926065902899089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155631369731284043935266059 233447054596926065902899089)
  ·
    refine ⟨175085290947694549427174317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233447054596926065902899089 175085290947694549427174317)
    ·
      refine ⟨65656984105385456035190369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175085290947694549427174317 65656984105385456035190369)
      ·
        refine ⟨49242738079039092026392777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65656984105385456035190369 49242738079039092026392777)
        ·
          refine ⟨36932053559279319019794583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49242738079039092026392777 36932053559279319019794583)
          ·
            refine ⟨55398080338918978529691875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36932053559279319019794583 55398080338918978529691875)
            ·
              refine ⟨83097120508378467794537813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55398080338918978529691875 83097120508378467794537813)
              ·
                refine ⟨121724297619695021183405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 83097120508378467794537813 121724297619695021183405)
                ·
                  rfl

theorem cell23_6400545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 11].length) (baseStart_6400545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400545 prefixEnd_6400545 := by exact prefixLift 6400545
  have htrace : WordTrace (prefixWord ++ tailWord_6400545) baseStart_6400545 baseEnd_6400545 := by
    simpa [prefixWord, tailWord_6400545, baseEnd_6400545] using wordTrace_append hprefix tailTrace_6400545
  have hstable : (prefixWord ++ tailWord_6400545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400545).length < 2 ^ (prefixWord ++ tailWord_6400545).sum := by decide
  have hdescent : baseEnd_6400545 < baseStart_6400545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400566 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6400566 : Nat := 118140960795 + 6400566 * 2 ^ 59
def prefixEnd_6400566 : Nat := 4983230072969 + 3 ^ 40 * 6400566 * 2
def baseEnd_6400566 : Nat := 1095522272941836663263113

theorem tailTrace_6400566 : CollatzResearch.WordTrace tailWord_6400566 prefixEnd_6400566 1095522272941836663263113 := by
  unfold tailWord_6400566
  simp only [CollatzResearch.WordTrace]
  refine ⟨14590488783115624155588347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155631880353233324326275701 14590488783115624155588347)
  ·
    refine ⟨21885733174673436233382521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14590488783115624155588347 21885733174673436233382521)
    ·
      refine ⟨16414299881005077175036891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21885733174673436233382521 16414299881005077175036891)
      ·
        refine ⟨24621449821507615762555337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16414299881005077175036891 24621449821507615762555337)
        ·
          refine ⟨18466087366130711821916503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24621449821507615762555337 18466087366130711821916503)
          ·
            refine ⟨27699131049196067732874755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18466087366130711821916503 27699131049196067732874755)
            ·
              refine ⟨41548696573794101599312133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27699131049196067732874755 41548696573794101599312133)
              ·
                refine ⟨7790380607586394049871025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41548696573794101599312133 7790380607586394049871025)
                ·
                  refine ⟨5842785455689795537403269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7790380607586394049871025 5842785455689795537403269)
                  ·
                    refine ⟨1095522272941836663263113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842785455689795537403269 1095522272941836663263113)
                    ·
                      rfl

theorem cell23_6400566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6400566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400566 prefixEnd_6400566 := by exact prefixLift 6400566
  have htrace : WordTrace (prefixWord ++ tailWord_6400566) baseStart_6400566 baseEnd_6400566 := by
    simpa [prefixWord, tailWord_6400566, baseEnd_6400566] using wordTrace_append hprefix tailTrace_6400566
  have hstable : (prefixWord ++ tailWord_6400566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400566).length < 2 ^ (prefixWord ++ tailWord_6400566).sum := by decide
  have hdescent : baseEnd_6400566 < baseStart_6400566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400575 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 9]
def baseStart_6400575 : Nat := 118140960795 + 6400575 * 2 ^ 59
def prefixEnd_6400575 : Nat := 4983230072969 + 3 ^ 40 * 6400575 * 2
def baseEnd_6400575 : Nat := 1095523813383800151525599

theorem tailTrace_6400575 : CollatzResearch.WordTrace tailWord_6400575 prefixEnd_6400575 1095523813383800151525599 := by
  unfold tailWord_6400575
  simp only [CollatzResearch.WordTrace]
  refine ⟨233448148786817381026491179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155632099191211587350994119 233448148786817381026491179)
  ·
    refine ⟨350172223180226071539736769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233448148786817381026491179 350172223180226071539736769)
    ·
      refine ⟨262629167385169553654802577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350172223180226071539736769 262629167385169553654802577)
      ·
        refine ⟨196971875538877165241101933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262629167385169553654802577 196971875538877165241101933)
        ·
          refine ⟨73864453327078936965413225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196971875538877165241101933 73864453327078936965413225)
          ·
            refine ⟨55398339995309202724059919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73864453327078936965413225 55398339995309202724059919)
            ·
              refine ⟨83097509992963804086089879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55398339995309202724059919 83097509992963804086089879)
              ·
                refine ⟨124646264989445706129134819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83097509992963804086089879 124646264989445706129134819)
                ·
                  refine ⟨186969397484168559193702229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124646264989445706129134819 186969397484168559193702229)
                  ·
                    refine ⟨1095523813383800151525599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186969397484168559193702229 1095523813383800151525599)
                    ·
                      rfl

theorem cell23_6400575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_6400575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400575 prefixEnd_6400575 := by exact prefixLift 6400575
  have htrace : WordTrace (prefixWord ++ tailWord_6400575) baseStart_6400575 baseEnd_6400575 := by
    simpa [prefixWord, tailWord_6400575, baseEnd_6400575] using wordTrace_append hprefix tailTrace_6400575
  have hstable : (prefixWord ++ tailWord_6400575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400575).length < 2 ^ (prefixWord ++ tailWord_6400575).sum := by decide
  have hdescent : baseEnd_6400575 < baseStart_6400575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400585 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_6400585 : Nat := 118140960795 + 6400585 * 2 ^ 59
def prefixEnd_6400585 : Nat := 4983230072969 + 3 ^ 40 * 6400585 * 2
def baseEnd_6400585 : Nat := 3286576574957945415451751

theorem tailTrace_6400585 : CollatzResearch.WordTrace tailWord_6400585 prefixEnd_6400585 3286576574957945415451751 := by
  unfold tailWord_6400585
  simp only [CollatzResearch.WordTrace]
  refine ⟨233448513516781152734355209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155632342344520768489570139 233448513516781152734355209)
  ·
    refine ⟨175086385137585864550766407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233448513516781152734355209 175086385137585864550766407)
    ·
      refine ⟨262629577706378796826149611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175086385137585864550766407 262629577706378796826149611)
      ·
        refine ⟨393944366559568195239224417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262629577706378796826149611 393944366559568195239224417)
        ·
          refine ⟨295458274919676146429418313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393944366559568195239224417 295458274919676146429418313)
          ·
            refine ⟨221593706189757109822063735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295458274919676146429418313 221593706189757109822063735)
            ·
              refine ⟨332390559284635664733095603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221593706189757109822063735 332390559284635664733095603)
              ·
                refine ⟨498585838926953497099643405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332390559284635664733095603 498585838926953497099643405)
                ·
                  refine ⟨186969689597607561412366277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498585838926953497099643405 186969689597607561412366277)
                  ·
                    refine ⟨35056816799551417764818677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186969689597607561412366277 35056816799551417764818677)
                    ·
                      refine ⟨3286576574957945415451751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35056816799551417764818677 3286576574957945415451751)
                      ·
                        rfl

theorem cell23_6400585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_6400585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400585 prefixEnd_6400585 := by exact prefixLift 6400585
  have htrace : WordTrace (prefixWord ++ tailWord_6400585) baseStart_6400585 baseEnd_6400585 := by
    simpa [prefixWord, tailWord_6400585, baseEnd_6400585] using wordTrace_append hprefix tailTrace_6400585
  have hstable : (prefixWord ++ tailWord_6400585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400585).length < 2 ^ (prefixWord ++ tailWord_6400585).sum := by decide
  have hdescent : baseEnd_6400585 < baseStart_6400585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400599 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 3, 3, 2]
def baseStart_6400599 : Nat := 118140960795 + 6400599 * 2 ^ 59
def prefixEnd_6400599 : Nat := 4983230072969 + 3 ^ 40 * 6400599 * 2
def baseEnd_6400599 : Nat := 3286583763687108360676687

theorem tailTrace_6400599 : CollatzResearch.WordTrace tailWord_6400599 prefixEnd_6400599 3286583763687108360676687 := by
  unfold tailWord_6400599
  simp only [CollatzResearch.WordTrace]
  refine ⟨233449024138730433125364851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155632682759153622083576567 233449024138730433125364851)
  ·
    refine ⟨350173536208095649688047277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233449024138730433125364851 350173536208095649688047277)
    ·
      refine ⟨131315076078035868633017729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350173536208095649688047277 131315076078035868633017729)
      ·
        refine ⟨98486307058526901474763297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131315076078035868633017729 98486307058526901474763297)
        ·
          refine ⟨73864730293895176106072473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98486307058526901474763297 73864730293895176106072473)
          ·
            refine ⟨55398547720421382079554355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73864730293895176106072473 55398547720421382079554355)
            ·
              refine ⟨83097821580632073119331533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55398547720421382079554355 83097821580632073119331533)
              ·
                refine ⟨31161683092737027419749325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83097821580632073119331533 31161683092737027419749325)
                ·
                  refine ⟨11685631159776385282405997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31161683092737027419749325 11685631159776385282405997)
                  ·
                    refine ⟨4382111684916144480902249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11685631159776385282405997 4382111684916144480902249)
                    ·
                      refine ⟨3286583763687108360676687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382111684916144480902249 3286583763687108360676687)
                      ·
                        rfl

theorem cell23_6400599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_6400599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400599 prefixEnd_6400599 := by exact prefixLift 6400599
  have htrace : WordTrace (prefixWord ++ tailWord_6400599) baseStart_6400599 baseEnd_6400599 := by
    simpa [prefixWord, tailWord_6400599, baseEnd_6400599] using wordTrace_append hprefix tailTrace_6400599
  have hstable : (prefixWord ++ tailWord_6400599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400599).length < 2 ^ (prefixWord ++ tailWord_6400599).sum := by decide
  have hdescent : baseEnd_6400599 < baseStart_6400599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400666 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6400666 : Nat := 118140960795 + 6400666 * 2 ^ 59
def prefixEnd_6400666 : Nat := 4983230072969 + 3 ^ 40 * 6400666 * 2
def baseEnd_6400666 : Nat := 3286618166890959598538879

theorem tailTrace_6400666 : CollatzResearch.WordTrace tailWord_6400666 prefixEnd_6400666 3286618166890959598538879 := by
  unfold tailWord_6400666
  simp only [CollatzResearch.WordTrace]
  refine ⟨58362866957371925892013463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155634311886325135712035901 58362866957371925892013463)
  ·
    refine ⟨87544300436057888838020195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58362866957371925892013463 87544300436057888838020195)
    ·
      refine ⟨131316450654086833257030293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87544300436057888838020195 131316450654086833257030293)
      ·
        refine ⟨6155458624410320308923295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131316450654086833257030293 6155458624410320308923295)
        ·
          refine ⟨9233187936615480463384943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6155458624410320308923295 9233187936615480463384943)
          ·
            refine ⟨13849781904923220695077415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9233187936615480463384943 13849781904923220695077415)
            ·
              refine ⟨20774672857384831042616123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849781904923220695077415 20774672857384831042616123)
              ·
                refine ⟨31162009286077246563924185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20774672857384831042616123 31162009286077246563924185)
                ·
                  refine ⟨23371506964557934922943139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31162009286077246563924185 23371506964557934922943139)
                  ·
                    refine ⟨35057260446836902384414709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23371506964557934922943139 35057260446836902384414709)
                    ·
                      refine ⟨3286618166890959598538879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35057260446836902384414709 3286618166890959598538879)
                      ·
                        rfl

theorem cell23_6400666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6400666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400666 prefixEnd_6400666 := by exact prefixLift 6400666
  have htrace : WordTrace (prefixWord ++ tailWord_6400666) baseStart_6400666 baseEnd_6400666 := by
    simpa [prefixWord, tailWord_6400666, baseEnd_6400666] using wordTrace_append hprefix tailTrace_6400666
  have hstable : (prefixWord ++ tailWord_6400666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400666).length < 2 ^ (prefixWord ++ tailWord_6400666).sum := by decide
  have hdescent : baseEnd_6400666 < baseStart_6400666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400686 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_6400686 : Nat := 118140960795 + 6400686 * 2 ^ 59
def prefixEnd_6400686 : Nat := 4983230072969 + 3 ^ 40 * 6400686 * 2
def baseEnd_6400686 : Nat := 365180937389338835587643

theorem tailTrace_6400686 : CollatzResearch.WordTrace tailWord_6400686 prefixEnd_6400686 365180937389338835587643 := by
  unfold tailWord_6400686
  simp only [CollatzResearch.WordTrace]
  refine ⟨29181524661176905872972739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155634798192943497989187941 29181524661176905872972739)
  ·
    refine ⟨43772286991765358809459109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29181524661176905872972739 43772286991765358809459109)
    ·
      refine ⟨8207303810956004776773583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43772286991765358809459109 8207303810956004776773583)
      ·
        refine ⟨12310955716434007165160375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8207303810956004776773583 12310955716434007165160375)
        ·
          refine ⟨18466433574651010747740563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310955716434007165160375 18466433574651010747740563)
          ·
            refine ⟨27699650361976516121610845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18466433574651010747740563 27699650361976516121610845)
            ·
              refine ⟨10387368885741193545604067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27699650361976516121610845 10387368885741193545604067)
              ·
                refine ⟨15581053328611790318406101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387368885741193545604067 15581053328611790318406101)
                ·
                  refine ⟨365180937389338835587643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15581053328611790318406101 365180937389338835587643)
                  ·
                    rfl

theorem cell23_6400686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_6400686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400686 prefixEnd_6400686 := by exact prefixLift 6400686
  have htrace : WordTrace (prefixWord ++ tailWord_6400686) baseStart_6400686 baseEnd_6400686 := by
    simpa [prefixWord, tailWord_6400686, baseEnd_6400686] using wordTrace_append hprefix tailTrace_6400686
  have hstable : (prefixWord ++ tailWord_6400686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400686).length < 2 ^ (prefixWord ++ tailWord_6400686).sum := by decide
  have hdescent : baseEnd_6400686 < baseStart_6400686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400716 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_6400716 : Nat := 118140960795 + 6400716 * 2 ^ 59
def prefixEnd_6400716 : Nat := 4983230072969 + 3 ^ 40 * 6400716 * 2
def baseEnd_6400716 : Nat := 1095547946974561467637883

theorem tailTrace_6400716 : CollatzResearch.WordTrace tailWord_6400716 prefixEnd_6400716 1095547946974561467637883 := by
  unfold tailWord_6400716
  simp only [CollatzResearch.WordTrace]
  refine ⟨116726645739653281053687001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155635527652871041404916001 116726645739653281053687001)
  ·
    refine ⟨87544984304739960790265251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116726645739653281053687001 87544984304739960790265251)
    ·
      refine ⟨131317476457109941185397877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87544984304739960790265251 131317476457109941185397877)
      ·
        refine ⟨12311013417854056986131051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131317476457109941185397877 12311013417854056986131051)
        ·
          refine ⟨18466520126781085479196577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311013417854056986131051 18466520126781085479196577)
          ·
            refine ⟨13849890095085814109397433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18466520126781085479196577 13849890095085814109397433)
            ·
              refine ⟨10387417571314360582048075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13849890095085814109397433 10387417571314360582048075)
              ·
                refine ⟨15581126356971540873072113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387417571314360582048075 15581126356971540873072113)
                ·
                  refine ⟨11685844767728655654804085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15581126356971540873072113 11685844767728655654804085)
                  ·
                    refine ⟨1095547946974561467637883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11685844767728655654804085 1095547946974561467637883)
                    ·
                      rfl

theorem cell23_6400716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_6400716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400716 prefixEnd_6400716 := by exact prefixLift 6400716
  have htrace : WordTrace (prefixWord ++ tailWord_6400716) baseStart_6400716 baseEnd_6400716 := by
    simpa [prefixWord, tailWord_6400716, baseEnd_6400716] using wordTrace_append hprefix tailTrace_6400716
  have hstable : (prefixWord ++ tailWord_6400716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400716).length < 2 ^ (prefixWord ++ tailWord_6400716).sum := by decide
  have hdescent : baseEnd_6400716 < baseStart_6400716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400719 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 6, 4, 2]
def baseStart_6400719 : Nat := 118140960795 + 6400719 * 2 ^ 59
def prefixEnd_6400719 : Nat := 4983230072969 + 3 ^ 40 * 6400719 * 2
def baseEnd_6400719 : Nat := 3286645381365647891176135

theorem tailTrace_6400719 : CollatzResearch.WordTrace tailWord_6400719 prefixEnd_6400719 3286645381365647891176135 := by
  unfold tailWord_6400719
  simp only [CollatzResearch.WordTrace]
  refine ⟨233453400898295693619733211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155635600598863795746488807 233453400898295693619733211)
  ·
    refine ⟨350180101347443540429599817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233453400898295693619733211 350180101347443540429599817)
    ·
      refine ⟨262635076010582655322199863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350180101347443540429599817 262635076010582655322199863)
      ·
        refine ⟨393952614015873982983299795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262635076010582655322199863 393952614015873982983299795)
        ·
          refine ⟨590928921023810974474949693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393952614015873982983299795 590928921023810974474949693)
          ·
            refine ⟨221598345383929115428106135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 590928921023810974474949693 221598345383929115428106135)
            ·
              refine ⟨332397518075893673142159203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221598345383929115428106135 332397518075893673142159203)
              ·
                refine ⟨498596277113840509713238805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332397518075893673142159203 498596277113840509713238805)
                ·
                  refine ⟨23371700489711273892808069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 498596277113840509713238805 23371700489711273892808069)
                  ·
                    refine ⟨4382193841820863854901513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23371700489711273892808069 4382193841820863854901513)
                    ·
                      refine ⟨3286645381365647891176135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382193841820863854901513 3286645381365647891176135)
                      ·
                        rfl

theorem cell23_6400719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4, 2].length) (baseStart_6400719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400719 prefixEnd_6400719 := by exact prefixLift 6400719
  have htrace : WordTrace (prefixWord ++ tailWord_6400719) baseStart_6400719 baseEnd_6400719 := by
    simpa [prefixWord, tailWord_6400719, baseEnd_6400719] using wordTrace_append hprefix tailTrace_6400719
  have hstable : (prefixWord ++ tailWord_6400719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400719).length < 2 ^ (prefixWord ++ tailWord_6400719).sum := by decide
  have hdescent : baseEnd_6400719 < baseStart_6400719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400810 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_6400810 : Nat := 118140960795 + 6400810 * 2 ^ 59
def prefixEnd_6400810 : Nat := 4983230072969 + 3 ^ 40 * 6400810 * 2
def baseEnd_6400810 : Nat := 365188012011689670570913

theorem tailTrace_6400810 : CollatzResearch.WordTrace tailWord_6400810 prefixEnd_6400810 365188012011689670570913 := by
  unfold tailWord_6400810
  simp only [CollatzResearch.WordTrace]
  refine ⟨58364179985241504040323971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155637813293977344107530589 58364179985241504040323971)
  ·
    refine ⟨87546269977862256060485957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58364179985241504040323971 87546269977862256060485957)
    ·
      refine ⟨16414925620849173011341117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87546269977862256060485957 16414925620849173011341117)
      ·
        refine ⟨6155597107818439879252919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16414925620849173011341117 6155597107818439879252919)
        ·
          refine ⟨9233395661727659818879379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6155597107818439879252919 9233395661727659818879379)
          ·
            refine ⟨13850093492591489728319069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9233395661727659818879379 13850093492591489728319069)
            ·
              refine ⟨5193785059721808648119651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13850093492591489728319069 5193785059721808648119651)
              ·
                refine ⟨7790677589582712972179477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193785059721808648119651 7790677589582712972179477)
                ·
                  refine ⟨365188012011689670570913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7790677589582712972179477 365188012011689670570913)
                  ·
                    rfl

theorem cell23_6400810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_6400810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400810 prefixEnd_6400810 := by exact prefixLift 6400810
  have htrace : WordTrace (prefixWord ++ tailWord_6400810) baseStart_6400810 baseEnd_6400810 := by
    simpa [prefixWord, tailWord_6400810, baseEnd_6400810] using wordTrace_append hprefix tailTrace_6400810
  have hstable : (prefixWord ++ tailWord_6400810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400810).length < 2 ^ (prefixWord ++ tailWord_6400810).sum := by decide
  have hdescent : baseEnd_6400810 < baseStart_6400810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400839 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_6400839 : Nat := 118140960795 + 6400839 * 2 ^ 59
def prefixEnd_6400839 : Nat := 4983230072969 + 3 ^ 40 * 6400839 * 2
def baseEnd_6400839 : Nat := 3286706999044187421675583

theorem tailTrace_6400839 : CollatzResearch.WordTrace tailWord_6400839 prefixEnd_6400839 3286706999044187421675583 := by
  unfold tailWord_6400839
  simp only [CollatzResearch.WordTrace]
  refine ⟨233457777657860954114101571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155638518438573969409401047 233457777657860954114101571)
  ·
    refine ⟨350186666486791431171152357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233457777657860954114101571 350186666486791431171152357)
    ·
      refine ⟨65659999966273393344591067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350186666486791431171152357 65659999966273393344591067)
      ·
        refine ⟨98489999949410090016886601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65659999966273393344591067 98489999949410090016886601)
        ·
          refine ⟨73867499962057567512664951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98489999949410090016886601 73867499962057567512664951)
          ·
            refine ⟨110801249943086351268997427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73867499962057567512664951 110801249943086351268997427)
            ·
              refine ⟨166201874914629526903496141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110801249943086351268997427 166201874914629526903496141)
              ·
                refine ⟨62325703092986072588811053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166201874914629526903496141 62325703092986072588811053)
                ·
                  refine ⟨23372138659869777220804145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62325703092986072588811053 23372138659869777220804145)
                  ·
                    refine ⟨17529103994902332915603109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23372138659869777220804145 17529103994902332915603109)
                    ·
                      refine ⟨3286706999044187421675583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17529103994902332915603109 3286706999044187421675583)
                      ·
                        rfl

theorem cell23_6400839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_6400839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400839 prefixEnd_6400839 := by exact prefixLift 6400839
  have htrace : WordTrace (prefixWord ++ tailWord_6400839) baseStart_6400839 baseEnd_6400839 := by
    simpa [prefixWord, tailWord_6400839, baseEnd_6400839] using wordTrace_append hprefix tailTrace_6400839
  have hstable : (prefixWord ++ tailWord_6400839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400839).length < 2 ^ (prefixWord ++ tailWord_6400839).sum := by decide
  have hdescent : baseEnd_6400839 < baseStart_6400839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400876 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_6400876 : Nat := 118140960795 + 6400876 * 2 ^ 59
def prefixEnd_6400876 : Nat := 4983230072969 + 3 ^ 40 * 6400876 * 2
def baseEnd_6400876 : Nat := 3286725997828403776912913

theorem tailTrace_6400876 : CollatzResearch.WordTrace tailWord_6400876 prefixEnd_6400876 3286725997828403776912913 := by
  unfold tailWord_6400876
  simp only [CollatzResearch.WordTrace]
  refine ⟨116729563579363454716599241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155639418105817939622132321 116729563579363454716599241)
  ·
    refine ⟨87547172684522591037449431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116729563579363454716599241 87547172684522591037449431)
    ·
      refine ⟨131320759026783886556174147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87547172684522591037449431 131320759026783886556174147)
      ·
        refine ⟨196981138540175829834261221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131320759026783886556174147 196981138540175829834261221)
        ·
          refine ⟨36933963476282968093923979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196981138540175829834261221 36933963476282968093923979)
          ·
            refine ⟨55400945214424452140885969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36933963476282968093923979 55400945214424452140885969)
            ·
              refine ⟨41550708910818339105664477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55400945214424452140885969 41550708910818339105664477)
              ·
                refine ⟨15581515841556877164624179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41550708910818339105664477 15581515841556877164624179)
                ·
                  refine ⟨23372273762335315746936269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15581515841556877164624179 23372273762335315746936269)
                  ·
                    refine ⟨8764602660875743405101101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23372273762335315746936269 8764602660875743405101101)
                    ·
                      refine ⟨3286725997828403776912913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8764602660875743405101101 3286725997828403776912913)
                      ·
                        rfl

theorem cell23_6400876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_6400876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400876 prefixEnd_6400876 := by exact prefixLift 6400876
  have htrace : WordTrace (prefixWord ++ tailWord_6400876) baseStart_6400876 baseEnd_6400876 := by
    simpa [prefixWord, tailWord_6400876, baseEnd_6400876] using wordTrace_append hprefix tailTrace_6400876
  have hstable : (prefixWord ++ tailWord_6400876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400876).length < 2 ^ (prefixWord ++ tailWord_6400876).sum := by decide
  have hdescent : baseEnd_6400876 < baseStart_6400876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400916 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6400916 : Nat := 118140960795 + 6400916 * 2 ^ 59
def prefixEnd_6400916 : Nat := 4983230072969 + 3 ^ 40 * 6400916 * 2
def baseEnd_6400916 : Nat := 3286746537054583620412729

theorem tailTrace_6400916 : CollatzResearch.WordTrace tailWord_6400916 prefixEnd_6400916 3286746537054583620412729 := by
  unfold tailWord_6400916
  simp only [CollatzResearch.WordTrace]
  refine ⟨116730293039290998132327301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155640390719054664176436401 116730293039290998132327301)
  ·
    refine ⟨21886929944867062149811369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116730293039290998132327301 21886929944867062149811369)
    ·
      refine ⟨16415197458650296612358527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21886929944867062149811369 16415197458650296612358527)
      ·
        refine ⟨24622796187975444918537791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16415197458650296612358527 24622796187975444918537791)
        ·
          refine ⟨36934194281963167377806687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24622796187975444918537791 36934194281963167377806687)
          ·
            refine ⟨55401291422944751066710031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36934194281963167377806687 55401291422944751066710031)
            ·
              refine ⟨83101937134417126600065047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55401291422944751066710031 83101937134417126600065047)
              ·
                refine ⟨124652905701625689900097571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83101937134417126600065047 124652905701625689900097571)
                ·
                  refine ⟨186979358552438534850146357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124652905701625689900097571 186979358552438534850146357)
                  ·
                    refine ⟨17529314864291112642201221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186979358552438534850146357 17529314864291112642201221)
                    ·
                      refine ⟨3286746537054583620412729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17529314864291112642201221 3286746537054583620412729)
                      ·
                        rfl

theorem cell23_6400916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6400916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400916 prefixEnd_6400916 := by exact prefixLift 6400916
  have htrace : WordTrace (prefixWord ++ tailWord_6400916) baseStart_6400916 baseEnd_6400916 := by
    simpa [prefixWord, tailWord_6400916, baseEnd_6400916] using wordTrace_append hprefix tailTrace_6400916
  have hstable : (prefixWord ++ tailWord_6400916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400916).length < 2 ^ (prefixWord ++ tailWord_6400916).sum := by decide
  have hdescent : baseEnd_6400916 < baseStart_6400916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400933 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 8, 2, 2]
def baseStart_6400933 : Nat := 118140960795 + 6400933 * 2 ^ 59
def prefixEnd_6400933 : Nat := 4983230072969 + 3 ^ 40 * 6400933 * 2
def baseEnd_6400933 : Nat := 3286755266225710053900151

theorem tailTrace_6400933 : CollatzResearch.WordTrace tailWord_6400933 prefixEnd_6400933 3286755266225710053900151 := by
  unfold tailWord_6400933
  simp only [CollatzResearch.WordTrace]
  refine ⟨233461206119520408168023453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155640804079680272112015635 233461206119520408168023453)
  ·
    refine ⟨87547952294820153063008795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233461206119520408168023453 87547952294820153063008795)
    ·
      refine ⟨131321928442230229594513193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87547952294820153063008795 131321928442230229594513193)
      ·
        refine ⟨98491446331672672195884895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131321928442230229594513193 98491446331672672195884895)
        ·
          refine ⟨147737169497509008293827343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98491446331672672195884895 147737169497509008293827343)
          ·
            refine ⟨221605754246263512440741015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147737169497509008293827343 221605754246263512440741015)
            ·
              refine ⟨332408631369395268661111523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221605754246263512440741015 332408631369395268661111523)
              ·
                refine ⟨498612947054092902991667285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332408631369395268661111523 498612947054092902991667285)
                ·
                  refine ⟨5843120473290151206933601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 498612947054092902991667285 5843120473290151206933601)
                  ·
                    refine ⟨4382340354967613405200201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5843120473290151206933601 4382340354967613405200201)
                    ·
                      refine ⟨3286755266225710053900151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382340354967613405200201 3286755266225710053900151)
                      ·
                        rfl

theorem cell23_6400933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_6400933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400933 prefixEnd_6400933 := by exact prefixLift 6400933
  have htrace : WordTrace (prefixWord ++ tailWord_6400933) baseStart_6400933 baseEnd_6400933 := by
    simpa [prefixWord, tailWord_6400933, baseEnd_6400933] using wordTrace_append hprefix tailTrace_6400933
  have hstable : (prefixWord ++ tailWord_6400933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400933).length < 2 ^ (prefixWord ++ tailWord_6400933).sum := by decide
  have hdescent : baseEnd_6400933 < baseStart_6400933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400939 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 7]
def baseStart_6400939 : Nat := 118140960795 + 6400939 * 2 ^ 59
def prefixEnd_6400939 : Nat := 4983230072969 + 3 ^ 40 * 6400939 * 2
def baseEnd_6400939 : Nat := 365195371901070781158347

theorem tailTrace_6400939 : CollatzResearch.WordTrace tailWord_6400939 prefixEnd_6400939 365195371901070781158347 := by
  unfold tailWord_6400939
  simp only [CollatzResearch.WordTrace]
  refine ⟨233461424957498671192741871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155640949971665780795161247 233461424957498671192741871)
  ·
    refine ⟨350192137436248006789112807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233461424957498671192741871 350192137436248006789112807)
    ·
      refine ⟨525288206154372010183669211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350192137436248006789112807 525288206154372010183669211)
      ·
        refine ⟨787932309231558015275503817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525288206154372010183669211 787932309231558015275503817)
        ·
          refine ⟨590949231923668511456627863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787932309231558015275503817 590949231923668511456627863)
          ·
            refine ⟨886423847885502767184941795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590949231923668511456627863 886423847885502767184941795)
            ·
              refine ⟨1329635771828254150777412693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886423847885502767184941795 1329635771828254150777412693)
              ·
                refine ⟨15581669201112353329422805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1329635771828254150777412693 15581669201112353329422805)
                ·
                  refine ⟨365195371901070781158347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15581669201112353329422805 365195371901070781158347)
                  ·
                    rfl

theorem cell23_6400939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 7].length) (baseStart_6400939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400939 prefixEnd_6400939 := by exact prefixLift 6400939
  have htrace : WordTrace (prefixWord ++ tailWord_6400939) baseStart_6400939 baseEnd_6400939 := by
    simpa [prefixWord, tailWord_6400939, baseEnd_6400939] using wordTrace_append hprefix tailTrace_6400939
  have hstable : (prefixWord ++ tailWord_6400939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400939).length < 2 ^ (prefixWord ++ tailWord_6400939).sum := by decide
  have hdescent : baseEnd_6400939 < baseStart_6400939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400969 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_6400969 : Nat := 118140960795 + 6400969 * 2 ^ 59
def prefixEnd_6400969 : Nat := 4983230072969 + 3 ^ 40 * 6400969 * 2
def baseEnd_6400969 : Nat := 1095591250509757304349995

theorem tailTrace_6400969 : CollatzResearch.WordTrace tailWord_6400969 prefixEnd_6400969 1095591250509757304349995 := by
  unfold tailWord_6400969
  simp only [CollatzResearch.WordTrace]
  refine ⟨233462519147389986316333961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155641679431593324210889307 233462519147389986316333961)
  ·
    refine ⟨175096889360542489737250471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233462519147389986316333961 175096889360542489737250471)
    ·
      refine ⟨262645334040813734605875707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175096889360542489737250471 262645334040813734605875707)
      ·
        refine ⟨393968001061220601908813561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262645334040813734605875707 393968001061220601908813561)
        ·
          refine ⟨295476000795915451431610171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393968001061220601908813561 295476000795915451431610171)
          ·
            refine ⟨443214001193873177147415257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295476000795915451431610171 443214001193873177147415257)
            ·
              refine ⟨332410500895404882860561443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443214001193873177147415257 332410500895404882860561443)
              ·
                refine ⟨498615751343107324290842165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332410500895404882860561443 498615751343107324290842165)
                ·
                  refine ⟨46745226688416311652266453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498615751343107324290842165 46745226688416311652266453)
                  ·
                    refine ⟨1095591250509757304349995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46745226688416311652266453 1095591250509757304349995)
                    ·
                      rfl

theorem cell23_6400969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_6400969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400969 prefixEnd_6400969 := by exact prefixLift 6400969
  have htrace : WordTrace (prefixWord ++ tailWord_6400969) baseStart_6400969 baseEnd_6400969 := by
    simpa [prefixWord, tailWord_6400969, baseEnd_6400969] using wordTrace_append hprefix tailTrace_6400969
  have hstable : (prefixWord ++ tailWord_6400969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400969).length < 2 ^ (prefixWord ++ tailWord_6400969).sum := by decide
  have hdescent : baseEnd_6400969 < baseStart_6400969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6400986 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_6400986 : Nat := 118140960795 + 6400986 * 2 ^ 59
def prefixEnd_6400986 : Nat := 4983230072969 + 3 ^ 40 * 6400986 * 2
def baseEnd_6400986 : Nat := 1095594160233466115512469

theorem tailTrace_6400986 : CollatzResearch.WordTrace tailWord_6400986 prefixEnd_6400986 1095594160233466115512469 := by
  unfold tailWord_6400986
  simp only [CollatzResearch.WordTrace]
  refine ⟨58365784797082099554925703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155642092792218932146468541 58365784797082099554925703)
  ·
    refine ⟨87548677195623149332388555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58365784797082099554925703 87548677195623149332388555)
    ·
      refine ⟨131323015793434723998582833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87548677195623149332388555 131323015793434723998582833)
      ·
        refine ⟨98492261845076042998937125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131323015793434723998582833 98492261845076042998937125)
        ·
          refine ⟨18467299095951758062300711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98492261845076042998937125 18467299095951758062300711)
          ·
            refine ⟨27700948643927637093451067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18467299095951758062300711 27700948643927637093451067)
            ·
              refine ⟨41551422965891455640176601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27700948643927637093451067 41551422965891455640176601)
              ·
                refine ⟨31163567224418591730132451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41551422965891455640176601 31163567224418591730132451)
                ·
                  refine ⟨46745350836627887595198677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31163567224418591730132451 46745350836627887595198677)
                  ·
                    refine ⟨1095594160233466115512469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46745350836627887595198677 1095594160233466115512469)
                    ·
                      rfl

theorem cell23_6400986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_6400986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6400986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6400986 prefixEnd_6400986 := by exact prefixLift 6400986
  have htrace : WordTrace (prefixWord ++ tailWord_6400986) baseStart_6400986 baseEnd_6400986 := by
    simpa [prefixWord, tailWord_6400986, baseEnd_6400986] using wordTrace_append hprefix tailTrace_6400986
  have hstable : (prefixWord ++ tailWord_6400986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6400986).length < 2 ^ (prefixWord ++ tailWord_6400986).sum := by decide
  have hdescent : baseEnd_6400986 < baseStart_6400986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6400986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401060 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_6401060 : Nat := 118140960795 + 6401060 * 2 ^ 59
def prefixEnd_6401060 : Nat := 4983230072969 + 3 ^ 40 * 6401060 * 2
def baseEnd_6401060 : Nat := 3286820478268831057012067

theorem tailTrace_6401060 : CollatzResearch.WordTrace tailWord_6401060 prefixEnd_6401060 3286820478268831057012067 := by
  unfold tailWord_6401060
  simp only [CollatzResearch.WordTrace]
  refine ⟨116732919095030154428948317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155643892126706872571931089 116732919095030154428948317)
  ·
    refine ⟨43774844660636307910855619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116732919095030154428948317 43774844660636307910855619)
    ·
      refine ⟨65662266990954461866283429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43774844660636307910855619 65662266990954461866283429)
      ·
        refine ⟨12311675060803961599928143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65662266990954461866283429 12311675060803961599928143)
        ·
          refine ⟨18467512591205942399892215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311675060803961599928143 18467512591205942399892215)
          ·
            refine ⟨27701268886808913599838323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18467512591205942399892215 27701268886808913599838323)
            ·
              refine ⟨41551903330213370399757485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27701268886808913599838323 41551903330213370399757485)
              ·
                refine ⟨15581963748830013899909057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41551903330213370399757485 15581963748830013899909057)
                ·
                  refine ⟨11686472811622510424931793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15581963748830013899909057 11686472811622510424931793)
                  ·
                    refine ⟨8764854608716882818698845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11686472811622510424931793 8764854608716882818698845)
                    ·
                      refine ⟨3286820478268831057012067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8764854608716882818698845 3286820478268831057012067)
                      ·
                        rfl

theorem cell23_6401060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_6401060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401060 prefixEnd_6401060 := by exact prefixLift 6401060
  have htrace : WordTrace (prefixWord ++ tailWord_6401060) baseStart_6401060 baseEnd_6401060 := by
    simpa [prefixWord, tailWord_6401060, baseEnd_6401060] using wordTrace_append hprefix tailTrace_6401060
  have hstable : (prefixWord ++ tailWord_6401060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401060).length < 2 ^ (prefixWord ++ tailWord_6401060).sum := by decide
  have hdescent : baseEnd_6401060 < baseStart_6401060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401084 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_6401084 : Nat := 118140960795 + 6401084 * 2 ^ 59
def prefixEnd_6401084 : Nat := 4983230072969 + 3 ^ 40 * 6401084 * 2
def baseEnd_6401084 : Nat := 1095610933934846321037319

theorem tailTrace_6401084 : CollatzResearch.WordTrace tailWord_6401084 prefixEnd_6401084 1095610933934846321037319 := by
  unfold tailWord_6401084
  simp only [CollatzResearch.WordTrace]
  refine ⟨116733356770986680478385153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155644475694648907304513537 116733356770986680478385153)
  ·
    refine ⟨87550017578240010358788865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116733356770986680478385153 87550017578240010358788865)
    ·
      refine ⟨65662513183680007769091649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87550017578240010358788865 65662513183680007769091649)
      ·
        refine ⟨49246884887760005826818737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65662513183680007769091649 49246884887760005826818737)
        ·
          refine ⟨36935163665820004370114053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49246884887760005826818737 36935163665820004370114053)
          ·
            refine ⟨6925343187341250819396385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36935163665820004370114053 6925343187341250819396385)
            ·
              refine ⟨5194007390505938114547289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925343187341250819396385 5194007390505938114547289)
              ·
                refine ⟨3895505542879453585910467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194007390505938114547289 3895505542879453585910467)
                ·
                  refine ⟨5843258314319180378865701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895505542879453585910467 5843258314319180378865701)
                  ·
                    refine ⟨1095610933934846321037319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843258314319180378865701 1095610933934846321037319)
                    ·
                      rfl

theorem cell23_6401084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_6401084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401084 prefixEnd_6401084 := by exact prefixLift 6401084
  have htrace : WordTrace (prefixWord ++ tailWord_6401084) baseStart_6401084 baseEnd_6401084 := by
    simpa [prefixWord, tailWord_6401084, baseEnd_6401084] using wordTrace_append hprefix tailTrace_6401084
  have hstable : (prefixWord ++ tailWord_6401084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401084).length < 2 ^ (prefixWord ++ tailWord_6401084).sum := by decide
  have hdescent : baseEnd_6401084 < baseStart_6401084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401113 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 8, 2]
def baseStart_6401113 : Nat := 118140960795 + 6401113 * 2 ^ 59
def prefixEnd_6401113 : Nat := 4983230072969 + 3 ^ 40 * 6401113 * 2
def baseEnd_6401113 : Nat := 3286847692743519349649323

theorem tailTrace_6401113 : CollatzResearch.WordTrace tailWord_6401113 prefixEnd_6401113 3286847692743519349649323 := by
  unfold tailWord_6401113
  simp only [CollatzResearch.WordTrace]
  refine ⟨233467771258868298909575993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155645180839245532606383995 233467771258868298909575993)
  ·
    refine ⟨175100828444151224182181995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233467771258868298909575993 175100828444151224182181995)
    ·
      refine ⟨262651242666226836273272993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175100828444151224182181995 262651242666226836273272993)
      ·
        refine ⟨196988431999670127204954745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262651242666226836273272993 196988431999670127204954745)
        ·
          refine ⟨147741323999752595403716059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196988431999670127204954745 147741323999752595403716059)
          ·
            refine ⟨221611985999628893105574089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147741323999752595403716059 221611985999628893105574089)
            ·
              refine ⟨166208989499721669829180567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221611985999628893105574089 166208989499721669829180567)
              ·
                refine ⟨249313484249582504743770851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166208989499721669829180567 249313484249582504743770851)
                ·
                  refine ⟨373970226374373757115656277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249313484249582504743770851 373970226374373757115656277)
                  ·
                    refine ⟨4382463590324692466199097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 373970226374373757115656277 4382463590324692466199097)
                    ·
                      refine ⟨3286847692743519349649323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382463590324692466199097 3286847692743519349649323)
                      ·
                        rfl

theorem cell23_6401113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_6401113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401113 prefixEnd_6401113 := by exact prefixLift 6401113
  have htrace : WordTrace (prefixWord ++ tailWord_6401113) baseStart_6401113 baseEnd_6401113 := by
    simpa [prefixWord, tailWord_6401113, baseEnd_6401113] using wordTrace_append hprefix tailTrace_6401113
  have hstable : (prefixWord ++ tailWord_6401113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401113).length < 2 ^ (prefixWord ++ tailWord_6401113).sum := by decide
  have hdescent : baseEnd_6401113 < baseStart_6401113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401123 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 4, 4]
def baseStart_6401123 : Nat := 118140960795 + 6401123 * 2 ^ 59
def prefixEnd_6401123 : Nat := 4983230072969 + 3 ^ 40 * 6401123 * 2
def baseEnd_6401123 : Nat := 1095617609183354770174759

theorem tailTrace_6401123 : CollatzResearch.WordTrace tailWord_6401123 prefixEnd_6401123 1095617609183354770174759 := by
  unfold tailWord_6401123
  simp only [CollatzResearch.WordTrace]
  refine ⟨233468135988832070617440023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155645423992554713744960015 233468135988832070617440023)
  ·
    refine ⟨350202203983248105926160035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233468135988832070617440023 350202203983248105926160035)
    ·
      refine ⟨525303305974872158889240053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350202203983248105926160035 525303305974872158889240053)
      ·
        refine ⟨49247184935144264895866255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 525303305974872158889240053 49247184935144264895866255)
        ·
          refine ⟨73870777402716397343799383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49247184935144264895866255 73870777402716397343799383)
          ·
            refine ⟨110806166104074596015699075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73870777402716397343799383 110806166104074596015699075)
            ·
              refine ⟨166209249156111894023548613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110806166104074596015699075 166209249156111894023548613)
              ·
                refine ⟨31164234216770980129415365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166209249156111894023548613 31164234216770980129415365)
                ·
                  refine ⟨5843293915644558774265381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31164234216770980129415365 5843293915644558774265381)
                  ·
                    refine ⟨1095617609183354770174759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843293915644558774265381 1095617609183354770174759)
                    ·
                      rfl

theorem cell23_6401123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 4].length) (baseStart_6401123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401123 prefixEnd_6401123 := by exact prefixLift 6401123
  have htrace : WordTrace (prefixWord ++ tailWord_6401123) baseStart_6401123 baseEnd_6401123 := by
    simpa [prefixWord, tailWord_6401123, baseEnd_6401123] using wordTrace_append hprefix tailTrace_6401123
  have hstable : (prefixWord ++ tailWord_6401123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401123).length < 2 ^ (prefixWord ++ tailWord_6401123).sum := by decide
  have hdescent : baseEnd_6401123 < baseStart_6401123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401127 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 1, 5]
def baseStart_6401127 : Nat := 118140960795 + 6401127 * 2 ^ 59
def prefixEnd_6401127 : Nat := 4983230072969 + 3 ^ 40 * 6401127 * 2
def baseEnd_6401127 : Nat := 1095618293824227431624753

theorem tailTrace_6401127 : CollatzResearch.WordTrace tailWord_6401127 prefixEnd_6401127 1095618293824227431624753 := by
  unfold tailWord_6401127
  simp only [CollatzResearch.WordTrace]
  refine ⟨233468281880817579300585635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155645521253878386200390423 233468281880817579300585635)
  ·
    refine ⟨350202422821226368950878453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233468281880817579300585635 350202422821226368950878453)
    ·
      refine ⟨32831477139489972089144855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 350202422821226368950878453 32831477139489972089144855)
      ·
        refine ⟨49247215709234958133717283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32831477139489972089144855 49247215709234958133717283)
        ·
          refine ⟨73870823563852437200575925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49247215709234958133717283 73870823563852437200575925)
          ·
            refine ⟨6925389709111165987553993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73870823563852437200575925 6925389709111165987553993)
            ·
              refine ⟨5194042281833374490665495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925389709111165987553993 5194042281833374490665495)
              ·
                refine ⟨7791063422750061735998243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194042281833374490665495 7791063422750061735998243)
                ·
                  refine ⟨11686595134125092603997365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791063422750061735998243 11686595134125092603997365)
                  ·
                    refine ⟨1095618293824227431624753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11686595134125092603997365 1095618293824227431624753)
                    ·
                      rfl

theorem cell23_6401127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_6401127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401127 prefixEnd_6401127 := by exact prefixLift 6401127
  have htrace : WordTrace (prefixWord ++ tailWord_6401127) baseStart_6401127 baseEnd_6401127 := by
    simpa [prefixWord, tailWord_6401127, baseEnd_6401127] using wordTrace_append hprefix tailTrace_6401127
  have hstable : (prefixWord ++ tailWord_6401127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401127).length < 2 ^ (prefixWord ++ tailWord_6401127).sum := by decide
  have hdescent : baseEnd_6401127 < baseStart_6401127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401136 : List Nat := [2, 1, 1, 1, 5, 1, 12]
def baseStart_6401136 : Nat := 118140960795 + 6401136 * 2 ^ 59
def prefixEnd_6401136 : Nat := 4983230072969 + 3 ^ 40 * 6401136 * 2
def baseEnd_6401136 : Nat := 40578512380229293329157

theorem tailTrace_6401136 : CollatzResearch.WordTrace tailWord_6401136 prefixEnd_6401136 40578512380229293329157 := by
  unfold tailWord_6401136
  simp only [CollatzResearch.WordTrace]
  refine ⟨116734305068892486918831631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155645740091856649225108841 116734305068892486918831631)
  ·
    refine ⟨175101457603338730378247447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116734305068892486918831631 175101457603338730378247447)
    ·
      refine ⟨262652186405008095567371171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175101457603338730378247447 262652186405008095567371171)
      ·
        refine ⟨393978279607512143351056757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262652186405008095567371171 393978279607512143351056757)
        ·
          refine ⟨36935463713204263439161571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 393978279607512143351056757 36935463713204263439161571)
          ·
            refine ⟨55403195569806395158742357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36935463713204263439161571 55403195569806395158742357)
            ·
              refine ⟨40578512380229293329157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 55403195569806395158742357 40578512380229293329157)
              ·
                rfl

theorem cell23_6401136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 12].length) (baseStart_6401136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401136 prefixEnd_6401136 := by exact prefixLift 6401136
  have htrace : WordTrace (prefixWord ++ tailWord_6401136) baseStart_6401136 baseEnd_6401136 := by
    simpa [prefixWord, tailWord_6401136, baseEnd_6401136] using wordTrace_append hprefix tailTrace_6401136
  have hstable : (prefixWord ++ tailWord_6401136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401136).length < 2 ^ (prefixWord ++ tailWord_6401136).sum := by decide
  have hdescent : baseEnd_6401136 < baseStart_6401136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401157 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_6401157 : Nat := 118140960795 + 6401157 * 2 ^ 59
def prefixEnd_6401157 : Nat := 4983230072969 + 3 ^ 40 * 6401157 * 2
def baseEnd_6401157 : Nat := 1095623428630772392499707

theorem tailTrace_6401157 : CollatzResearch.WordTrace tailWord_6401157 prefixEnd_6401157 1095623428630772392499707 := by
  unfold tailWord_6401157
  simp only [CollatzResearch.WordTrace]
  refine ⟨233469376070708894424177725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155646250713805929616118483 233469376070708894424177725)
  ·
    refine ⟨87551016026515835409066647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233469376070708894424177725 87551016026515835409066647)
    ·
      refine ⟨131326524039773753113599971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87551016026515835409066647 131326524039773753113599971)
      ·
        refine ⟨196989786059660629670399957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131326524039773753113599971 196989786059660629670399957)
        ·
          refine ⟨4616948110773296007899999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 196989786059660629670399957 4616948110773296007899999)
          ·
            refine ⟨6925422166159944011849999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4616948110773296007899999 6925422166159944011849999)
            ·
              refine ⟨10388133249239916017774999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925422166159944011849999 10388133249239916017774999)
              ·
                refine ⟨15582199873859874026662499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10388133249239916017774999 15582199873859874026662499)
                ·
                  refine ⟨23373299810789811039993749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15582199873859874026662499 23373299810789811039993749)
                  ·
                    refine ⟨1095623428630772392499707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23373299810789811039993749 1095623428630772392499707)
                    ·
                      rfl

theorem cell23_6401157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_6401157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401157 prefixEnd_6401157 := by exact prefixLift 6401157
  have htrace : WordTrace (prefixWord ++ tailWord_6401157) baseStart_6401157 baseEnd_6401157 := by
    simpa [prefixWord, tailWord_6401157, baseEnd_6401157] using wordTrace_append hprefix tailTrace_6401157
  have hstable : (prefixWord ++ tailWord_6401157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401157).length < 2 ^ (prefixWord ++ tailWord_6401157).sum := by decide
  have hdescent : baseEnd_6401157 < baseStart_6401157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401160 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6401160 : Nat := 118140960795 + 6401160 * 2 ^ 59
def prefixEnd_6401160 : Nat := 4983230072969 + 3 ^ 40 * 6401160 * 2
def baseEnd_6401160 : Nat := 3286871826334280665761607

theorem tailTrace_6401160 : CollatzResearch.WordTrace tailWord_6401160 prefixEnd_6401160 3286871826334280665761607 := by
  unfold tailWord_6401160
  simp only [CollatzResearch.WordTrace]
  refine ⟨116734742744849012968268467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155646323659798683957691289 116734742744849012968268467)
  ·
    refine ⟨175102114117273519452402701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116734742744849012968268467 175102114117273519452402701)
    ·
      refine ⟨65663292793977569794651013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175102114117273519452402701 65663292793977569794651013)
      ·
        refine ⟨12311867398870794336497065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65663292793977569794651013 12311867398870794336497065)
        ·
          refine ⟨9233900549153095752372799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12311867398870794336497065 9233900549153095752372799)
          ·
            refine ⟨13850850823729643628559199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9233900549153095752372799 13850850823729643628559199)
            ·
              refine ⟨20776276235594465442838799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13850850823729643628559199 20776276235594465442838799)
              ·
                refine ⟨31164414353391698164258199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20776276235594465442838799 31164414353391698164258199)
                ·
                  refine ⟨46746621530087547246387299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31164414353391698164258199 46746621530087547246387299)
                  ·
                    refine ⟨70119932295131320869580949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46746621530087547246387299 70119932295131320869580949)
                    ·
                      refine ⟨3286871826334280665761607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70119932295131320869580949 3286871826334280665761607)
                      ·
                        rfl

theorem cell23_6401160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6401160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401160 prefixEnd_6401160 := by exact prefixLift 6401160
  have htrace : WordTrace (prefixWord ++ tailWord_6401160) baseStart_6401160 baseEnd_6401160 := by
    simpa [prefixWord, tailWord_6401160, baseEnd_6401160] using wordTrace_append hprefix tailTrace_6401160
  have hstable : (prefixWord ++ tailWord_6401160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401160).length < 2 ^ (prefixWord ++ tailWord_6401160).sum := by decide
  have hdescent : baseEnd_6401160 < baseStart_6401160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401170 : List Nat := [3, 2, 3, 1, 1, 2, 4, 7]
def baseStart_6401170 : Nat := 118140960795 + 6401170 * 2 ^ 59
def prefixEnd_6401170 : Nat := 4983230072969 + 3 ^ 40 * 6401170 * 2
def baseEnd_6401170 : Nat := 121736183745956504690243

theorem tailTrace_6401170 : CollatzResearch.WordTrace tailWord_6401170 prefixEnd_6401170 121736183745956504690243 := by
  unfold tailWord_6401170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58367462554915449411100241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155646566813107865096267309 58367462554915449411100241)
  ·
    refine ⟨43775596916186587058325181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58367462554915449411100241 43775596916186587058325181)
    ·
      refine ⟨16415848843569970146871943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43775596916186587058325181 16415848843569970146871943)
      ·
        refine ⟨24623773265354955220307915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16415848843569970146871943 24623773265354955220307915)
        ·
          refine ⟨36935659898032432830461873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24623773265354955220307915 36935659898032432830461873)
          ·
            refine ⟨27701744923524324622846405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36935659898032432830461873 27701744923524324622846405)
            ·
              refine ⟨5194077173160810866783701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27701744923524324622846405 5194077173160810866783701)
              ·
                refine ⟨121736183745956504690243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5194077173160810866783701 121736183745956504690243)
                ·
                  rfl

theorem cell23_6401170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_6401170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401170 prefixEnd_6401170 := by exact prefixLift 6401170
  have htrace : WordTrace (prefixWord ++ tailWord_6401170) baseStart_6401170 baseEnd_6401170 := by
    simpa [prefixWord, tailWord_6401170, baseEnd_6401170] using wordTrace_append hprefix tailTrace_6401170
  have hstable : (prefixWord ++ tailWord_6401170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401170).length < 2 ^ (prefixWord ++ tailWord_6401170).sum := by decide
  have hdescent : baseEnd_6401170 < baseStart_6401170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401213 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_6401213 : Nat := 118140960795 + 6401213 * 2 ^ 59
def prefixEnd_6401213 : Nat := 4983230072969 + 3 ^ 40 * 6401213 * 2
def baseEnd_6401213 : Nat := 1095633013602989652799621

theorem tailTrace_6401213 : CollatzResearch.WordTrace tailWord_6401213 prefixEnd_6401213 1095633013602989652799621 := by
  unfold tailWord_6401213
  simp only [CollatzResearch.WordTrace]
  refine ⟨233471418558506015988216293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155647612372337343992144195 233471418558506015988216293)
  ·
    refine ⟨43775890979719877997790555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233471418558506015988216293 43775890979719877997790555)
    ·
      refine ⟨65663836469579816996685833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43775890979719877997790555 65663836469579816996685833)
      ·
        refine ⟨49247877352184862747514375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65663836469579816996685833 49247877352184862747514375)
        ·
          refine ⟨73871816028277294121271563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49247877352184862747514375 73871816028277294121271563)
          ·
            refine ⟨110807724042415941181907345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73871816028277294121271563 110807724042415941181907345)
            ·
              refine ⟨83105793031811955886430509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110807724042415941181907345 83105793031811955886430509)
              ·
                refine ⟨31164672386929483457411441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83105793031811955886430509 31164672386929483457411441)
                ·
                  refine ⟨23373504290197112593058581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31164672386929483457411441 23373504290197112593058581)
                  ·
                    refine ⟨1095633013602989652799621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23373504290197112593058581 1095633013602989652799621)
                    ·
                      rfl

theorem cell23_6401213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_6401213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401213 prefixEnd_6401213 := by exact prefixLift 6401213
  have htrace : WordTrace (prefixWord ++ tailWord_6401213) baseStart_6401213 baseEnd_6401213 := by
    simpa [prefixWord, tailWord_6401213, baseEnd_6401213] using wordTrace_append hprefix tailTrace_6401213
  have hstable : (prefixWord ++ tailWord_6401213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401213).length < 2 ^ (prefixWord ++ tailWord_6401213).sum := by decide
  have hdescent : baseEnd_6401213 < baseStart_6401213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401214 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_6401214 : Nat := 118140960795 + 6401214 * 2 ^ 59
def prefixEnd_6401214 : Nat := 4983230072969 + 3 ^ 40 * 6401214 * 2
def baseEnd_6401214 : Nat := 3286899554289623454486359

theorem tailTrace_6401214 : CollatzResearch.WordTrace tailWord_6401214 prefixEnd_6401214 3286899554289623454486359 := by
  unfold tailWord_6401214
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183931878937799144875337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155647636687668262106001797 29183931878937799144875337)
  ·
    refine ⟨21887948909203349358656503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29183931878937799144875337 21887948909203349358656503)
    ·
      refine ⟨32831923363805024037984755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21887948909203349358656503 32831923363805024037984755)
      ·
        refine ⟨49247885045707536056977133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32831923363805024037984755 49247885045707536056977133)
        ·
          refine ⟨18467956892140326021366425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49247885045707536056977133 18467956892140326021366425)
          ·
            refine ⟨13850967669105244516024819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18467956892140326021366425 13850967669105244516024819)
            ·
              refine ⟨20776451503657866774037229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13850967669105244516024819 20776451503657866774037229)
              ·
                refine ⟨7791169313871700040263961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20776451503657866774037229 7791169313871700040263961)
                ·
                  refine ⟨5843376985403775030197971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791169313871700040263961 5843376985403775030197971)
                  ·
                    refine ⟨8765065478105662545296957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5843376985403775030197971 8765065478105662545296957)
                    ·
                      refine ⟨3286899554289623454486359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8765065478105662545296957 3286899554289623454486359)
                      ·
                        rfl

theorem cell23_6401214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_6401214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401214 prefixEnd_6401214 := by exact prefixLift 6401214
  have htrace : WordTrace (prefixWord ++ tailWord_6401214) baseStart_6401214 baseEnd_6401214 := by
    simpa [prefixWord, tailWord_6401214, baseEnd_6401214] using wordTrace_append hprefix tailTrace_6401214
  have hstable : (prefixWord ++ tailWord_6401214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401214).length < 2 ^ (prefixWord ++ tailWord_6401214).sum := by decide
  have hdescent : baseEnd_6401214 < baseStart_6401214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401218 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_6401218 : Nat := 118140960795 + 6401218 * 2 ^ 59
def prefixEnd_6401218 : Nat := 4983230072969 + 3 ^ 40 * 6401218 * 2
def baseEnd_6401218 : Nat := 3286901608212241438836341

theorem tailTrace_6401218 : CollatzResearch.WordTrace tailWord_6401218 prefixEnd_6401218 3286901608212241438836341 := by
  unfold tailWord_6401218
  simp only [CollatzResearch.WordTrace]
  refine ⟨58367900230871975460537077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155647733948991934561432205 58367900230871975460537077)
  ·
    refine ⟨5471990646644247699425351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58367900230871975460537077 5471990646644247699425351)
    ·
      refine ⟨8207985969966371549138027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471990646644247699425351 8207985969966371549138027)
      ·
        refine ⟨12311978954949557323707041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8207985969966371549138027 12311978954949557323707041)
        ·
          refine ⟨9233984216212167992780281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12311978954949557323707041 9233984216212167992780281)
          ·
            refine ⟨6925488162159125994585211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9233984216212167992780281 6925488162159125994585211)
            ·
              refine ⟨10388232243238688991877817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925488162159125994585211 10388232243238688991877817)
              ·
                refine ⟨7791174182429016743908363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10388232243238688991877817 7791174182429016743908363)
                ·
                  refine ⟨11686761273643525115862545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791174182429016743908363 11686761273643525115862545)
                  ·
                    refine ⟨8765070955232643836896909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11686761273643525115862545 8765070955232643836896909)
                    ·
                      refine ⟨3286901608212241438836341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8765070955232643836896909 3286901608212241438836341)
                      ·
                        rfl

theorem cell23_6401218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_6401218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401218 prefixEnd_6401218 := by exact prefixLift 6401218
  have htrace : WordTrace (prefixWord ++ tailWord_6401218) baseStart_6401218 baseEnd_6401218 := by
    simpa [prefixWord, tailWord_6401218, baseEnd_6401218] using wordTrace_append hprefix tailTrace_6401218
  have hstable : (prefixWord ++ tailWord_6401218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401218).length < 2 ^ (prefixWord ++ tailWord_6401218).sum := by decide
  have hdescent : baseEnd_6401218 < baseStart_6401218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401233 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_6401233 : Nat := 118140960795 + 6401233 * 2 ^ 59
def prefixEnd_6401233 : Nat := 4983230072969 + 3 ^ 40 * 6401233 * 2
def baseEnd_6401233 : Nat := 3286909310422058880148771

theorem tailTrace_6401233 : CollatzResearch.WordTrace tailWord_6401233 prefixEnd_6401233 3286909310422058880148771 := by
  unfold tailWord_6401233
  simp only [CollatzResearch.WordTrace]
  refine ⟨233472148018433559403944353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155648098678955706269296235 233472148018433559403944353)
  ·
    refine ⟨175104111013825169552958265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233472148018433559403944353 175104111013825169552958265)
    ·
      refine ⟨131328083260368877164718699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175104111013825169552958265 131328083260368877164718699)
      ·
        refine ⟨196992124890553315747078049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131328083260368877164718699 196992124890553315747078049)
        ·
          refine ⟨147744093667914986810308537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196992124890553315747078049 147744093667914986810308537)
          ·
            refine ⟨110808070250936240107731403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147744093667914986810308537 110808070250936240107731403)
            ·
              refine ⟨166212105376404360161597105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110808070250936240107731403 166212105376404360161597105)
              ·
                refine ⟨124659079032303270121197829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166212105376404360161597105 124659079032303270121197829)
                ·
                  refine ⟨23373577318556863147724593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124659079032303270121197829 23373577318556863147724593)
                  ·
                    refine ⟨17530182988917647360793445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23373577318556863147724593 17530182988917647360793445)
                    ·
                      refine ⟨3286909310422058880148771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17530182988917647360793445 3286909310422058880148771)
                      ·
                        rfl

theorem cell23_6401233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_6401233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401233 prefixEnd_6401233 := by exact prefixLift 6401233
  have htrace : WordTrace (prefixWord ++ tailWord_6401233) baseStart_6401233 baseEnd_6401233 := by
    simpa [prefixWord, tailWord_6401233, baseEnd_6401233] using wordTrace_append hprefix tailTrace_6401233
  have hstable : (prefixWord ++ tailWord_6401233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401233).length < 2 ^ (prefixWord ++ tailWord_6401233).sum := by decide
  have hdescent : baseEnd_6401233 < baseStart_6401233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401237 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6401237 : Nat := 118140960795 + 6401237 * 2 ^ 59
def prefixEnd_6401237 : Nat := 4983230072969 + 3 ^ 40 * 6401237 * 2
def baseEnd_6401237 : Nat := 3286911364344676864498753

theorem tailTrace_6401237 : CollatzResearch.WordTrace tailWord_6401237 prefixEnd_6401237 3286911364344676864498753 := by
  unfold tailWord_6401237
  simp only [CollatzResearch.WordTrace]
  refine ⟨233472293910419068087089965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155648195940279378724726643 233472293910419068087089965)
  ·
    refine ⟨87552110216407150532658737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233472293910419068087089965 87552110216407150532658737)
    ·
      refine ⟨65664082662305362899494053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87552110216407150532658737 65664082662305362899494053)
      ·
        refine ⟨12312015499182255543655135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65664082662305362899494053 12312015499182255543655135)
        ·
          refine ⟨18468023248773383315482703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12312015499182255543655135 18468023248773383315482703)
          ·
            refine ⟨27702034873160074973224055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18468023248773383315482703 27702034873160074973224055)
            ·
              refine ⟨41553052309740112459836083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27702034873160074973224055 41553052309740112459836083)
              ·
                refine ⟨62329578464610168689754125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41553052309740112459836083 62329578464610168689754125)
                ·
                  refine ⟨23373591924228813258657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62329578464610168689754125 23373591924228813258657797)
                  ·
                    refine ⟨4382548485792902485998337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23373591924228813258657797 4382548485792902485998337)
                    ·
                      refine ⟨3286911364344676864498753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382548485792902485998337 3286911364344676864498753)
                      ·
                        rfl

theorem cell23_6401237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6401237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401237 prefixEnd_6401237 := by exact prefixLift 6401237
  have htrace : WordTrace (prefixWord ++ tailWord_6401237) baseStart_6401237 baseEnd_6401237 := by
    simpa [prefixWord, tailWord_6401237, baseEnd_6401237] using wordTrace_append hprefix tailTrace_6401237
  have hstable : (prefixWord ++ tailWord_6401237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401237).length < 2 ^ (prefixWord ++ tailWord_6401237).sum := by decide
  have hdescent : baseEnd_6401237 < baseStart_6401237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401273 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_6401273 : Nat := 118140960795 + 6401273 * 2 ^ 59
def prefixEnd_6401273 : Nat := 4983230072969 + 3 ^ 40 * 6401273 * 2
def baseEnd_6401273 : Nat := 1095643283216079574549529

theorem tailTrace_6401273 : CollatzResearch.WordTrace tailWord_6401273 prefixEnd_6401273 1095643283216079574549529 := by
  unfold tailWord_6401273
  simp only [CollatzResearch.WordTrace]
  refine ⟨233473606938288646235400473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155649071292192430823600315 233473606938288646235400473)
  ·
    refine ⟨175105205203716484676550355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233473606938288646235400473 175105205203716484676550355)
    ·
      refine ⟨262657807805574727014825533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175105205203716484676550355 262657807805574727014825533)
      ·
        refine ⟨98496677927090522630559575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262657807805574727014825533 98496677927090522630559575)
        ·
          refine ⟨147745016890635783945839363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98496677927090522630559575 147745016890635783945839363)
          ·
            refine ⟨221617525335953675918759045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147745016890635783945839363 221617525335953675918759045)
            ·
              refine ⟨41553286000491314234767321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221617525335953675918759045 41553286000491314234767321)
              ·
                refine ⟨31164964500368485676075491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41553286000491314234767321 31164964500368485676075491)
                ·
                  refine ⟨46747446750552728514113237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31164964500368485676075491 46747446750552728514113237)
                  ·
                    refine ⟨1095643283216079574549529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46747446750552728514113237 1095643283216079574549529)
                    ·
                      rfl

theorem cell23_6401273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_6401273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401273 prefixEnd_6401273 := by exact prefixLift 6401273
  have htrace : WordTrace (prefixWord ++ tailWord_6401273) baseStart_6401273 baseEnd_6401273 := by
    simpa [prefixWord, tailWord_6401273, baseEnd_6401273] using wordTrace_append hprefix tailTrace_6401273
  have hstable : (prefixWord ++ tailWord_6401273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401273).length < 2 ^ (prefixWord ++ tailWord_6401273).sum := by decide
  have hdescent : baseEnd_6401273 < baseStart_6401273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401280 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 4, 5, 2]
def baseStart_6401280 : Nat := 118140960795 + 6401280 * 2 ^ 59
def prefixEnd_6401280 : Nat := 4983230072969 + 3 ^ 40 * 6401280 * 2
def baseEnd_6401280 : Nat := 3286933444012820196261055

theorem tailTrace_6401280 : CollatzResearch.WordTrace tailWord_6401280 prefixEnd_6401280 3286933444012820196261055 := by
  unfold tailWord_6401280
  simp only [CollatzResearch.WordTrace]
  refine ⟨116736931124631643215452647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155649241499508857620603529 116736931124631643215452647)
  ·
    refine ⟨175105396686947464823178971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116736931124631643215452647 175105396686947464823178971)
    ·
      refine ⟨262658095030421197234768457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175105396686947464823178971 262658095030421197234768457)
      ·
        refine ⟨196993571272815897926076343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262658095030421197234768457 196993571272815897926076343)
        ·
          refine ⟨295490356909223846889114515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196993571272815897926076343 295490356909223846889114515)
          ·
            refine ⟨443235535363835770333671773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295490356909223846889114515 443235535363835770333671773)
            ·
              refine ⟨166213325761438413875126915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 443235535363835770333671773 166213325761438413875126915)
              ·
                refine ⟨249319988642157620812690373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166213325761438413875126915 249319988642157620812690373)
                ·
                  refine ⟨46747497870404553902379445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249319988642157620812690373 46747497870404553902379445)
                  ·
                    refine ⟨4382577925350426928348073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46747497870404553902379445 4382577925350426928348073)
                    ·
                      refine ⟨3286933444012820196261055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382577925350426928348073 3286933444012820196261055)
                      ·
                        rfl

theorem cell23_6401280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_6401280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401280 prefixEnd_6401280 := by exact prefixLift 6401280
  have htrace : WordTrace (prefixWord ++ tailWord_6401280) baseStart_6401280 baseEnd_6401280 := by
    simpa [prefixWord, tailWord_6401280, baseEnd_6401280] using wordTrace_append hprefix tailTrace_6401280
  have hstable : (prefixWord ++ tailWord_6401280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401280).length < 2 ^ (prefixWord ++ tailWord_6401280).sum := by decide
  have hdescent : baseEnd_6401280 < baseStart_6401280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401404 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_6401404 : Nat := 118140960795 + 6401404 * 2 ^ 59
def prefixEnd_6401404 : Nat := 4983230072969 + 3 ^ 40 * 6401404 * 2
def baseEnd_6401404 : Nat := 3286997115613977711110485

theorem tailTrace_6401404 : CollatzResearch.WordTrace tailWord_6401404 prefixEnd_6401404 3286997115613977711110485 := by
  unfold tailWord_6401404
  simp only [CollatzResearch.WordTrace]
  refine ⟨116739192450407027804209633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155652256600542703738946177 116739192450407027804209633)
  ·
    refine ⟨87554394337805270853157225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116739192450407027804209633 87554394337805270853157225)
    ·
      refine ⟨65665795753353953139867919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87554394337805270853157225 65665795753353953139867919)
      ·
        refine ⟨98498693630030929709801879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65665795753353953139867919 98498693630030929709801879)
        ·
          refine ⟨147748040445046394564702819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98498693630030929709801879 147748040445046394564702819)
          ·
            refine ⟨221622060667569591847054229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147748040445046394564702819 221622060667569591847054229)
            ·
              refine ⟨10388534093792324617830667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221622060667569591847054229 10388534093792324617830667)
              ·
                refine ⟨15582801140688486926746001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10388534093792324617830667 15582801140688486926746001)
                ·
                  refine ⟨11687100855516365195059501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15582801140688486926746001 11687100855516365195059501)
                  ·
                    refine ⟨4382662820818636948147313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11687100855516365195059501 4382662820818636948147313)
                    ·
                      refine ⟨3286997115613977711110485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382662820818636948147313 3286997115613977711110485)
                      ·
                        rfl

theorem cell23_6401404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_6401404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401404 prefixEnd_6401404 := by exact prefixLift 6401404
  have htrace : WordTrace (prefixWord ++ tailWord_6401404) baseStart_6401404 baseEnd_6401404 := by
    simpa [prefixWord, tailWord_6401404, baseEnd_6401404] using wordTrace_append hprefix tailTrace_6401404
  have hstable : (prefixWord ++ tailWord_6401404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401404).length < 2 ^ (prefixWord ++ tailWord_6401404).sum := by decide
  have hdescent : baseEnd_6401404 < baseStart_6401404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401428 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6401428 : Nat := 118140960795 + 6401428 * 2 ^ 59
def prefixEnd_6401428 : Nat := 4983230072969 + 3 ^ 40 * 6401428 * 2
def baseEnd_6401428 : Nat := 3287009439149685617210375

theorem tailTrace_6401428 : CollatzResearch.WordTrace tailWord_6401428 prefixEnd_6401428 3287009439149685617210375 := by
  unfold tailWord_6401428
  simp only [CollatzResearch.WordTrace]
  refine ⟨116739630126363553853646469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155652840168484738471528625 116739630126363553853646469)
  ·
    refine ⟨21888680648693166347558713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116739630126363553853646469 21888680648693166347558713)
    ·
      refine ⟨16416510486519874760669035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21888680648693166347558713 16416510486519874760669035)
      ·
        refine ⟨24624765729779812141003553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16416510486519874760669035 24624765729779812141003553)
        ·
          refine ⟨18468574297334859105752665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24624765729779812141003553 18468574297334859105752665)
          ·
            refine ⟨13851430723001144329314499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18468574297334859105752665 13851430723001144329314499)
            ·
              refine ⟨20777146084501716493971749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13851430723001144329314499 20777146084501716493971749)
              ·
                refine ⟨3895714890844071842619703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20777146084501716493971749 3895714890844071842619703)
                ·
                  refine ⟨5843572336266107763929555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895714890844071842619703 5843572336266107763929555)
                  ·
                    refine ⟨8765358504399161645894333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5843572336266107763929555 8765358504399161645894333)
                    ·
                      refine ⟨3287009439149685617210375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8765358504399161645894333 3287009439149685617210375)
                      ·
                        rfl

theorem cell23_6401428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6401428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401428 prefixEnd_6401428 := by exact prefixLift 6401428
  have htrace : WordTrace (prefixWord ++ tailWord_6401428) baseStart_6401428 baseEnd_6401428 := by
    simpa [prefixWord, tailWord_6401428, baseEnd_6401428] using wordTrace_append hprefix tailTrace_6401428
  have hstable : (prefixWord ++ tailWord_6401428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401428).length < 2 ^ (prefixWord ++ tailWord_6401428).sum := by decide
  have hdescent : baseEnd_6401428 < baseStart_6401428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401457 : List Nat := [1, 2, 2, 4, 1, 1, 5, 7]
def baseStart_6401457 : Nat := 118140960795 + 6401457 * 2 ^ 59
def prefixEnd_6401457 : Nat := 4983230072969 + 3 ^ 40 * 6401457 * 2
def baseEnd_6401457 : Nat := 121741641855135777916583

theorem tailTrace_6401457 : CollatzResearch.WordTrace tailWord_6401457 prefixEnd_6401457 121741641855135777916583 := by
  unfold tailWord_6401457
  simp only [CollatzResearch.WordTrace]
  refine ⟨233480317969622045660098625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155653545313081363773399083 233480317969622045660098625)
  ·
    refine ⟨175110238477216534245073969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233480317969622045660098625 175110238477216534245073969)
    ·
      refine ⟨131332678857912400683805477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175110238477216534245073969 131332678857912400683805477)
      ·
        refine ⟨24624877285858575128213527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131332678857912400683805477 24624877285858575128213527)
        ·
          refine ⟨36937315928787862692320291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24624877285858575128213527 36937315928787862692320291)
          ·
            refine ⟨55405973893181794038480437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36937315928787862692320291 55405973893181794038480437)
            ·
              refine ⟨5194310052485793191107541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55405973893181794038480437 5194310052485793191107541)
              ·
                refine ⟨121741641855135777916583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5194310052485793191107541 121741641855135777916583)
                ·
                  rfl

theorem cell23_6401457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 7].length) (baseStart_6401457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401457 prefixEnd_6401457 := by exact prefixLift 6401457
  have htrace : WordTrace (prefixWord ++ tailWord_6401457) baseStart_6401457 baseEnd_6401457 := by
    simpa [prefixWord, tailWord_6401457, baseEnd_6401457] using wordTrace_append hprefix tailTrace_6401457
  have hstable : (prefixWord ++ tailWord_6401457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401457).length < 2 ^ (prefixWord ++ tailWord_6401457).sum := by decide
  have hdescent : baseEnd_6401457 < baseStart_6401457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401468 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6401468 : Nat := 118140960795 + 6401468 * 2 ^ 59
def prefixEnd_6401468 : Nat := 4983230072969 + 3 ^ 40 * 6401468 * 2
def baseEnd_6401468 : Nat := 3287029978375865460710191

theorem tailTrace_6401468 : CollatzResearch.WordTrace tailWord_6401468 prefixEnd_6401468 3287029978375865460710191 := by
  unfold tailWord_6401468
  simp only [CollatzResearch.WordTrace]
  refine ⟨116740359586291097269374529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155653812781721463025832705 116740359586291097269374529)
  ·
    refine ⟨87555269689718322952030897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116740359586291097269374529 87555269689718322952030897)
    ·
      refine ⟨65666452267288742214023173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87555269689718322952030897 65666452267288742214023173)
      ·
        refine ⟨12312459800116639165129345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65666452267288742214023173 12312459800116639165129345)
        ·
          refine ⟨9234344850087479373847009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12312459800116639165129345 9234344850087479373847009)
          ·
            refine ⟨6925758637565609530385257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9234344850087479373847009 6925758637565609530385257)
            ·
              refine ⟨5194318978174207147788943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925758637565609530385257 5194318978174207147788943)
              ·
                refine ⟨7791478467261310721683415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194318978174207147788943 7791478467261310721683415)
                ·
                  refine ⟨11687217700891966082525123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791478467261310721683415 11687217700891966082525123)
                  ·
                    refine ⟨17530826551337949123787685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11687217700891966082525123 17530826551337949123787685)
                    ·
                      refine ⟨3287029978375865460710191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17530826551337949123787685 3287029978375865460710191)
                      ·
                        rfl

theorem cell23_6401468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6401468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401468 prefixEnd_6401468 := by exact prefixLift 6401468
  have htrace : WordTrace (prefixWord ++ tailWord_6401468) baseStart_6401468 baseEnd_6401468 := by
    simpa [prefixWord, tailWord_6401468, baseEnd_6401468] using wordTrace_append hprefix tailTrace_6401468
  have hstable : (prefixWord ++ tailWord_6401468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401468).length < 2 ^ (prefixWord ++ tailWord_6401468).sum := by decide
  have hdescent : baseEnd_6401468 < baseStart_6401468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401501 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_6401501 : Nat := 118140960795 + 6401501 * 2 ^ 59
def prefixEnd_6401501 : Nat := 4983230072969 + 3 ^ 40 * 6401501 * 2
def baseEnd_6401501 : Nat := 3287046923237463831597539

theorem tailTrace_6401501 : CollatzResearch.WordTrace tailWord_6401501 prefixEnd_6401501 3287046923237463831597539 := by
  unfold tailWord_6401501
  simp only [CollatzResearch.WordTrace]
  refine ⟨233481922781462641174700357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155654615187641760783133571 233481922781462641174700357)
  ·
    refine ⟨43777860521524245220256317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233481922781462641174700357 43777860521524245220256317)
    ·
      refine ⟨16416697695571591957596119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43777860521524245220256317 16416697695571591957596119)
      ·
        refine ⟨24625046543357387936394179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16416697695571591957596119 24625046543357387936394179)
        ·
          refine ⟨36937569815036081904591269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24625046543357387936394179 36937569815036081904591269)
          ·
            refine ⟨6925794340319265357110863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36937569815036081904591269 6925794340319265357110863)
            ·
              refine ⟨10388691510478898035666295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925794340319265357110863 10388691510478898035666295)
              ·
                refine ⟨15583037265718347053499443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10388691510478898035666295 15583037265718347053499443)
                ·
                  refine ⟨23374555898577520580249165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15583037265718347053499443 23374555898577520580249165)
                  ·
                    refine ⟨8765458461966570217593437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23374555898577520580249165 8765458461966570217593437)
                    ·
                      refine ⟨3287046923237463831597539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8765458461966570217593437 3287046923237463831597539)
                      ·
                        rfl

theorem cell23_6401501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_6401501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401501 prefixEnd_6401501 := by exact prefixLift 6401501
  have htrace : WordTrace (prefixWord ++ tailWord_6401501) baseStart_6401501 baseEnd_6401501 := by
    simpa [prefixWord, tailWord_6401501, baseEnd_6401501] using wordTrace_append hprefix tailTrace_6401501
  have hstable : (prefixWord ++ tailWord_6401501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401501).length < 2 ^ (prefixWord ++ tailWord_6401501).sum := by decide
  have hdescent : baseEnd_6401501 < baseStart_6401501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401511 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6401511 : Nat := 118140960795 + 6401511 * 2 ^ 59
def prefixEnd_6401511 : Nat := 4983230072969 + 3 ^ 40 * 6401511 * 2
def baseEnd_6401511 : Nat := 3287052058044008792472493

theorem tailTrace_6401511 : CollatzResearch.WordTrace tailWord_6401511 prefixEnd_6401511 3287052058044008792472493 := by
  unfold tailWord_6401511
  simp only [CollatzResearch.WordTrace]
  refine ⟨233482287511426412882564387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155654858340950941921709591 233482287511426412882564387)
  ·
    refine ⟨350223431267139619323846581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233482287511426412882564387 350223431267139619323846581)
    ·
      refine ⟨32833446681294339311610617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 350223431267139619323846581 32833446681294339311610617)
      ·
        refine ⟨24625085010970754483707963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32833446681294339311610617 24625085010970754483707963)
        ·
          refine ⟨36937627516456131725561945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24625085010970754483707963 36937627516456131725561945)
          ·
            refine ⟨27703220637342098794171459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36937627516456131725561945 27703220637342098794171459)
            ·
              refine ⟨41554830956013148191257189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27703220637342098794171459 41554830956013148191257189)
              ·
                refine ⟨7791530804252465285860723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41554830956013148191257189 7791530804252465285860723)
                ·
                  refine ⟨11687296206378697928791085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791530804252465285860723 11687296206378697928791085)
                  ·
                    refine ⟨4382736077392011723296657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11687296206378697928791085 4382736077392011723296657)
                    ·
                      refine ⟨3287052058044008792472493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382736077392011723296657 3287052058044008792472493)
                      ·
                        rfl

theorem cell23_6401511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6401511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401511 prefixEnd_6401511 := by exact prefixLift 6401511
  have htrace : WordTrace (prefixWord ++ tailWord_6401511) baseStart_6401511 baseEnd_6401511 := by
    simpa [prefixWord, tailWord_6401511, baseEnd_6401511] using wordTrace_append hprefix tailTrace_6401511
  have hstable : (prefixWord ++ tailWord_6401511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401511).length < 2 ^ (prefixWord ++ tailWord_6401511).sum := by decide
  have hdescent : baseEnd_6401511 < baseStart_6401511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401541 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 2, 2, 2]
def baseStart_6401541 : Nat := 118140960795 + 6401541 * 2 ^ 59
def prefixEnd_6401541 : Nat := 4983230072969 + 3 ^ 40 * 6401541 * 2
def baseEnd_6401541 : Nat := 3287067462463643675097355

theorem tailTrace_6401541 : CollatzResearch.WordTrace tailWord_6401541 prefixEnd_6401541 3287067462463643675097355 := by
  unfold tailWord_6401541
  simp only [CollatzResearch.WordTrace]
  refine ⟨233483381701317728006156477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155655587800878485337437651 233483381701317728006156477)
  ·
    refine ⟨87556268137994148002308679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233483381701317728006156477 87556268137994148002308679)
    ·
      refine ⟨131334402206991222003463019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87556268137994148002308679 131334402206991222003463019)
      ·
        refine ⟨197001603310486833005194529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131334402206991222003463019 197001603310486833005194529)
        ·
          refine ⟨147751202482865124753895897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197001603310486833005194529 147751202482865124753895897)
          ·
            refine ⟨110813401862148843565421923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147751202482865124753895897 110813401862148843565421923)
            ·
              refine ⟨166220102793223265348132885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110813401862148843565421923 166220102793223265348132885)
              ·
                refine ⟨7791567318432340563193729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166220102793223265348132885 7791567318432340563193729)
                ·
                  refine ⟨5843675488824255422395297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791567318432340563193729 5843675488824255422395297)
                  ·
                    refine ⟨4382756616618191566796473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5843675488824255422395297 4382756616618191566796473)
                    ·
                      refine ⟨3287067462463643675097355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382756616618191566796473 3287067462463643675097355)
                      ·
                        rfl

theorem cell23_6401541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_6401541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401541 prefixEnd_6401541 := by exact prefixLift 6401541
  have htrace : WordTrace (prefixWord ++ tailWord_6401541) baseStart_6401541 baseEnd_6401541 := by
    simpa [prefixWord, tailWord_6401541, baseEnd_6401541] using wordTrace_append hprefix tailTrace_6401541
  have hstable : (prefixWord ++ tailWord_6401541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401541).length < 2 ^ (prefixWord ++ tailWord_6401541).sum := by decide
  have hdescent : baseEnd_6401541 < baseStart_6401541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401587 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5]
def baseStart_6401587 : Nat := 118140960795 + 6401587 * 2 ^ 59
def prefixEnd_6401587 : Nat := 4983230072969 + 3 ^ 40 * 6401587 * 2
def baseEnd_6401587 : Nat := 3287091082573750495122143

theorem tailTrace_6401587 : CollatzResearch.WordTrace tailWord_6401587 prefixEnd_6401587 3287091082573750495122143 := by
  unfold tailWord_6401587
  simp only [CollatzResearch.WordTrace]
  refine ⟨233485059459151077862331015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155656706306100718574887343 233485059459151077862331015)
  ·
    refine ⟨350227589188726616793496523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233485059459151077862331015 350227589188726616793496523)
    ·
      refine ⟨525341383783089925190244785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350227589188726616793496523 525341383783089925190244785)
      ·
        refine ⟨394006037837317443892683589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525341383783089925190244785 394006037837317443892683589)
        ·
          refine ⟨73876132094497020729878173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394006037837317443892683589 73876132094497020729878173)
          ·
            refine ⟨27703549535436382773704315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73876132094497020729878173 27703549535436382773704315)
            ·
              refine ⟨41555324303154574160556473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27703549535436382773704315 41555324303154574160556473)
              ·
                refine ⟨31166493227365930620417355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41555324303154574160556473 31166493227365930620417355)
                ·
                  refine ⟨46749739841048895930626033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31166493227365930620417355 46749739841048895930626033)
                  ·
                    refine ⟨35062304880786671947969525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46749739841048895930626033 35062304880786671947969525)
                    ·
                      refine ⟨3287091082573750495122143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35062304880786671947969525 3287091082573750495122143)
                      ·
                        rfl

theorem cell23_6401587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_6401587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401587 prefixEnd_6401587 := by exact prefixLift 6401587
  have htrace : WordTrace (prefixWord ++ tailWord_6401587) baseStart_6401587 baseEnd_6401587 := by
    simpa [prefixWord, tailWord_6401587, baseEnd_6401587] using wordTrace_append hprefix tailTrace_6401587
  have hstable : (prefixWord ++ tailWord_6401587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401587).length < 2 ^ (prefixWord ++ tailWord_6401587).sum := by decide
  have hdescent : baseEnd_6401587 < baseStart_6401587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401641 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 1, 4]
def baseStart_6401641 : Nat := 118140960795 + 6401641 * 2 ^ 59
def prefixEnd_6401641 : Nat := 4983230072969 + 3 ^ 40 * 6401641 * 2
def baseEnd_6401641 : Nat := 1095706270176364427948965

theorem tailTrace_6401641 : CollatzResearch.WordTrace tailWord_6401641 prefixEnd_6401641 1095706270176364427948965 := by
  unfold tailWord_6401641
  simp only [CollatzResearch.WordTrace]
  refine ⟨233487029000955445084796777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155658019333970296723197851 233487029000955445084796777)
  ·
    refine ⟨175115271750716583813597583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233487029000955445084796777 175115271750716583813597583)
    ·
      refine ⟨262672907626074875720396375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175115271750716583813597583 262672907626074875720396375)
      ·
        refine ⟨394009361439112313580594563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262672907626074875720396375 394009361439112313580594563)
        ·
          refine ⟨591014042158668470370891845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394009361439112313580594563 591014042158668470370891845)
          ·
            refine ⟨110815132904750338194542221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 591014042158668470370891845 110815132904750338194542221)
            ·
              refine ⟨41555674839281376822953333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110815132904750338194542221 41555674839281376822953333)
              ·
                refine ⟨3895844516182629077151875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41555674839281376822953333 3895844516182629077151875)
                ·
                  refine ⟨5843766774273943615727813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895844516182629077151875 5843766774273943615727813)
                  ·
                    refine ⟨1095706270176364427948965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843766774273943615727813 1095706270176364427948965)
                    ·
                      rfl

theorem cell23_6401641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 4].length) (baseStart_6401641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401641 prefixEnd_6401641 := by exact prefixLift 6401641
  have htrace : WordTrace (prefixWord ++ tailWord_6401641) baseStart_6401641 baseEnd_6401641 := by
    simpa [prefixWord, tailWord_6401641, baseEnd_6401641] using wordTrace_append hprefix tailTrace_6401641
  have hstable : (prefixWord ++ tailWord_6401641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401641).length < 2 ^ (prefixWord ++ tailWord_6401641).sum := by decide
  have hdescent : baseEnd_6401641 < baseStart_6401641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401657 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6401657 : Nat := 118140960795 + 6401657 * 2 ^ 59
def prefixEnd_6401657 : Nat := 4983230072969 + 3 ^ 40 * 6401657 * 2
def baseEnd_6401657 : Nat := 3287127026219565221246821

theorem tailTrace_6401657 : CollatzResearch.WordTrace tailWord_6401657 prefixEnd_6401657 3287127026219565221246821 := by
  unfold tailWord_6401657
  simp only [CollatzResearch.WordTrace]
  refine ⟨233487612568897479817379225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155658408379264986544919483 233487612568897479817379225)
  ·
    refine ⟨175115709426673109863034419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233487612568897479817379225 175115709426673109863034419)
    ·
      refine ⟨262673564140009664794551629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175115709426673109863034419 262673564140009664794551629)
      ·
        refine ⟨98502586552503624297956861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262673564140009664794551629 98502586552503624297956861)
        ·
          refine ⟨36938469957188859111733823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98502586552503624297956861 36938469957188859111733823)
          ·
            refine ⟨55407704935783288667600735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36938469957188859111733823 55407704935783288667600735)
            ·
              refine ⟨83111557403674933001401103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55407704935783288667600735 83111557403674933001401103)
              ·
                refine ⟨124667336105512399502101655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83111557403674933001401103 124667336105512399502101655)
                ·
                  refine ⟨187001004158268599253152483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124667336105512399502101655 187001004158268599253152483)
                  ·
                    refine ⟨280501506237402898879728725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187001004158268599253152483 280501506237402898879728725)
                    ·
                      refine ⟨3287127026219565221246821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 280501506237402898879728725 3287127026219565221246821)
                      ·
                        rfl

theorem cell23_6401657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6401657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401657 prefixEnd_6401657 := by exact prefixLift 6401657
  have htrace : WordTrace (prefixWord ++ tailWord_6401657) baseStart_6401657 baseEnd_6401657 := by
    simpa [prefixWord, tailWord_6401657, baseEnd_6401657] using wordTrace_append hprefix tailTrace_6401657
  have hstable : (prefixWord ++ tailWord_6401657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401657).length < 2 ^ (prefixWord ++ tailWord_6401657).sum := by decide
  have hdescent : baseEnd_6401657 < baseStart_6401657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401671 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 6]
def baseStart_6401671 : Nat := 118140960795 + 6401671 * 2 ^ 59
def prefixEnd_6401671 : Nat := 4983230072969 + 3 ^ 40 * 6401671 * 2
def baseEnd_6401671 : Nat := 365237134994303129607973

theorem tailTrace_6401671 : CollatzResearch.WordTrace tailWord_6401671 prefixEnd_6401671 365237134994303129607973 := by
  unfold tailWord_6401671
  simp only [CollatzResearch.WordTrace]
  refine ⟨233488123190846760208388867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155658748793897840138925911 233488123190846760208388867)
  ·
    refine ⟨350232184786270140312583301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233488123190846760208388867 350232184786270140312583301)
    ·
      refine ⟨65668534647425651308609369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350232184786270140312583301 65668534647425651308609369)
      ·
        refine ⟨49251400985569238481457027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65668534647425651308609369 49251400985569238481457027)
        ·
          refine ⟨73877101478353857722185541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49251400985569238481457027 73877101478353857722185541)
          ·
            refine ⟨13851956527191348322909789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73877101478353857722185541 13851956527191348322909789)
            ·
              refine ⟨5194483697696755621091171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13851956527191348322909789 5194483697696755621091171)
              ·
                refine ⟨7791725546545133431636757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194483697696755621091171 7791725546545133431636757)
                ·
                  refine ⟨365237134994303129607973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7791725546545133431636757 365237134994303129607973)
                  ·
                    rfl

theorem cell23_6401671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 6].length) (baseStart_6401671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401671 prefixEnd_6401671 := by exact prefixLift 6401671
  have htrace : WordTrace (prefixWord ++ tailWord_6401671) baseStart_6401671 baseEnd_6401671 := by
    simpa [prefixWord, tailWord_6401671, baseEnd_6401671] using wordTrace_append hprefix tailTrace_6401671
  have hstable : (prefixWord ++ tailWord_6401671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401671).length < 2 ^ (prefixWord ++ tailWord_6401671).sum := by decide
  have hdescent : baseEnd_6401671 < baseStart_6401671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401692 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_6401692 : Nat := 118140960795 + 6401692 * 2 ^ 59
def prefixEnd_6401692 : Nat := 4983230072969 + 3 ^ 40 * 6401692 * 2
def baseEnd_6401692 : Nat := 1095714999347490861436387

theorem tailTrace_6401692 : CollatzResearch.WordTrace tailWord_6401692 prefixEnd_6401692 1095714999347490861436387 := by
  unfold tailWord_6401692
  simp only [CollatzResearch.WordTrace]
  refine ⟨116744444561885340397451665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155659259415847120529935553 116744444561885340397451665)
  ·
    refine ⟨87558333421414005298088749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116744444561885340397451665 87558333421414005298088749)
    ·
      refine ⟨32834375033030251986783281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87558333421414005298088749 32834375033030251986783281)
      ·
        refine ⟨24625781274772688990087461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32834375033030251986783281 24625781274772688990087461)
        ·
          refine ⟨4617333989019879185641399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24625781274772688990087461 4617333989019879185641399)
          ·
            refine ⟨6926000983529818778462099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617333989019879185641399 6926000983529818778462099)
            ·
              refine ⟨10389001475294728167693149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926000983529818778462099 10389001475294728167693149)
              ·
                refine ⟨3895875553235523062884931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10389001475294728167693149 3895875553235523062884931)
                ·
                  refine ⟨5843813329853284594327397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895875553235523062884931 5843813329853284594327397)
                  ·
                    refine ⟨1095714999347490861436387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843813329853284594327397 1095714999347490861436387)
                    ·
                      rfl

theorem cell23_6401692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_6401692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401692 prefixEnd_6401692 := by exact prefixLift 6401692
  have htrace : WordTrace (prefixWord ++ tailWord_6401692) baseStart_6401692 baseEnd_6401692 := by
    simpa [prefixWord, tailWord_6401692, baseEnd_6401692] using wordTrace_append hprefix tailTrace_6401692
  have hstable : (prefixWord ++ tailWord_6401692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401692).length < 2 ^ (prefixWord ++ tailWord_6401692).sum := by decide
  have hdescent : baseEnd_6401692 < baseStart_6401692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401715 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 1, 1, 3]
def baseStart_6401715 : Nat := 118140960795 + 6401715 * 2 ^ 59
def prefixEnd_6401715 : Nat := 4983230072969 + 3 ^ 40 * 6401715 * 2
def baseEnd_6401715 : Nat := 3287156808097525994321555

theorem tailTrace_6401715 : CollatzResearch.WordTrace tailWord_6401715 prefixEnd_6401715 3287156808097525994321555 := by
  unfold tailWord_6401715
  simp only [CollatzResearch.WordTrace]
  refine ⟨233489728002687355722990599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155659818668458237148660399 233489728002687355722990599)
  ·
    refine ⟨350234592004031033584485899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233489728002687355722990599 350234592004031033584485899)
    ·
      refine ⟨525351888006046550376728849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350234592004031033584485899 525351888006046550376728849)
      ·
        refine ⟨394013916004534912782546637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525351888006046550376728849 394013916004534912782546637)
        ·
          refine ⟨147755218501700592293454989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394013916004534912782546637 147755218501700592293454989)
          ·
            refine ⟨55408206938137722110045621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147755218501700592293454989 55408206938137722110045621)
            ·
              refine ⟨5194519400450411447816777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55408206938137722110045621 5194519400450411447816777)
              ·
                refine ⟨3895889550337808585862583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194519400450411447816777 3895889550337808585862583)
                ·
                  refine ⟨5843834325506712878793875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895889550337808585862583 5843834325506712878793875)
                  ·
                    refine ⟨8765751488260069318190813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5843834325506712878793875 8765751488260069318190813)
                    ·
                      refine ⟨3287156808097525994321555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8765751488260069318190813 3287156808097525994321555)
                      ·
                        rfl

theorem cell23_6401715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 1, 3].length) (baseStart_6401715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401715 prefixEnd_6401715 := by exact prefixLift 6401715
  have htrace : WordTrace (prefixWord ++ tailWord_6401715) baseStart_6401715 baseEnd_6401715 := by
    simpa [prefixWord, tailWord_6401715, baseEnd_6401715] using wordTrace_append hprefix tailTrace_6401715
  have hstable : (prefixWord ++ tailWord_6401715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401715).length < 2 ^ (prefixWord ++ tailWord_6401715).sum := by decide
  have hdescent : baseEnd_6401715 < baseStart_6401715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401771 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 3]
def baseStart_6401771 : Nat := 118140960795 + 6401771 * 2 ^ 59
def prefixEnd_6401771 : Nat := 4983230072969 + 3 ^ 40 * 6401771 * 2
def baseEnd_6401771 : Nat := 3287185563014177775221297

theorem tailTrace_6401771 : CollatzResearch.WordTrace tailWord_6401771 prefixEnd_6401771 3287185563014177775221297 := by
  unfold tailWord_6401771
  simp only [CollatzResearch.WordTrace]
  refine ⟨233491770490484477287029167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155661180326989651524686111 233491770490484477287029167)
  ·
    refine ⟨350237655735726715930543751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233491770490484477287029167 350237655735726715930543751)
    ·
      refine ⟨525356483603590073895815627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350237655735726715930543751 525356483603590073895815627)
      ·
        refine ⟨788034725405385110843723441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525356483603590073895815627 788034725405385110843723441)
        ·
          refine ⟨591026044054038833132792581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788034725405385110843723441 591026044054038833132792581)
          ·
            refine ⟨110817383260132281212398609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 591026044054038833132792581 110817383260132281212398609)
            ·
              refine ⟨83113037445099210909298957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110817383260132281212398609 83113037445099210909298957)
              ·
                refine ⟨31167389041912204090987109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83113037445099210909298957 31167389041912204090987109)
                ·
                  refine ⟨5843885445358538267060083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31167389041912204090987109 5843885445358538267060083)
                  ·
                    refine ⟨8765828168037807400590125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5843885445358538267060083 8765828168037807400590125)
                    ·
                      refine ⟨3287185563014177775221297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8765828168037807400590125 3287185563014177775221297)
                      ·
                        rfl

theorem cell23_6401771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 3].length) (baseStart_6401771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401771 prefixEnd_6401771 := by exact prefixLift 6401771
  have htrace : WordTrace (prefixWord ++ tailWord_6401771) baseStart_6401771 baseEnd_6401771 := by
    simpa [prefixWord, tailWord_6401771, baseEnd_6401771] using wordTrace_append hprefix tailTrace_6401771
  have hstable : (prefixWord ++ tailWord_6401771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401771).length < 2 ^ (prefixWord ++ tailWord_6401771).sum := by decide
  have hdescent : baseEnd_6401771 < baseStart_6401771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401772 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 1, 2, 2]
def baseStart_6401772 : Nat := 118140960795 + 6401772 * 2 ^ 59
def prefixEnd_6401772 : Nat := 4983230072969 + 3 ^ 40 * 6401772 * 2
def baseEnd_6401772 : Nat := 3287186076494832271308793

theorem tailTrace_6401772 : CollatzResearch.WordTrace tailWord_6401772 prefixEnd_6401772 3287186076494832271308793 := by
  unfold tailWord_6401772
  simp only [CollatzResearch.WordTrace]
  refine ⟨116745903481740427228907785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155661204642320569638543713 116745903481740427228907785)
  ·
    refine ⟨87559427611305320421680839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116745903481740427228907785 87559427611305320421680839)
    ·
      refine ⟨131339141416957980632521259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87559427611305320421680839 131339141416957980632521259)
      ·
        refine ⟨197008712125436970948781889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131339141416957980632521259 197008712125436970948781889)
        ·
          refine ⟨147756534094077728211586417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197008712125436970948781889 147756534094077728211586417)
          ·
            refine ⟨110817400570558296158689813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147756534094077728211586417 110817400570558296158689813)
            ·
              refine ⟨5194565651744920132438585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110817400570558296158689813 5194565651744920132438585)
              ·
                refine ⟨3895924238808690099328939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194565651744920132438585 3895924238808690099328939)
                ·
                  refine ⟨5843886358213035148993409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895924238808690099328939 5843886358213035148993409)
                  ·
                    refine ⟨4382914768659776361745057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5843886358213035148993409 4382914768659776361745057)
                    ·
                      refine ⟨3287186076494832271308793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382914768659776361745057 3287186076494832271308793)
                      ·
                        rfl

theorem cell23_6401772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_6401772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401772 prefixEnd_6401772 := by exact prefixLift 6401772
  have htrace : WordTrace (prefixWord ++ tailWord_6401772) baseStart_6401772 baseEnd_6401772 := by
    simpa [prefixWord, tailWord_6401772, baseEnd_6401772] using wordTrace_append hprefix tailTrace_6401772
  have hstable : (prefixWord ++ tailWord_6401772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401772).length < 2 ^ (prefixWord ++ tailWord_6401772).sum := by decide
  have hdescent : baseEnd_6401772 < baseStart_6401772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401774 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_6401774 : Nat := 118140960795 + 6401774 * 2 ^ 59
def prefixEnd_6401774 : Nat := 4983230072969 + 3 ^ 40 * 6401774 * 2
def baseEnd_6401774 : Nat := 1095729034485380421161261

theorem tailTrace_6401774 : CollatzResearch.WordTrace tailWord_6401774 prefixEnd_6401774 1095729034485380421161261 := by
  unfold tailWord_6401774
  simp only [CollatzResearch.WordTrace]
  refine ⟨29186484988684201099923547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155661253272982405866258917 29186484988684201099923547)
  ·
    refine ⟨43779727483026301649885321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29186484988684201099923547 43779727483026301649885321)
    ·
      refine ⟨32834795612269726237413991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43779727483026301649885321 32834795612269726237413991)
      ·
        refine ⟨49252193418404589356120987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32834795612269726237413991 49252193418404589356120987)
        ·
          refine ⟨73878290127606884034181481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49252193418404589356120987 73878290127606884034181481)
          ·
            refine ⟨55408717595705163025636111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73878290127606884034181481 55408717595705163025636111)
            ·
              refine ⟨83113076393557744538454167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55408717595705163025636111 83113076393557744538454167)
              ·
                refine ⟨124669614590336616807681251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83113076393557744538454167 124669614590336616807681251)
                ·
                  refine ⟨187004421885504925211521877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124669614590336616807681251 187004421885504925211521877)
                  ·
                    refine ⟨1095729034485380421161261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187004421885504925211521877 1095729034485380421161261)
                    ·
                      rfl

theorem cell23_6401774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_6401774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401774 prefixEnd_6401774 := by exact prefixLift 6401774
  have htrace : WordTrace (prefixWord ++ tailWord_6401774) baseStart_6401774 baseEnd_6401774 := by
    simpa [prefixWord, tailWord_6401774, baseEnd_6401774] using wordTrace_append hprefix tailTrace_6401774
  have hstable : (prefixWord ++ tailWord_6401774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401774).length < 2 ^ (prefixWord ++ tailWord_6401774).sum := by decide
  have hdescent : baseEnd_6401774 < baseStart_6401774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401788 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_6401788 : Nat := 118140960795 + 6401788 * 2 ^ 59
def prefixEnd_6401788 : Nat := 4983230072969 + 3 ^ 40 * 6401788 * 2
def baseEnd_6401788 : Nat := 3287194292185304208708719

theorem tailTrace_6401788 : CollatzResearch.WordTrace tailWord_6401788 prefixEnd_6401788 3287194292185304208708719 := by
  unfold tailWord_6401788
  simp only [CollatzResearch.WordTrace]
  refine ⟨116746195265711444595199009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155661593687615259460265345 116746195265711444595199009)
  ·
    refine ⟨87559646449283583446399257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116746195265711444595199009 87559646449283583446399257)
    ·
      refine ⟨65669734836962687584799443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87559646449283583446399257 65669734836962687584799443)
      ·
        refine ⟨98504602255444031377199165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65669734836962687584799443 98504602255444031377199165)
        ·
          refine ⟨36939225845791511766449687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98504602255444031377199165 36939225845791511766449687)
          ·
            refine ⟨55408838768687267649674531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36939225845791511766449687 55408838768687267649674531)
            ·
              refine ⟨83113258153030901474511797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55408838768687267649674531 83113258153030901474511797)
              ·
                refine ⟨7791867951846647013235481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83113258153030901474511797 7791867951846647013235481)
                ·
                  refine ⟨5843900963884985259926611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791867951846647013235481 5843900963884985259926611)
                  ·
                    refine ⟨8765851445827477889889917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5843900963884985259926611 8765851445827477889889917)
                    ·
                      refine ⟨3287194292185304208708719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8765851445827477889889917 3287194292185304208708719)
                      ·
                        rfl

theorem cell23_6401788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_6401788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401788 prefixEnd_6401788 := by exact prefixLift 6401788
  have htrace : WordTrace (prefixWord ++ tailWord_6401788) baseStart_6401788 baseEnd_6401788 := by
    simpa [prefixWord, tailWord_6401788, baseEnd_6401788] using wordTrace_append hprefix tailTrace_6401788
  have hstable : (prefixWord ++ tailWord_6401788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401788).length < 2 ^ (prefixWord ++ tailWord_6401788).sum := by decide
  have hdescent : baseEnd_6401788 < baseStart_6401788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401811 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 3, 4, 2]
def baseStart_6401811 : Nat := 118140960795 + 6401811 * 2 ^ 59
def prefixEnd_6401811 : Nat := 4983230072969 + 3 ^ 40 * 6401811 * 2
def baseEnd_6401811 : Nat := 3287206102240357618721113

theorem tailTrace_6401811 : CollatzResearch.WordTrace tailWord_6401811 prefixEnd_6401811 3287206102240357618721113 := by
  unfold tailWord_6401811
  simp only [CollatzResearch.WordTrace]
  refine ⟨233493229410339564118485287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155662152940226376078990191 233493229410339564118485287)
  ·
    refine ⟨350239844115509346177727931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233493229410339564118485287 350239844115509346177727931)
    ·
      refine ⟨525359766173264019266591897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350239844115509346177727931 525359766173264019266591897)
      ·
        refine ⟨394019824629948014449943923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525359766173264019266591897 394019824629948014449943923)
        ·
          refine ⟨591029736944922021674915885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394019824629948014449943923 591029736944922021674915885)
          ·
            refine ⟨221636151354345758128093457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591029736944922021674915885 221636151354345758128093457)
            ·
              refine ⟨166227113515759318596070093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221636151354345758128093457 166227113515759318596070093)
              ·
                refine ⟨62335167568409744473526285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166227113515759318596070093 62335167568409744473526285)
                ·
                  refine ⟨23375687838153654177572357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62335167568409744473526285 23375687838153654177572357)
                  ·
                    refine ⟨4382941469653810158294817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23375687838153654177572357 4382941469653810158294817)
                    ·
                      refine ⟨3287206102240357618721113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382941469653810158294817 3287206102240357618721113)
                      ·
                        rfl

theorem cell23_6401811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4, 2].length) (baseStart_6401811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401811 prefixEnd_6401811 := by exact prefixLift 6401811
  have htrace : WordTrace (prefixWord ++ tailWord_6401811) baseStart_6401811 baseEnd_6401811 := by
    simpa [prefixWord, tailWord_6401811, baseEnd_6401811] using wordTrace_append hprefix tailTrace_6401811
  have hstable : (prefixWord ++ tailWord_6401811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401811).length < 2 ^ (prefixWord ++ tailWord_6401811).sum := by decide
  have hdescent : baseEnd_6401811 < baseStart_6401811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401815 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 1, 3, 2]
def baseStart_6401815 : Nat := 118140960795 + 6401815 * 2 ^ 59
def prefixEnd_6401815 : Nat := 4983230072969 + 3 ^ 40 * 6401815 * 2
def baseEnd_6401815 : Nat := 3287208156162975603071095

theorem tailTrace_6401815 : CollatzResearch.WordTrace tailWord_6401815 prefixEnd_6401815 3287208156162975603071095 := by
  unfold tailWord_6401815
  simp only [CollatzResearch.WordTrace]
  refine ⟨233493375302325072801630899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155662250201550048534420599 233493375302325072801630899)
  ·
    refine ⟨350240062953487609202446349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233493375302325072801630899 350240062953487609202446349)
    ·
      refine ⟨131340023607557853450917381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350240062953487609202446349 131340023607557853450917381)
      ·
        refine ⟨24626254426417097522047009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131340023607557853450917381 24626254426417097522047009)
        ·
          refine ⟨18469690819812823141535257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24626254426417097522047009 18469690819812823141535257)
          ·
            refine ⟨13852268114859617356151443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18469690819812823141535257 13852268114859617356151443)
            ·
              refine ⟨20778402172289426034227165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13852268114859617356151443 20778402172289426034227165)
              ·
                refine ⟨7791900814608534762835187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20778402172289426034227165 7791900814608534762835187)
                ·
                  refine ⟨11687851221912802144252781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791900814608534762835187 11687851221912802144252781)
                  ·
                    refine ⟨4382944208217300804094793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11687851221912802144252781 4382944208217300804094793)
                    ·
                      refine ⟨3287208156162975603071095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4382944208217300804094793 3287208156162975603071095)
                      ·
                        rfl

theorem cell23_6401815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_6401815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401815 prefixEnd_6401815 := by exact prefixLift 6401815
  have htrace : WordTrace (prefixWord ++ tailWord_6401815) baseStart_6401815 baseEnd_6401815 := by
    simpa [prefixWord, tailWord_6401815, baseEnd_6401815] using wordTrace_append hprefix tailTrace_6401815
  have hstable : (prefixWord ++ tailWord_6401815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401815).length < 2 ^ (prefixWord ++ tailWord_6401815).sum := by decide
  have hdescent : baseEnd_6401815 < baseStart_6401815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401841 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6401841 : Nat := 118140960795 + 6401841 * 2 ^ 59
def prefixEnd_6401841 : Nat := 4983230072969 + 3 ^ 40 * 6401841 * 2
def baseEnd_6401841 : Nat := 3287221506659992501345975

theorem tailTrace_6401841 : CollatzResearch.WordTrace tailWord_6401841 prefixEnd_6401841 3287221506659992501345975 := by
  unfold tailWord_6401841
  simp only [CollatzResearch.WordTrace]
  refine ⟨233494323600230879242077377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155662882400153919494718251 233494323600230879242077377)
  ·
    refine ⟨175120742700173159431558033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233494323600230879242077377 175120742700173159431558033)
    ·
      refine ⟨131340557025129869573668525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175120742700173159431558033 131340557025129869573668525)
      ·
        refine ⟨49252708884423701090125697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131340557025129869573668525 49252708884423701090125697)
        ·
          refine ⟨36939531663317775817594273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49252708884423701090125697 36939531663317775817594273)
          ·
            refine ⟨27704648747488331863195705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36939531663317775817594273 27704648747488331863195705)
            ·
              refine ⟨20778486560616248897396779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27704648747488331863195705 20778486560616248897396779)
              ·
                refine ⟨31167729840924373346095169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20778486560616248897396779 31167729840924373346095169)
                ·
                  refine ⟨23375797380693280009571377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31167729840924373346095169 23375797380693280009571377)
                  ·
                    refine ⟨17531848035519960007178533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23375797380693280009571377 17531848035519960007178533)
                    ·
                      refine ⟨3287221506659992501345975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17531848035519960007178533 3287221506659992501345975)
                      ·
                        rfl

theorem cell23_6401841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6401841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401841 prefixEnd_6401841 := by exact prefixLift 6401841
  have htrace : WordTrace (prefixWord ++ tailWord_6401841) baseStart_6401841 baseEnd_6401841 := by
    simpa [prefixWord, tailWord_6401841, baseEnd_6401841] using wordTrace_append hprefix tailTrace_6401841
  have hstable : (prefixWord ++ tailWord_6401841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401841).length < 2 ^ (prefixWord ++ tailWord_6401841).sum := by decide
  have hdescent : baseEnd_6401841 < baseStart_6401841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401881 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_6401881 : Nat := 118140960795 + 6401881 * 2 ^ 59
def prefixEnd_6401881 : Nat := 4983230072969 + 3 ^ 40 * 6401881 * 2
def baseEnd_6401881 : Nat := 1095747348628724114948597

theorem tailTrace_6401881 : CollatzResearch.WordTrace tailWord_6401881 prefixEnd_6401881 1095747348628724114948597 := by
  unfold tailWord_6401881
  simp only [CollatzResearch.WordTrace]
  refine ⟨233495782520085966073533497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155663855013390644049022331 233495782520085966073533497)
  ·
    refine ⟨175121836890064474555150123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233495782520085966073533497 175121836890064474555150123)
    ·
      refine ⟨262682755335096711832725185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175121836890064474555150123 262682755335096711832725185)
      ·
        refine ⟨197012066501322533874543889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262682755335096711832725185 197012066501322533874543889)
        ·
          refine ⟨147759049875991900405907917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197012066501322533874543889 147759049875991900405907917)
          ·
            refine ⟨55409643703496962652215469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147759049875991900405907917 55409643703496962652215469)
            ·
              refine ⟨20778616388811360994580801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55409643703496962652215469 20778616388811360994580801)
              ·
                refine ⟨15583962291608520745935601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20778616388811360994580801 15583962291608520745935601)
                ·
                  refine ⟨11687971718706390559451701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15583962291608520745935601 11687971718706390559451701)
                  ·
                    refine ⟨1095747348628724114948597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11687971718706390559451701 1095747348628724114948597)
                    ·
                      rfl

theorem cell23_6401881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_6401881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401881 prefixEnd_6401881 := by exact prefixLift 6401881
  have htrace : WordTrace (prefixWord ++ tailWord_6401881) baseStart_6401881 baseEnd_6401881 := by
    simpa [prefixWord, tailWord_6401881, baseEnd_6401881] using wordTrace_append hprefix tailTrace_6401881
  have hstable : (prefixWord ++ tailWord_6401881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401881).length < 2 ^ (prefixWord ++ tailWord_6401881).sum := by decide
  have hdescent : baseEnd_6401881 < baseStart_6401881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401901 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6401901 : Nat := 118140960795 + 6401901 * 2 ^ 59
def prefixEnd_6401901 : Nat := 4983230072969 + 3 ^ 40 * 6401901 * 2
def baseEnd_6401901 : Nat := 3287252315499262266595699

theorem tailTrace_6401901 : CollatzResearch.WordTrace tailWord_6401901 prefixEnd_6401901 3287252315499262266595699 := by
  unfold tailWord_6401901
  simp only [CollatzResearch.WordTrace]
  refine ⟨233496511980013509489261557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155664341320009006326174371 233496511980013509489261557)
  ·
    refine ⟨21890297998126266514618271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233496511980013509489261557 21890297998126266514618271)
    ·
      refine ⟨32835446997189399771927407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21890297998126266514618271 32835446997189399771927407)
      ·
        refine ⟨49253170495784099657891111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32835446997189399771927407 49253170495784099657891111)
        ·
          refine ⟨73879755743676149486836667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49253170495784099657891111 73879755743676149486836667)
          ·
            refine ⟨110819633615514224230255001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73879755743676149486836667 110819633615514224230255001)
            ·
              refine ⟨83114725211635668172691251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110819633615514224230255001 83114725211635668172691251)
              ·
                refine ⟨124672087817453502259036877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83114725211635668172691251 124672087817453502259036877)
                ·
                  refine ⟨46752032931545063347138829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124672087817453502259036877 46752032931545063347138829)
                  ·
                    refine ⟨17532012349329398755177061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46752032931545063347138829 17532012349329398755177061)
                    ·
                      refine ⟨3287252315499262266595699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17532012349329398755177061 3287252315499262266595699)
                      ·
                        rfl

theorem cell23_6401901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6401901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401901 prefixEnd_6401901 := by exact prefixLift 6401901
  have htrace : WordTrace (prefixWord ++ tailWord_6401901) baseStart_6401901 baseEnd_6401901 := by
    simpa [prefixWord, tailWord_6401901, baseEnd_6401901] using wordTrace_append hprefix tailTrace_6401901
  have hstable : (prefixWord ++ tailWord_6401901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401901).length < 2 ^ (prefixWord ++ tailWord_6401901).sum := by decide
  have hdescent : baseEnd_6401901 < baseStart_6401901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401966 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6401966 : Nat := 118140960795 + 6401966 * 2 ^ 59
def prefixEnd_6401966 : Nat := 4983230072969 + 3 ^ 40 * 6401966 * 2
def baseEnd_6401966 : Nat := 1095761897247268170760967

theorem tailTrace_6401966 : CollatzResearch.WordTrace tailWord_6401966 prefixEnd_6401966 1095761897247268170760967 := by
  unfold tailWord_6401966
  simp only [CollatzResearch.WordTrace]
  refine ⟨29187360340597253198797219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155665921816518683726918501 29187360340597253198797219)
  ·
    refine ⟨43781040510895879798195829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29187360340597253198797219 43781040510895879798195829)
    ·
      refine ⟨4104472547896488731080859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43781040510895879798195829 4104472547896488731080859)
      ·
        refine ⟨6156708821844733096621289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104472547896488731080859 6156708821844733096621289)
        ·
          refine ⟨4617531616383549822465967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6156708821844733096621289 4617531616383549822465967)
          ·
            refine ⟨6926297424575324733698951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617531616383549822465967 6926297424575324733698951)
            ·
              refine ⟨10389446136862987100548427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926297424575324733698951 10389446136862987100548427)
              ·
                refine ⟨15584169205294480650822641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10389446136862987100548427 15584169205294480650822641)
                ·
                  refine ⟨11688126903970860488116981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15584169205294480650822641 11688126903970860488116981)
                  ·
                    refine ⟨1095761897247268170760967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11688126903970860488116981 1095761897247268170760967)
                    ·
                      rfl

theorem cell23_6401966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6401966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401966 prefixEnd_6401966 := by exact prefixLift 6401966
  have htrace : WordTrace (prefixWord ++ tailWord_6401966) baseStart_6401966 baseEnd_6401966 := by
    simpa [prefixWord, tailWord_6401966, baseEnd_6401966] using wordTrace_append hprefix tailTrace_6401966
  have hstable : (prefixWord ++ tailWord_6401966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401966).length < 2 ^ (prefixWord ++ tailWord_6401966).sum := by decide
  have hdescent : baseEnd_6401966 < baseStart_6401966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401971 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 3, 5]
def baseStart_6401971 : Nat := 118140960795 + 6401971 * 2 ^ 59
def prefixEnd_6401971 : Nat := 4983230072969 + 3 ^ 40 * 6401971 * 2
def baseEnd_6401971 : Nat := 1095762753048358997573459

theorem tailTrace_6401971 : CollatzResearch.WordTrace tailWord_6401971 prefixEnd_6401971 1095762753048358997573459 := by
  unfold tailWord_6401971
  simp only [CollatzResearch.WordTrace]
  refine ⟨233499065089759911444309767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155666043393173274296206511 233499065089759911444309767)
  ·
    refine ⟨350248597634639867166464651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233499065089759911444309767 350248597634639867166464651)
    ·
      refine ⟨525372896451959800749696977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350248597634639867166464651 525372896451959800749696977)
      ·
        refine ⟨394029672338969850562272733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525372896451959800749696977 394029672338969850562272733)
        ·
          refine ⟨147761127127113693960852275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394029672338969850562272733 147761127127113693960852275)
          ·
            refine ⟨221641690690670540941278413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147761127127113693960852275 221641690690670540941278413)
            ·
              refine ⟨83115634009001452852979405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221641690690670540941278413 83115634009001452852979405)
              ·
                refine ⟨31168362753375544819867277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83115634009001452852979405 31168362753375544819867277)
                ·
                  refine ⟨11688136032515829307450229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31168362753375544819867277 11688136032515829307450229)
                  ·
                    refine ⟨1095762753048358997573459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11688136032515829307450229 1095762753048358997573459)
                    ·
                      rfl

theorem cell23_6401971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 5].length) (baseStart_6401971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401971 prefixEnd_6401971 := by exact prefixLift 6401971
  have htrace : WordTrace (prefixWord ++ tailWord_6401971) baseStart_6401971 baseEnd_6401971 := by
    simpa [prefixWord, tailWord_6401971, baseEnd_6401971] using wordTrace_append hprefix tailTrace_6401971
  have hstable : (prefixWord ++ tailWord_6401971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401971).length < 2 ^ (prefixWord ++ tailWord_6401971).sum := by decide
  have hdescent : baseEnd_6401971 < baseStart_6401971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401972 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6401972 : Nat := 118140960795 + 6401972 * 2 ^ 59
def prefixEnd_6401972 : Nat := 4983230072969 + 3 ^ 40 * 6401972 * 2
def baseEnd_6401972 : Nat := 3287288772625731488807873

theorem tailTrace_6401972 : CollatzResearch.WordTrace tailWord_6401972 prefixEnd_6401972 3287288772625731488807873 := by
  unfold tailWord_6401972
  simp only [CollatzResearch.WordTrace]
  refine ⟨116749550781378144307548085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155666067708504192410064113 116749550781378144307548085)
  ·
    refine ⟨10945270385754201028832633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116749550781378144307548085 10945270385754201028832633)
    ·
      refine ⟨8208952789315650771624475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10945270385754201028832633 8208952789315650771624475)
      ·
        refine ⟨12313429183973476157436713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8208952789315650771624475 12313429183973476157436713)
        ·
          refine ⟨9235071887980107118077535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12313429183973476157436713 9235071887980107118077535)
          ·
            refine ⟨13852607831970160677116303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9235071887980107118077535 13852607831970160677116303)
            ·
              refine ⟨20778911747955241015674455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13852607831970160677116303 20778911747955241015674455)
              ·
                refine ⟨31168367621932861523511683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20778911747955241015674455 31168367621932861523511683)
                ·
                  refine ⟨46752551432899292285267525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31168367621932861523511683 46752551432899292285267525)
                  ·
                    refine ⟨8766103393668617303487661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46752551432899292285267525 8766103393668617303487661)
                    ·
                      refine ⟨3287288772625731488807873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8766103393668617303487661 3287288772625731488807873)
                      ·
                        rfl

theorem cell23_6401972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6401972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6401972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6401972 prefixEnd_6401972 := by exact prefixLift 6401972
  have htrace : WordTrace (prefixWord ++ tailWord_6401972) baseStart_6401972 baseEnd_6401972 := by
    simpa [prefixWord, tailWord_6401972, baseEnd_6401972] using wordTrace_append hprefix tailTrace_6401972
  have hstable : (prefixWord ++ tailWord_6401972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401972).length < 2 ^ (prefixWord ++ tailWord_6401972).sum := by decide
  have hdescent : baseEnd_6401972 < baseStart_6401972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402028 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_6402028 : Nat := 118140960795 + 6402028 * 2 ^ 59
def prefixEnd_6402028 : Nat := 4983230072969 + 3 ^ 40 * 6402028 * 2
def baseEnd_6402028 : Nat := 3287317527542383269707615

theorem tailTrace_6402028 : CollatzResearch.WordTrace tailWord_6402028 prefixEnd_6402028 3287317527542383269707615 := by
  unfold tailWord_6402028
  simp only [CollatzResearch.WordTrace]
  refine ⟨116750572025276705089567369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155667429367035606786089825 116750572025276705089567369)
  ·
    refine ⟨87562929018957528817175527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116750572025276705089567369 87562929018957528817175527)
    ·
      refine ⟨131344393528436293225763291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87562929018957528817175527 131344393528436293225763291)
      ·
        refine ⟨197016590292654439838644937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131344393528436293225763291 197016590292654439838644937)
        ·
          refine ⟨147762442719490829878983703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197016590292654439838644937 147762442719490829878983703)
          ·
            refine ⟨221643664079236244818475555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147762442719490829878983703 221643664079236244818475555)
            ·
              refine ⟨332465496118854367227713333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221643664079236244818475555 332465496118854367227713333)
              ·
                refine ⟨31168640261142596927598125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332465496118854367227713333 31168640261142596927598125)
                ·
                  refine ⟨11688240097928473847849297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31168640261142596927598125 11688240097928473847849297)
                  ·
                    refine ⟨8766180073446355385886973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11688240097928473847849297 8766180073446355385886973)
                    ·
                      refine ⟨3287317527542383269707615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8766180073446355385886973 3287317527542383269707615)
                      ·
                        rfl

theorem cell23_6402028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_6402028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402028 prefixEnd_6402028 := by exact prefixLift 6402028
  have htrace : WordTrace (prefixWord ++ tailWord_6402028) baseStart_6402028 baseEnd_6402028 := by
    simpa [prefixWord, tailWord_6402028, baseEnd_6402028] using wordTrace_append hprefix tailTrace_6402028
  have hstable : (prefixWord ++ tailWord_6402028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402028).length < 2 ^ (prefixWord ++ tailWord_6402028).sum := by decide
  have hdescent : baseEnd_6402028 < baseStart_6402028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402031 : List Nat := [1, 1, 2, 1, 4, 2, 3, 9]
def baseStart_6402031 : Nat := 118140960795 + 6402031 * 2 ^ 59
def prefixEnd_6402031 : Nat := 4983230072969 + 3 ^ 40 * 6402031 * 2
def baseEnd_6402031 : Nat := 121752558073494324369263

theorem tailTrace_6402031 : CollatzResearch.WordTrace tailWord_6402031 prefixEnd_6402031 121752558073494324369263 := by
  unfold tailWord_6402031
  simp only [CollatzResearch.WordTrace]
  refine ⟨233501253469542541691493947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155667502313028361127662631 233501253469542541691493947)
  ·
    refine ⟨350251880204313812537240921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233501253469542541691493947 350251880204313812537240921)
    ·
      refine ⟨262688910153235359402930691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350251880204313812537240921 262688910153235359402930691)
      ·
        refine ⟨394033365229853039104396037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262688910153235359402930691 394033365229853039104396037)
        ·
          refine ⟨73881255980597444832074257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394033365229853039104396037 73881255980597444832074257)
          ·
            refine ⟨55410941985448083624055693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73881255980597444832074257 55410941985448083624055693)
            ·
              refine ⟨20779103244543031359020885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55410941985448083624055693 20779103244543031359020885)
              ·
                refine ⟨121752558073494324369263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20779103244543031359020885 121752558073494324369263)
                ·
                  rfl

theorem cell23_6402031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 9].length) (baseStart_6402031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402031 prefixEnd_6402031 := by exact prefixLift 6402031
  have htrace : WordTrace (prefixWord ++ tailWord_6402031) baseStart_6402031 baseEnd_6402031 := by
    simpa [prefixWord, tailWord_6402031, baseEnd_6402031] using wordTrace_append hprefix tailTrace_6402031
  have hstable : (prefixWord ++ tailWord_6402031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402031).length < 2 ^ (prefixWord ++ tailWord_6402031).sum := by decide
  have hdescent : baseEnd_6402031 < baseStart_6402031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402045 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_6402045 : Nat := 118140960795 + 6402045 * 2 ^ 59
def prefixEnd_6402045 : Nat := 4983230072969 + 3 ^ 40 * 6402045 * 2
def baseEnd_6402045 : Nat := 3287326256713509703195037

theorem tailTrace_6402045 : CollatzResearch.WordTrace tailWord_6402045 prefixEnd_6402045 3287326256713509703195037 := by
  unfold tailWord_6402045
  simp only [CollatzResearch.WordTrace]
  refine ⟨233501764091491822082503589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155667842727661214721669059 233501764091491822082503589)
  ·
    refine ⟨43781580767154716640469423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233501764091491822082503589 43781580767154716640469423)
    ·
      refine ⟨65672371150732074960704135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43781580767154716640469423 65672371150732074960704135)
      ·
        refine ⟨98508556726098112441056203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65672371150732074960704135 98508556726098112441056203)
        ·
          refine ⟨147762835089147168661584305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98508556726098112441056203 147762835089147168661584305)
          ·
            refine ⟨110822126316860376496188229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147762835089147168661584305 110822126316860376496188229)
            ·
              refine ⟨20779148684411320593035293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110822126316860376496188229 20779148684411320593035293)
              ·
                refine ⟨7792180756654245222388235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20779148684411320593035293 7792180756654245222388235)
                ·
                  refine ⟨11688271134981367833582353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7792180756654245222388235 11688271134981367833582353)
                  ·
                    refine ⟨8766203351236025875186765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11688271134981367833582353 8766203351236025875186765)
                    ·
                      refine ⟨3287326256713509703195037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8766203351236025875186765 3287326256713509703195037)
                      ·
                        rfl

theorem cell23_6402045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_6402045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402045 prefixEnd_6402045 := by exact prefixLift 6402045
  have htrace : WordTrace (prefixWord ++ tailWord_6402045) baseStart_6402045 baseEnd_6402045 := by
    simpa [prefixWord, tailWord_6402045, baseEnd_6402045] using wordTrace_append hprefix tailTrace_6402045
  have hstable : (prefixWord ++ tailWord_6402045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402045).length < 2 ^ (prefixWord ++ tailWord_6402045).sum := by decide
  have hdescent : baseEnd_6402045 < baseStart_6402045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402069 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_6402069 : Nat := 118140960795 + 6402069 * 2 ^ 59
def prefixEnd_6402069 : Nat := 4983230072969 + 3 ^ 40 * 6402069 * 2
def baseEnd_6402069 : Nat := 1095779526749739203098309

theorem tailTrace_6402069 : CollatzResearch.WordTrace tailWord_6402069 prefixEnd_6402069 1095779526749739203098309 := by
  unfold tailWord_6402069
  simp only [CollatzResearch.WordTrace]
  refine ⟨233502639443404874181377261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155668426295603249454251507 233502639443404874181377261)
  ·
    refine ⟨87563489791276827818016473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233502639443404874181377261 87563489791276827818016473)
    ·
      refine ⟨65672617343457620863512355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87563489791276827818016473 65672617343457620863512355)
      ·
        refine ⟨98508926015186431295268533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65672617343457620863512355 98508926015186431295268533)
        ·
          refine ⟨9235211813923727933931425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98508926015186431295268533 9235211813923727933931425)
          ·
            refine ⟨6926408860442795950448569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9235211813923727933931425 6926408860442795950448569)
            ·
              refine ⟨5194806645332096962836427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926408860442795950448569 5194806645332096962836427)
              ·
                refine ⟨7792209967998145444254641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194806645332096962836427 7792209967998145444254641)
                ·
                  refine ⟨5844157475998609083190981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7792209967998145444254641 5844157475998609083190981)
                  ·
                    refine ⟨1095779526749739203098309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5844157475998609083190981 1095779526749739203098309)
                    ·
                      rfl

theorem cell23_6402069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_6402069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402069 prefixEnd_6402069 := by exact prefixLift 6402069
  have htrace : WordTrace (prefixWord ++ tailWord_6402069) baseStart_6402069 baseEnd_6402069 := by
    simpa [prefixWord, tailWord_6402069, baseEnd_6402069] using wordTrace_append hprefix tailTrace_6402069
  have hstable : (prefixWord ++ tailWord_6402069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402069).length < 2 ^ (prefixWord ++ tailWord_6402069).sum := by decide
  have hdescent : baseEnd_6402069 < baseStart_6402069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402091 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 8]
def baseStart_6402091 : Nat := 118140960795 + 6402091 * 2 ^ 59
def prefixEnd_6402091 : Nat := 4983230072969 + 3 ^ 40 * 6402091 * 2
def baseEnd_6402091 : Nat := 1095783292274538841073275

theorem tailTrace_6402091 : CollatzResearch.WordTrace tailWord_6402091 prefixEnd_6402091 1095783292274538841073275 := by
  unfold tailWord_6402091
  simp only [CollatzResearch.WordTrace]
  refine ⟨233503441849325171938678127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155668961232883447959118751 233503441849325171938678127)
  ·
    refine ⟨350255162773987757908017191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233503441849325171938678127 350255162773987757908017191)
    ·
      refine ⟨525382744160981636862025787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350255162773987757908017191 525382744160981636862025787)
      ·
        refine ⟨788074116241472455293038681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525382744160981636862025787 788074116241472455293038681)
        ·
          refine ⟨591055587181104341469779011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788074116241472455293038681 591055587181104341469779011)
          ·
            refine ⟨886583380771656512204668517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591055587181104341469779011 886583380771656512204668517)
            ·
              refine ⟨166234383894685596038375347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 886583380771656512204668517 166234383894685596038375347)
              ·
                refine ⟨249351575842028394057563021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166234383894685596038375347 249351575842028394057563021)
                ·
                  refine ⟨93506840940760647771586133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249351575842028394057563021 93506840940760647771586133)
                  ·
                    refine ⟨1095783292274538841073275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93506840940760647771586133 1095783292274538841073275)
                    ·
                      rfl

theorem cell23_6402091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_6402091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402091 prefixEnd_6402091 := by exact prefixLift 6402091
  have htrace : WordTrace (prefixWord ++ tailWord_6402091) baseStart_6402091 baseEnd_6402091 := by
    simpa [prefixWord, tailWord_6402091, baseEnd_6402091] using wordTrace_append hprefix tailTrace_6402091
  have hstable : (prefixWord ++ tailWord_6402091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402091).length < 2 ^ (prefixWord ++ tailWord_6402091).sum := by decide
  have hdescent : baseEnd_6402091 < baseStart_6402091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402108 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_6402108 : Nat := 118140960795 + 6402108 * 2 ^ 59
def prefixEnd_6402108 : Nat := 4983230072969 + 3 ^ 40 * 6402108 * 2
def baseEnd_6402108 : Nat := 1095786201998247652235749

theorem tailTrace_6402108 : CollatzResearch.WordTrace tailWord_6402108 prefixEnd_6402108 1095786201998247652235749 := by
  unfold tailWord_6402108
  simp only [CollatzResearch.WordTrace]
  refine ⟨116752030945131791921023489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155669374593509055894697985 116752030945131791921023489)
  ·
    refine ⟨87564023208848843940767617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116752030945131791921023489 87564023208848843940767617)
    ·
      refine ⟨65673017406636632955575713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87564023208848843940767617 65673017406636632955575713)
      ·
        refine ⟨49254763054977474716681785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65673017406636632955575713 49254763054977474716681785)
        ·
          refine ⟨36941072291233106037511339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49254763054977474716681785 36941072291233106037511339)
          ·
            refine ⟨55411608436849659056267009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36941072291233106037511339 55411608436849659056267009)
            ·
              refine ⟨41558706327637244292200257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55411608436849659056267009 41558706327637244292200257)
              ·
                refine ⟨31169029745727933219150193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41558706327637244292200257 31169029745727933219150193)
                ·
                  refine ⟨23376772309295949914362645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31169029745727933219150193 23376772309295949914362645)
                  ·
                    refine ⟨1095786201998247652235749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23376772309295949914362645 1095786201998247652235749)
                    ·
                      rfl

theorem cell23_6402108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_6402108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402108 prefixEnd_6402108 := by exact prefixLift 6402108
  have htrace : WordTrace (prefixWord ++ tailWord_6402108) baseStart_6402108 baseEnd_6402108 := by
    simpa [prefixWord, tailWord_6402108, baseEnd_6402108] using wordTrace_append hprefix tailTrace_6402108
  have hstable : (prefixWord ++ tailWord_6402108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402108).length < 2 ^ (prefixWord ++ tailWord_6402108).sum := by decide
  have hdescent : baseEnd_6402108 < baseStart_6402108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402110 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6402110 : Nat := 118140960795 + 6402110 * 2 ^ 59
def prefixEnd_6402110 : Nat := 4983230072969 + 3 ^ 40 * 6402110 * 2
def baseEnd_6402110 : Nat := 3287359632956051948882239

theorem tailTrace_6402110 : CollatzResearch.WordTrace tailWord_6402110 prefixEnd_6402110 3287359632956051948882239 := by
  unfold tailWord_6402110
  simp only [CollatzResearch.WordTrace]
  refine ⟨29188016854532042272952473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155669423224170892122413189 29188016854532042272952473)
  ·
    refine ⟨21891012640899031704714355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29188016854532042272952473 21891012640899031704714355)
    ·
      refine ⟨32836518961348547557071533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21891012640899031704714355 32836518961348547557071533)
      ·
        refine ⟨12313694610505705333901825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32836518961348547557071533 12313694610505705333901825)
        ·
          refine ⟨9235270957879279000426369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12313694610505705333901825 9235270957879279000426369)
          ·
            refine ⟨6926453218409459250319777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9235270957879279000426369 6926453218409459250319777)
            ·
              refine ⟨5194839913807094437739833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926453218409459250319777 5194839913807094437739833)
              ·
                refine ⟨3896129935355320828304875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194839913807094437739833 3896129935355320828304875)
                ·
                  refine ⟨5844194903032981242457313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896129935355320828304875 5844194903032981242457313)
                  ·
                    refine ⟨4383146177274735931842985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5844194903032981242457313 4383146177274735931842985)
                    ·
                      refine ⟨3287359632956051948882239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383146177274735931842985 3287359632956051948882239)
                      ·
                        rfl

theorem cell23_6402110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6402110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402110 prefixEnd_6402110 := by exact prefixLift 6402110
  have htrace : WordTrace (prefixWord ++ tailWord_6402110) baseStart_6402110 baseEnd_6402110 := by
    simpa [prefixWord, tailWord_6402110, baseEnd_6402110] using wordTrace_append hprefix tailTrace_6402110
  have hstable : (prefixWord ++ tailWord_6402110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402110).length < 2 ^ (prefixWord ++ tailWord_6402110).sum := by decide
  have hdescent : baseEnd_6402110 < baseStart_6402110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402125 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_6402125 : Nat := 118140960795 + 6402125 * 2 ^ 59
def prefixEnd_6402125 : Nat := 4983230072969 + 3 ^ 40 * 6402125 * 2
def baseEnd_6402125 : Nat := 1095789111721956463398223

theorem tailTrace_6402125 : CollatzResearch.WordTrace tailWord_6402125 prefixEnd_6402125 1095789111721956463398223 := by
  unfold tailWord_6402125
  simp only [CollatzResearch.WordTrace]
  refine ⟨233504681931201995745415829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155669787954134663830277219 233504681931201995745415829)
  ·
    refine ⟨10945531965525093550566367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 233504681931201995745415829 10945531965525093550566367)
    ·
      refine ⟨16418297948287640325849551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10945531965525093550566367 16418297948287640325849551)
      ·
        refine ⟨24627446922431460488774327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16418297948287640325849551 24627446922431460488774327)
        ·
          refine ⟨36941170383647190733161491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24627446922431460488774327 36941170383647190733161491)
          ·
            refine ⟨55411755575470786099742237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36941170383647190733161491 55411755575470786099742237)
            ·
              refine ⟨20779408340801544787403339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55411755575470786099742237 20779408340801544787403339)
              ·
                refine ⟨31169112511202317181105009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20779408340801544787403339 31169112511202317181105009)
                ·
                  refine ⟨23376834383401737885828757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31169112511202317181105009 23376834383401737885828757)
                  ·
                    refine ⟨1095789111721956463398223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23376834383401737885828757 1095789111721956463398223)
                    ·
                      rfl

theorem cell23_6402125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_6402125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402125 prefixEnd_6402125 := by exact prefixLift 6402125
  have htrace : WordTrace (prefixWord ++ tailWord_6402125) baseStart_6402125 baseEnd_6402125 := by
    simpa [prefixWord, tailWord_6402125, baseEnd_6402125] using wordTrace_append hprefix tailTrace_6402125
  have hstable : (prefixWord ++ tailWord_6402125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402125).length < 2 ^ (prefixWord ++ tailWord_6402125).sum := by decide
  have hdescent : baseEnd_6402125 < baseStart_6402125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402132 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_6402132 : Nat := 118140960795 + 6402132 * 2 ^ 59
def prefixEnd_6402132 : Nat := 4983230072969 + 3 ^ 40 * 6402132 * 2
def baseEnd_6402132 : Nat := 3287370929530450862807137

theorem tailTrace_6402132 : CollatzResearch.WordTrace tailWord_6402132 prefixEnd_6402132 3287370929530450862807137 := by
  unfold tailWord_6402132
  simp only [CollatzResearch.WordTrace]
  refine ⟨116752468621088317970460325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155669958161451090627280433 116752468621088317970460325)
  ·
    refine ⟨21891087866454059619461311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116752468621088317970460325 21891087866454059619461311)
    ·
      refine ⟨32836631799681089429191967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21891087866454059619461311 32836631799681089429191967)
      ·
        refine ⟨49254947699521634143787951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32836631799681089429191967 49254947699521634143787951)
        ·
          refine ⟨73882421549282451215681927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49254947699521634143787951 73882421549282451215681927)
          ·
            refine ⟨110823632323923676823522891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73882421549282451215681927 110823632323923676823522891)
            ·
              refine ⟨166235448485885515235284337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110823632323923676823522891 166235448485885515235284337)
              ·
                refine ⟨124676586364414136426463253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166235448485885515235284337 124676586364414136426463253)
                ·
                  refine ⟨5844214985831912644990465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124676586364414136426463253 5844214985831912644990465)
                  ·
                    refine ⟨4383161239373934483742849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5844214985831912644990465 4383161239373934483742849)
                    ·
                      refine ⟨3287370929530450862807137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383161239373934483742849 3287370929530450862807137)
                      ·
                        rfl

theorem cell23_6402132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_6402132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402132 prefixEnd_6402132 := by exact prefixLift 6402132
  have htrace : WordTrace (prefixWord ++ tailWord_6402132) baseStart_6402132 baseEnd_6402132 := by
    simpa [prefixWord, tailWord_6402132, baseEnd_6402132] using wordTrace_append hprefix tailTrace_6402132
  have hstable : (prefixWord ++ tailWord_6402132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402132).length < 2 ^ (prefixWord ++ tailWord_6402132).sum := by decide
  have hdescent : baseEnd_6402132 < baseStart_6402132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402138 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_6402138 : Nat := 118140960795 + 6402138 * 2 ^ 59
def prefixEnd_6402138 : Nat := 4983230072969 + 3 ^ 40 * 6402138 * 2
def baseEnd_6402138 : Nat := 365263778934930871036901

theorem tailTrace_6402138 : CollatzResearch.WordTrace tailWord_6402138 prefixEnd_6402138 365263778934930871036901 := by
  unfold tailWord_6402138
  simp only [CollatzResearch.WordTrace]
  refine ⟨58376289020038724741409767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155670104053436599310426045 58376289020038724741409767)
  ·
    refine ⟨87564433530058087112114651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58376289020038724741409767 87564433530058087112114651)
    ·
      refine ⟨131346650295087130668171977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87564433530058087112114651 131346650295087130668171977)
      ·
        refine ⟨98509987721315348001128983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131346650295087130668171977 98509987721315348001128983)
        ·
          refine ⟨147764981581973022001693475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98509987721315348001128983 147764981581973022001693475)
          ·
            refine ⟨221647472372959533002540213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147764981581973022001693475 221647472372959533002540213)
            ·
              refine ⟨20779450534964956218988145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221647472372959533002540213 20779450534964956218988145)
              ·
                refine ⟨15584587901223717164241109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20779450534964956218988145 15584587901223717164241109)
                ·
                  refine ⟨365263778934930871036901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15584587901223717164241109 365263778934930871036901)
                  ·
                    rfl

theorem cell23_6402138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_6402138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402138 prefixEnd_6402138 := by exact prefixLift 6402138
  have htrace : WordTrace (prefixWord ++ tailWord_6402138) baseStart_6402138 baseEnd_6402138 := by
    simpa [prefixWord, tailWord_6402138, baseEnd_6402138] using wordTrace_append hprefix tailTrace_6402138
  have hstable : (prefixWord ++ tailWord_6402138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402138).length < 2 ^ (prefixWord ++ tailWord_6402138).sum := by decide
  have hdescent : baseEnd_6402138 < baseStart_6402138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402166 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6402166 : Nat := 118140960795 + 6402166 * 2 ^ 59
def prefixEnd_6402166 : Nat := 4983230072969 + 3 ^ 40 * 6402166 * 2
def baseEnd_6402166 : Nat := 3287388387872703729781981

theorem tailTrace_6402166 : CollatzResearch.WordTrace tailWord_6402166 prefixEnd_6402166 3287388387872703729781981 := by
  unfold tailWord_6402166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14594136082753341234228647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155670784882702306498438901 14594136082753341234228647)
  ·
    refine ⟨21891204124130011851342971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14594136082753341234228647 21891204124130011851342971)
    ·
      refine ⟨32836806186195017777014457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21891204124130011851342971 32836806186195017777014457)
      ·
        refine ⟨24627604639646263332760843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32836806186195017777014457 24627604639646263332760843)
        ·
          refine ⟨36941406959469394999141265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24627604639646263332760843 36941406959469394999141265)
          ·
            refine ⟨27706055219602046249355949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36941406959469394999141265 27706055219602046249355949)
            ·
              refine ⟨10389770707350767343508481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27706055219602046249355949 10389770707350767343508481)
              ·
                refine ⟨7792328030513075507631361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10389770707350767343508481 7792328030513075507631361)
                ·
                  refine ⟨5844246022884806630723521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7792328030513075507631361 5844246022884806630723521)
                  ·
                    refine ⟨4383184517163604973042641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5844246022884806630723521 4383184517163604973042641)
                    ·
                      refine ⟨3287388387872703729781981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383184517163604973042641 3287388387872703729781981)
                      ·
                        rfl

theorem cell23_6402166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6402166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402166 prefixEnd_6402166 := by exact prefixLift 6402166
  have htrace : WordTrace (prefixWord ++ tailWord_6402166) baseStart_6402166 baseEnd_6402166 := by
    simpa [prefixWord, tailWord_6402166, baseEnd_6402166] using wordTrace_append hprefix tailTrace_6402166
  have hstable : (prefixWord ++ tailWord_6402166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402166).length < 2 ^ (prefixWord ++ tailWord_6402166).sum := by decide
  have hdescent : baseEnd_6402166 < baseStart_6402166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402168 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_6402168 : Nat := 118140960795 + 6402168 * 2 ^ 59
def prefixEnd_6402168 : Nat := 4983230072969 + 3 ^ 40 * 6402168 * 2
def baseEnd_6402168 : Nat := 1095796471611337573985657

theorem tailTrace_6402168 : CollatzResearch.WordTrace tailWord_6402168 prefixEnd_6402168 1095796471611337573985657 := by
  unfold tailWord_6402168
  simp only [CollatzResearch.WordTrace]
  refine ⟨116753125135023107044615579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155670833513364142726154105 116753125135023107044615579)
  ·
    refine ⟨175129687702534660566923369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116753125135023107044615579 175129687702534660566923369)
    ·
      refine ⟨131347265776900995425192527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175129687702534660566923369 131347265776900995425192527)
      ·
        refine ⟨197020898665351493137788791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131347265776900995425192527 197020898665351493137788791)
        ·
          refine ⟨295531347998027239706683187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197020898665351493137788791 295531347998027239706683187)
          ·
            refine ⟨443297021997040859560024781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295531347998027239706683187 443297021997040859560024781)
            ·
              refine ⟨166236383248890322335009293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 443297021997040859560024781 166236383248890322335009293)
              ·
                refine ⟨62338643718333870875628485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166236383248890322335009293 62338643718333870875628485)
                ·
                  refine ⟨11688495697187600789180341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62338643718333870875628485 11688495697187600789180341)
                  ·
                    refine ⟨1095796471611337573985657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11688495697187600789180341 1095796471611337573985657)
                    ·
                      rfl

theorem cell23_6402168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_6402168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402168 prefixEnd_6402168 := by exact prefixLift 6402168
  have htrace : WordTrace (prefixWord ++ tailWord_6402168) baseStart_6402168 baseEnd_6402168 := by
    simpa [prefixWord, tailWord_6402168, baseEnd_6402168] using wordTrace_append hprefix tailTrace_6402168
  have hstable : (prefixWord ++ tailWord_6402168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402168).length < 2 ^ (prefixWord ++ tailWord_6402168).sum := by decide
  have hdescent : baseEnd_6402168 < baseStart_6402168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402205 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_6402205 : Nat := 118140960795 + 6402205 * 2 ^ 59
def prefixEnd_6402205 : Nat := 4983230072969 + 3 ^ 40 * 6402205 * 2
def baseEnd_6402205 : Nat := 3287408413618229077194301

theorem tailTrace_6402205 : CollatzResearch.WordTrace tailWord_6402205 prefixEnd_6402205 3287408413618229077194301 := by
  unfold tailWord_6402205
  simp only [CollatzResearch.WordTrace]
  refine ⟨233507599770912169408328069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155671733180608112938885379 233507599770912169408328069)
  ·
    refine ⟨43782674957046031764061513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233507599770912169408328069 43782674957046031764061513)
    ·
      refine ⟨32837006217784523823046135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43782674957046031764061513 32837006217784523823046135)
      ·
        refine ⟨49255509326676785734569203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32837006217784523823046135 49255509326676785734569203)
        ·
          refine ⟨73883263990015178601853805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49255509326676785734569203 73883263990015178601853805)
          ·
            refine ⟨27706223996255691975695177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73883263990015178601853805 27706223996255691975695177)
            ·
              refine ⟨20779667997191768981771383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27706223996255691975695177 20779667997191768981771383)
              ·
                refine ⟨31169501995787653472657075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20779667997191768981771383 31169501995787653472657075)
                ·
                  refine ⟨46754252993681480208985613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31169501995787653472657075 46754252993681480208985613)
                  ·
                    refine ⟨17532844872630555078369605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46754252993681480208985613 17532844872630555078369605)
                    ·
                      refine ⟨3287408413618229077194301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17532844872630555078369605 3287408413618229077194301)
                      ·
                        rfl

theorem cell23_6402205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_6402205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402205 prefixEnd_6402205 := by exact prefixLift 6402205
  have htrace : WordTrace (prefixWord ++ tailWord_6402205) baseStart_6402205 baseEnd_6402205 := by
    simpa [prefixWord, tailWord_6402205, baseEnd_6402205] using wordTrace_append hprefix tailTrace_6402205
  have hstable : (prefixWord ++ tailWord_6402205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402205).length < 2 ^ (prefixWord ++ tailWord_6402205).sum := by decide
  have hdescent : baseEnd_6402205 < baseStart_6402205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402206 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_6402206 : Nat := 118140960795 + 6402206 * 2 ^ 59
def prefixEnd_6402206 : Nat := 4983230072969 + 3 ^ 40 * 6402206 * 2
def baseEnd_6402206 : Nat := 365267658566542619253533

theorem tailTrace_6402206 : CollatzResearch.WordTrace tailWord_6402206 prefixEnd_6402206 365267658566542619253533 := by
  unfold tailWord_6402206
  simp only [CollatzResearch.WordTrace]
  refine ⟨29188454530488568322389309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155671757495939031052742981 29188454530488568322389309)
  ·
    refine ⟨10945670448933213120895991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29188454530488568322389309 10945670448933213120895991)
    ·
      refine ⟨16418505673399819681343987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10945670448933213120895991 16418505673399819681343987)
      ·
        refine ⟨24627758510099729522015981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16418505673399819681343987 24627758510099729522015981)
        ·
          refine ⟨9235409441287398570755993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24627758510099729522015981 9235409441287398570755993)
          ·
            refine ⟨6926557080965548928066995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9235409441287398570755993 6926557080965548928066995)
            ·
              refine ⟨10389835621448323392100493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926557080965548928066995 10389835621448323392100493)
              ·
                refine ⟨3896188358043121272037685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10389835621448323392100493 3896188358043121272037685)
                ·
                  refine ⟨365267658566542619253533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896188358043121272037685 365267658566542619253533)
                  ·
                    rfl

theorem cell23_6402206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_6402206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402206 prefixEnd_6402206 := by exact prefixLift 6402206
  have htrace : WordTrace (prefixWord ++ tailWord_6402206) baseStart_6402206 baseEnd_6402206 := by
    simpa [prefixWord, tailWord_6402206, baseEnd_6402206] using wordTrace_append hprefix tailTrace_6402206
  have hstable : (prefixWord ++ tailWord_6402206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402206).length < 2 ^ (prefixWord ++ tailWord_6402206).sum := by decide
  have hdescent : baseEnd_6402206 < baseStart_6402206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402306 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_6402306 : Nat := 118140960795 + 6402306 * 2 ^ 59
def prefixEnd_6402306 : Nat := 4983230072969 + 3 ^ 40 * 6402306 * 2
def baseEnd_6402306 : Nat := 3287460275164333182031337

theorem tailTrace_6402306 : CollatzResearch.WordTrace tailWord_6402306 prefixEnd_6402306 3287460275164333182031337 := by
  unfold tailWord_6402306
  simp only [CollatzResearch.WordTrace]
  refine ⟨58377820885886565914438693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155674189029030842438503181 58377820885886565914438693)
  ·
    refine ⟨10945841416103731108957255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58377820885886565914438693 10945841416103731108957255)
    ·
      refine ⟨16418762124155596663435883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10945841416103731108957255 16418762124155596663435883)
      ·
        refine ⟨24628143186233394995153825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16418762124155596663435883 24628143186233394995153825)
        ·
          refine ⟨18471107389675046246365369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24628143186233394995153825 18471107389675046246365369)
          ·
            refine ⟨13853330542256284684774027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18471107389675046246365369 13853330542256284684774027)
            ·
              refine ⟨20779995813384427027161041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13853330542256284684774027 20779995813384427027161041)
              ·
                refine ⟨15584996860038320270370781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20779995813384427027161041 15584996860038320270370781)
                ·
                  refine ⟨5844373822514370101389043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15584996860038320270370781 5844373822514370101389043)
                  ·
                    refine ⟨8766560733771555152083565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5844373822514370101389043 8766560733771555152083565)
                    ·
                      refine ⟨3287460275164333182031337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8766560733771555152083565 3287460275164333182031337)
                      ·
                        rfl

theorem cell23_6402306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_6402306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402306 prefixEnd_6402306 := by exact prefixLift 6402306
  have htrace : WordTrace (prefixWord ++ tailWord_6402306) baseStart_6402306 baseEnd_6402306 := by
    simpa [prefixWord, tailWord_6402306, baseEnd_6402306] using wordTrace_append hprefix tailTrace_6402306
  have hstable : (prefixWord ++ tailWord_6402306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402306).length < 2 ^ (prefixWord ++ tailWord_6402306).sum := by decide
  have hdescent : baseEnd_6402306 < baseStart_6402306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402312 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_6402312 : Nat := 118140960795 + 6402312 * 2 ^ 59
def prefixEnd_6402312 : Nat := 4983230072969 + 3 ^ 40 * 6402312 * 2
def baseEnd_6402312 : Nat := 3287463356048260158556309

theorem tailTrace_6402312 : CollatzResearch.WordTrace tailWord_6402312 prefixEnd_6402312 3287463356048260158556309 := by
  unfold tailWord_6402312
  simp only [CollatzResearch.WordTrace]
  refine ⟨116755751190762263341236595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155674334921016351121648793 116755751190762263341236595)
  ·
    refine ⟨175133626786143395011854893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116755751190762263341236595 175133626786143395011854893)
    ·
      refine ⟨65675110044803773129445585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175133626786143395011854893 65675110044803773129445585)
      ·
        refine ⟨49256332533602829847084189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65675110044803773129445585 49256332533602829847084189)
        ·
          refine ⟨18471124700101061192656571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49256332533602829847084189 18471124700101061192656571)
          ·
            refine ⟨27706687050151591788984857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18471124700101061192656571 27706687050151591788984857)
            ·
              refine ⟨20780015287613693841738643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27706687050151591788984857 20780015287613693841738643)
              ·
                refine ⟨31170022931420540762607965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20780015287613693841738643 31170022931420540762607965)
                ·
                  refine ⟨11688758599282702785977987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31170022931420540762607965 11688758599282702785977987)
                  ·
                    refine ⟨17533137898924054178966981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11688758599282702785977987 17533137898924054178966981)
                    ·
                      refine ⟨3287463356048260158556309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17533137898924054178966981 3287463356048260158556309)
                      ·
                        rfl

theorem cell23_6402312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_6402312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402312 prefixEnd_6402312 := by exact prefixLift 6402312
  have htrace : WordTrace (prefixWord ++ tailWord_6402312) baseStart_6402312 baseEnd_6402312 := by
    simpa [prefixWord, tailWord_6402312, baseEnd_6402312] using wordTrace_append hprefix tailTrace_6402312
  have hstable : (prefixWord ++ tailWord_6402312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402312).length < 2 ^ (prefixWord ++ tailWord_6402312).sum := by decide
  have hdescent : baseEnd_6402312 < baseStart_6402312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402335 : List Nat := [1, 1, 2, 4, 3, 2, 10]
def baseStart_6402335 : Nat := 118140960795 + 6402335 * 2 ^ 59
def prefixEnd_6402335 : Nat := 4983230072969 + 3 ^ 40 * 6402335 * 2
def baseEnd_6402335 : Nat := 40586113161769303315663

theorem tailTrace_6402335 : CollatzResearch.WordTrace tailWord_6402335 prefixEnd_6402335 40586113161769303315663 := by
  unfold tailWord_6402335
  simp only [CollatzResearch.WordTrace]
  refine ⟨233512341260441201610560459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155674894173627467740373639 233512341260441201610560459)
  ·
    refine ⟨350268511890661802415840689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233512341260441201610560459 350268511890661802415840689)
    ·
      refine ⟨262701383917996351811880517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350268511890661802415840689 262701383917996351811880517)
      ·
        refine ⟨49256509484624315964727597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262701383917996351811880517 49256509484624315964727597)
        ·
          refine ⟨18471191056734118486772849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49256509484624315964727597 18471191056734118486772849)
          ·
            refine ⟨13853393292550588865079637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18471191056734118486772849 13853393292550588865079637)
            ·
              refine ⟨40586113161769303315663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13853393292550588865079637 40586113161769303315663)
              ·
                rfl

theorem cell23_6402335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 10].length) (baseStart_6402335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402335 prefixEnd_6402335 := by exact prefixLift 6402335
  have htrace : WordTrace (prefixWord ++ tailWord_6402335) baseStart_6402335 baseEnd_6402335 := by
    simpa [prefixWord, tailWord_6402335, baseEnd_6402335] using wordTrace_append hprefix tailTrace_6402335
  have hstable : (prefixWord ++ tailWord_6402335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402335).length < 2 ^ (prefixWord ++ tailWord_6402335).sum := by decide
  have hdescent : baseEnd_6402335 < baseStart_6402335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402366 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_6402366 : Nat := 118140960795 + 6402366 * 2 ^ 59
def prefixEnd_6402366 : Nat := 4983230072969 + 3 ^ 40 * 6402366 * 2
def baseEnd_6402366 : Nat := 3287491084003602947281061

theorem tailTrace_6402366 : CollatzResearch.WordTrace tailWord_6402366 prefixEnd_6402366 3287491084003602947281061 := by
  unfold tailWord_6402366
  simp only [CollatzResearch.WordTrace]
  refine ⟨29189183990416111738117369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155675647948885929269959301 29189183990416111738117369)
  ·
    refine ⟨21891887992812083803588027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29189183990416111738117369 21891887992812083803588027)
    ·
      refine ⟨32837831989218125705382041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21891887992812083803588027 32837831989218125705382041)
      ·
        refine ⟨24628373991913594279036531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32837831989218125705382041 24628373991913594279036531)
        ·
          refine ⟨36942560987870391418554797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24628373991913594279036531 36942560987870391418554797)
          ·
            refine ⟨13853460370451396781958049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36942560987870391418554797 13853460370451396781958049)
            ·
              refine ⟨10390095277838547586468537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13853460370451396781958049 10390095277838547586468537)
              ·
                refine ⟨7792571458378910689851403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10390095277838547586468537 7792571458378910689851403)
                ·
                  refine ⟨11688857187568366034777105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7792571458378910689851403 11688857187568366034777105)
                  ·
                    refine ⟨8766642890676274526082829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11688857187568366034777105 8766642890676274526082829)
                    ·
                      refine ⟨3287491084003602947281061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8766642890676274526082829 3287491084003602947281061)
                      ·
                        rfl

theorem cell23_6402366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_6402366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402366 prefixEnd_6402366 := by exact prefixLift 6402366
  have htrace : WordTrace (prefixWord ++ tailWord_6402366) baseStart_6402366 baseEnd_6402366 := by
    simpa [prefixWord, tailWord_6402366, baseEnd_6402366] using wordTrace_append hprefix tailTrace_6402366
  have hstable : (prefixWord ++ tailWord_6402366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402366).length < 2 ^ (prefixWord ++ tailWord_6402366).sum := by decide
  have hdescent : baseEnd_6402366 < baseStart_6402366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402375 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_6402375 : Nat := 118140960795 + 6402375 * 2 ^ 59
def prefixEnd_6402375 : Nat := 4983230072969 + 3 ^ 40 * 6402375 * 2
def baseEnd_6402375 : Nat := 3287495705329493412068519

theorem tailTrace_6402375 : CollatzResearch.WordTrace tailWord_6402375 prefixEnd_6402375 3287495705329493412068519 := by
  unfold tailWord_6402375
  simp only [CollatzResearch.WordTrace]
  refine ⟨233513800180296288442016579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155675866786864192294677719 233513800180296288442016579)
  ·
    refine ⟨350270700270444432663024869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233513800180296288442016579 350270700270444432663024869)
    ·
      refine ⟨65675756300708331124317163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350270700270444432663024869 65675756300708331124317163)
      ·
        refine ⟨98513634451062496686475745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65675756300708331124317163 98513634451062496686475745)
        ·
          refine ⟨73885225838296872514856809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98513634451062496686475745 73885225838296872514856809)
          ·
            refine ⟨55413919378722654386142607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73885225838296872514856809 55413919378722654386142607)
            ·
              refine ⟨83120879068083981579213911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55413919378722654386142607 83120879068083981579213911)
              ·
                refine ⟨124681318602125972368820867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83120879068083981579213911 124681318602125972368820867)
                ·
                  refine ⟨187021977903188958553231301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124681318602125972368820867 187021977903188958553231301)
                  ·
                    refine ⟨35066620856847929728730869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187021977903188958553231301 35066620856847929728730869)
                    ·
                      refine ⟨3287495705329493412068519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35066620856847929728730869 3287495705329493412068519)
                      ·
                        rfl

theorem cell23_6402375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_6402375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402375 prefixEnd_6402375 := by exact prefixLift 6402375
  have htrace : WordTrace (prefixWord ++ tailWord_6402375) baseStart_6402375 baseEnd_6402375 := by
    simpa [prefixWord, tailWord_6402375, baseEnd_6402375] using wordTrace_append hprefix tailTrace_6402375
  have hstable : (prefixWord ++ tailWord_6402375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402375).length < 2 ^ (prefixWord ++ tailWord_6402375).sum := by decide
  have hdescent : baseEnd_6402375 < baseStart_6402375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402425 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 9]
def baseStart_6402425 : Nat := 118140960795 + 6402425 * 2 ^ 59
def prefixEnd_6402425 : Nat := 4983230072969 + 3 ^ 40 * 6402425 * 2
def baseEnd_6402425 : Nat := 365280153262468690715921

theorem tailTrace_6402425 : CollatzResearch.WordTrace tailWord_6402425 prefixEnd_6402425 365280153262468690715921 := by
  unfold tailWord_6402425
  simp only [CollatzResearch.WordTrace]
  refine ⟨233515623830115146981336729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155677082553410097987557819 233515623830115146981336729)
  ·
    refine ⟨175136717872586360236002547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233515623830115146981336729 175136717872586360236002547)
    ·
      refine ⟨262705076808879540354003821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175136717872586360236002547 262705076808879540354003821)
      ·
        refine ⟨98514403803329827632751433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262705076808879540354003821 98514403803329827632751433)
        ·
          refine ⟨73885802852497370724563575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98514403803329827632751433 73885802852497370724563575)
          ·
            refine ⟨110828704278746056086845363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73885802852497370724563575 110828704278746056086845363)
            ·
              refine ⟨166243056418119084130268045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110828704278746056086845363 166243056418119084130268045)
              ·
                refine ⟨62341146156794656548850517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166243056418119084130268045 62341146156794656548850517)
                ·
                  refine ⟨365280153262468690715921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62341146156794656548850517 365280153262468690715921)
                  ·
                    rfl

theorem cell23_6402425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_6402425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402425 prefixEnd_6402425 := by exact prefixLift 6402425
  have htrace : WordTrace (prefixWord ++ tailWord_6402425) baseStart_6402425 baseEnd_6402425 := by
    simpa [prefixWord, tailWord_6402425, baseEnd_6402425] using wordTrace_append hprefix tailTrace_6402425
  have hstable : (prefixWord ++ tailWord_6402425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402425).length < 2 ^ (prefixWord ++ tailWord_6402425).sum := by decide
  have hdescent : baseEnd_6402425 < baseStart_6402425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402475 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_6402475 : Nat := 118140960795 + 6402475 * 2 ^ 59
def prefixEnd_6402475 : Nat := 4983230072969 + 3 ^ 40 * 6402475 * 2
def baseEnd_6402475 : Nat := 3287547053394943020818059

theorem tailTrace_6402475 : CollatzResearch.WordTrace tailWord_6402475 prefixEnd_6402475 3287547053394943020818059 := by
  unfold tailWord_6402475
  simp only [CollatzResearch.WordTrace]
  refine ⟨233517447479934005520656879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155678298319956003680437919 233517447479934005520656879)
  ·
    refine ⟨350276171219901008280985319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233517447479934005520656879 350276171219901008280985319)
    ·
      refine ⟨525414256829851512421477979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350276171219901008280985319 525414256829851512421477979)
      ·
        refine ⟨788121385244777268632216969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525414256829851512421477979 788121385244777268632216969)
        ·
          refine ⟨591091038933582951474162727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788121385244777268632216969 591091038933582951474162727)
          ·
            refine ⟨886636558400374427211244091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591091038933582951474162727 886636558400374427211244091)
            ·
              refine ⟨1329954837600561640816866137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886636558400374427211244091 1329954837600561640816866137)
              ·
                refine ⟨997466128200421230612649603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1329954837600561640816866137 997466128200421230612649603)
                ·
                  refine ⟨1496199192300631845918974405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997466128200421230612649603 1496199192300631845918974405)
                  ·
                    refine ⟨280537348556368471109807701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1496199192300631845918974405 280537348556368471109807701)
                    ·
                      refine ⟨3287547053394943020818059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 280537348556368471109807701 3287547053394943020818059)
                      ·
                        rfl

theorem cell23_6402475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_6402475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402475 prefixEnd_6402475 := by exact prefixLift 6402475
  have htrace : WordTrace (prefixWord ++ tailWord_6402475) baseStart_6402475 baseEnd_6402475 := by
    simpa [prefixWord, tailWord_6402475, baseEnd_6402475] using wordTrace_append hprefix tailTrace_6402475
  have hstable : (prefixWord ++ tailWord_6402475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402475).length < 2 ^ (prefixWord ++ tailWord_6402475).sum := by decide
  have hdescent : baseEnd_6402475 < baseStart_6402475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402489 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 2, 5]
def baseStart_6402489 : Nat := 118140960795 + 6402489 * 2 ^ 59
def prefixEnd_6402489 : Nat := 4983230072969 + 3 ^ 40 * 6402489 * 2
def baseEnd_6402489 : Nat := 1095851414041368655347665

theorem tailTrace_6402489 : CollatzResearch.WordTrace tailWord_6402489 prefixEnd_6402489 1095851414041368655347665 := by
  unfold tailWord_6402489
  simp only [CollatzResearch.WordTrace]
  refine ⟨233517958101883285911666521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155678638734588857274444347 233517958101883285911666521)
  ·
    refine ⟨175138468576412464433749891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233517958101883285911666521 175138468576412464433749891)
    ·
      refine ⟨262707702864618696650624837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175138468576412464433749891 262707702864618696650624837)
      ·
        refine ⟨49257694287116005621992157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262707702864618696650624837 49257694287116005621992157)
        ·
          refine ⟨18471635357668502108247059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49257694287116005621992157 18471635357668502108247059)
          ·
            refine ⟨27707453036502753162370589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18471635357668502108247059 27707453036502753162370589)
            ·
              refine ⟨10390294888688532435888971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27707453036502753162370589 10390294888688532435888971)
              ·
                refine ⟨15585442333032798653833457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10390294888688532435888971 15585442333032798653833457)
                ·
                  refine ⟨11689081749774598990375093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15585442333032798653833457 11689081749774598990375093)
                  ·
                    refine ⟨1095851414041368655347665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11689081749774598990375093 1095851414041368655347665)
                    ·
                      rfl

theorem cell23_6402489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_6402489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402489 prefixEnd_6402489 := by exact prefixLift 6402489
  have htrace : WordTrace (prefixWord ++ tailWord_6402489) baseStart_6402489 baseEnd_6402489 := by
    simpa [prefixWord, tailWord_6402489, baseEnd_6402489] using wordTrace_append hprefix tailTrace_6402489
  have hstable : (prefixWord ++ tailWord_6402489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402489).length < 2 ^ (prefixWord ++ tailWord_6402489).sum := by decide
  have hdescent : baseEnd_6402489 < baseStart_6402489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402512 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_6402512 : Nat := 118140960795 + 6402512 * 2 ^ 59
def prefixEnd_6402512 : Nat := 4983230072969 + 3 ^ 40 * 6402512 * 2
def baseEnd_6402512 : Nat := 3287566052179159376055389

theorem tailTrace_6402512 : CollatzResearch.WordTrace tailWord_6402512 prefixEnd_6402512 3287566052179159376055389 := by
  unfold tailWord_6402512
  simp only [CollatzResearch.WordTrace]
  refine ⟨116759398490399980419876895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155679197987199973893169193 116759398490399980419876895)
  ·
    refine ⟨175139097735599970629815343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116759398490399980419876895 175139097735599970629815343)
    ·
      refine ⟨262708646603399955944723015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175139097735599970629815343 262708646603399955944723015)
      ·
        refine ⟨394062969905099933917084523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262708646603399955944723015 394062969905099933917084523)
        ·
          refine ⟨591094454857649900875626785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394062969905099933917084523 591094454857649900875626785)
          ·
            refine ⟨443320841143237425656720089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591094454857649900875626785 443320841143237425656720089)
            ·
              refine ⟨332490630857428069242540067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443320841143237425656720089 332490630857428069242540067)
              ·
                refine ⟨498735946286142103863810101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332490630857428069242540067 498735946286142103863810101)
                ·
                  refine ⟨46756494964325822237232197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498735946286142103863810101 46756494964325822237232197)
                  ·
                    refine ⟨8766842805811091669481037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46756494964325822237232197 8766842805811091669481037)
                    ·
                      refine ⟨3287566052179159376055389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8766842805811091669481037 3287566052179159376055389)
                      ·
                        rfl

theorem cell23_6402512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_6402512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402512 prefixEnd_6402512 := by exact prefixLift 6402512
  have htrace : WordTrace (prefixWord ++ tailWord_6402512) baseStart_6402512 baseEnd_6402512 := by
    simpa [prefixWord, tailWord_6402512, baseEnd_6402512] using wordTrace_append hprefix tailTrace_6402512
  have hstable : (prefixWord ++ tailWord_6402512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402512).length < 2 ^ (prefixWord ++ tailWord_6402512).sum := by decide
  have hdescent : baseEnd_6402512 < baseStart_6402512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402522 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_6402522 : Nat := 118140960795 + 6402522 * 2 ^ 59
def prefixEnd_6402522 : Nat := 4983230072969 + 3 ^ 40 * 6402522 * 2
def baseEnd_6402522 : Nat := 3287571186985704336930343

theorem tailTrace_6402522 : CollatzResearch.WordTrace tailWord_6402522 prefixEnd_6402522 3287571186985704336930343 := by
  unfold tailWord_6402522
  simp only [CollatzResearch.WordTrace]
  refine ⟨58379790427690933136904455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155679441140509155031745213 58379790427690933136904455)
  ·
    refine ⟨87569685641536399705356683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58379790427690933136904455 87569685641536399705356683)
    ·
      refine ⟨131354528462304599558035025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87569685641536399705356683 131354528462304599558035025)
      ·
        refine ⟨98515896346728449668526269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131354528462304599558035025 98515896346728449668526269)
        ·
          refine ⟨36943461130023168625697351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98515896346728449668526269 36943461130023168625697351)
          ·
            refine ⟨55415191695034752938546027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36943461130023168625697351 55415191695034752938546027)
            ·
              refine ⟨83122787542552129407819041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55415191695034752938546027 83122787542552129407819041)
              ·
                refine ⟨62342090656914097055864281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83122787542552129407819041 62342090656914097055864281)
                ·
                  refine ⟨46756567992685572791898211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62342090656914097055864281 46756567992685572791898211)
                  ·
                    refine ⟨70134851989028359187847317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46756567992685572791898211 70134851989028359187847317)
                    ·
                      refine ⟨3287571186985704336930343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70134851989028359187847317 3287571186985704336930343)
                      ·
                        rfl

theorem cell23_6402522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_6402522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402522 prefixEnd_6402522 := by exact prefixLift 6402522
  have htrace : WordTrace (prefixWord ++ tailWord_6402522) baseStart_6402522 baseEnd_6402522 := by
    simpa [prefixWord, tailWord_6402522, baseEnd_6402522] using wordTrace_append hprefix tailTrace_6402522
  have hstable : (prefixWord ++ tailWord_6402522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402522).length < 2 ^ (prefixWord ++ tailWord_6402522).sum := by decide
  have hdescent : baseEnd_6402522 < baseStart_6402522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402569 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 3, 5, 2]
def baseStart_6402569 : Nat := 118140960795 + 6402569 * 2 ^ 59
def prefixEnd_6402569 : Nat := 4983230072969 + 3 ^ 40 * 6402569 * 2
def baseEnd_6402569 : Nat := 3287595320576465653042627

theorem tailTrace_6402569 : CollatzResearch.WordTrace tailWord_6402569 prefixEnd_6402569 3287595320576465653042627 := by
  unfold tailWord_6402569
  simp only [CollatzResearch.WordTrace]
  refine ⟨233520875941593459574578761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155680583961062306383052507 233520875941593459574578761)
  ·
    refine ⟨175140656956195094680934071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233520875941593459574578761 175140656956195094680934071)
    ·
      refine ⟨262710985434292642021401107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175140656956195094680934071 262710985434292642021401107)
      ·
        refine ⟨394066478151438963032101661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262710985434292642021401107 394066478151438963032101661)
        ·
          refine ⟨147774929306789611137038123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394066478151438963032101661 147774929306789611137038123)
          ·
            refine ⟨221662393960184416705557185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147774929306789611137038123 221662393960184416705557185)
            ·
              refine ⟨166246795470138312529167889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221662393960184416705557185 166246795470138312529167889)
              ·
                refine ⟨124685096602603734396875917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166246795470138312529167889 124685096602603734396875917)
                ·
                  refine ⟨46756911225976400398828469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124685096602603734396875917 46756911225976400398828469)
                  ·
                    refine ⟨4383460427435287537390169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46756911225976400398828469 4383460427435287537390169)
                    ·
                      refine ⟨3287595320576465653042627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383460427435287537390169 3287595320576465653042627)
                      ·
                        rfl

theorem cell23_6402569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 5, 2].length) (baseStart_6402569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402569 prefixEnd_6402569 := by exact prefixLift 6402569
  have htrace : WordTrace (prefixWord ++ tailWord_6402569) baseStart_6402569 baseEnd_6402569 := by
    simpa [prefixWord, tailWord_6402569, baseEnd_6402569] using wordTrace_append hprefix tailTrace_6402569
  have hstable : (prefixWord ++ tailWord_6402569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402569).length < 2 ^ (prefixWord ++ tailWord_6402569).sum := by decide
  have hdescent : baseEnd_6402569 < baseStart_6402569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402609 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 6, 4]
def baseStart_6402609 : Nat := 118140960795 + 6402609 * 2 ^ 59
def prefixEnd_6402609 : Nat := 4983230072969 + 3 ^ 40 * 6402609 * 2
def baseEnd_6402609 : Nat := 1095871953267548498847481

theorem tailTrace_6402609 : CollatzResearch.WordTrace tailWord_6402609 prefixEnd_6402609 1095871953267548498847481 := by
  unfold tailWord_6402609
  simp only [CollatzResearch.WordTrace]
  refine ⟨233522334861448546406034881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155681556574299030937356587 233522334861448546406034881)
  ·
    refine ⟨175141751146086409804526161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233522334861448546406034881 175141751146086409804526161)
    ·
      refine ⟨131356313359564807353394621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175141751146086409804526161 131356313359564807353394621)
      ·
        refine ⟨49258617509836802757522983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131356313359564807353394621 49258617509836802757522983)
        ·
          refine ⟨73887926264755204136284475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49258617509836802757522983 73887926264755204136284475)
          ·
            refine ⟨110831889397132806204426713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73887926264755204136284475 110831889397132806204426713)
            ·
              refine ⟨83123917047849604653320035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110831889397132806204426713 83123917047849604653320035)
              ·
                refine ⟨124685875571774406979980053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83123917047849604653320035 124685875571774406979980053)
                ·
                  refine ⟨5844650417426925327186565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124685875571774406979980053 5844650417426925327186565)
                  ·
                    refine ⟨1095871953267548498847481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5844650417426925327186565 1095871953267548498847481)
                    ·
                      rfl

theorem cell23_6402609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_6402609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402609 prefixEnd_6402609 := by exact prefixLift 6402609
  have htrace : WordTrace (prefixWord ++ tailWord_6402609) baseStart_6402609 baseEnd_6402609 := by
    simpa [prefixWord, tailWord_6402609, baseEnd_6402609] using wordTrace_append hprefix tailTrace_6402609
  have hstable : (prefixWord ++ tailWord_6402609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402609).length < 2 ^ (prefixWord ++ tailWord_6402609).sum := by decide
  have hdescent : baseEnd_6402609 < baseStart_6402609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402666 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_6402666 : Nat := 118140960795 + 6402666 * 2 ^ 59
def prefixEnd_6402666 : Nat := 4983230072969 + 3 ^ 40 * 6402666 * 2
def baseEnd_6402666 : Nat := 3287645128199951773529681

theorem tailTrace_6402666 : CollatzResearch.WordTrace tailWord_6402666 prefixEnd_6402666 3287645128199951773529681 := by
  unfold tailWord_6402666
  simp only [CollatzResearch.WordTrace]
  refine ⟨58381103455560511285214963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155682942548161363427239901 58381103455560511285214963)
  ·
    refine ⟨87571655183340766927822445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58381103455560511285214963 87571655183340766927822445)
    ·
      refine ⟨32839370693752787597933417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87571655183340766927822445 32839370693752787597933417)
      ·
        refine ⟨24629528020314590698450063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32839370693752787597933417 24629528020314590698450063)
        ·
          refine ⟨36944292030471886047675095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24629528020314590698450063 36944292030471886047675095)
          ·
            refine ⟨55416438045707829071512643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36944292030471886047675095 55416438045707829071512643)
            ·
              refine ⟨83124657068561743607268965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55416438045707829071512643 83124657068561743607268965)
              ·
                refine ⟨15585873200355326926362931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83124657068561743607268965 15585873200355326926362931)
                ·
                  refine ⟨23378809800532990389544397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15585873200355326926362931 23378809800532990389544397)
                  ·
                    refine ⟨8767053675199871396079149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23378809800532990389544397 8767053675199871396079149)
                    ·
                      refine ⟨3287645128199951773529681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767053675199871396079149 3287645128199951773529681)
                      ·
                        rfl

theorem cell23_6402666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_6402666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402666 prefixEnd_6402666 := by exact prefixLift 6402666
  have htrace : WordTrace (prefixWord ++ tailWord_6402666) baseStart_6402666 baseEnd_6402666 := by
    simpa [prefixWord, tailWord_6402666, baseEnd_6402666] using wordTrace_append hprefix tailTrace_6402666
  have hstable : (prefixWord ++ tailWord_6402666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402666).length < 2 ^ (prefixWord ++ tailWord_6402666).sum := by decide
  have hdescent : baseEnd_6402666 < baseStart_6402666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402670 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_6402670 : Nat := 118140960795 + 6402670 * 2 ^ 59
def prefixEnd_6402670 : Nat := 4983230072969 + 3 ^ 40 * 6402670 * 2
def baseEnd_6402670 : Nat := 3287647182122569757879663

theorem tailTrace_6402670 : CollatzResearch.WordTrace tailWord_6402670 prefixEnd_6402670 3287647182122569757879663 := by
  unfold tailWord_6402670
  simp only [CollatzResearch.WordTrace]
  refine ⟨29190569964278444228000683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155683039809485035882670309 29190569964278444228000683)
  ·
    refine ⟨43785854946417666342001025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29190569964278444228000683 43785854946417666342001025)
    ·
      refine ⟨32839391209813249756500769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43785854946417666342001025 32839391209813249756500769)
      ·
        refine ⟨24629543407359937317375577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32839391209813249756500769 24629543407359937317375577)
        ·
          refine ⟨18472157555519952988031683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24629543407359937317375577 18472157555519952988031683)
          ·
            refine ⟨27708236333279929482047525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18472157555519952988031683 27708236333279929482047525)
            ·
              refine ⟨5195294312489986777883911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27708236333279929482047525 5195294312489986777883911)
              ·
                refine ⟨7792941468734980166825867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195294312489986777883911 7792941468734980166825867)
                ·
                  refine ⟨11689412203102470250238801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7792941468734980166825867 11689412203102470250238801)
                  ·
                    refine ⟨8767059152326852687679101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11689412203102470250238801 8767059152326852687679101)
                    ·
                      refine ⟨3287647182122569757879663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767059152326852687679101 3287647182122569757879663)
                      ·
                        rfl

theorem cell23_6402670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_6402670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402670 prefixEnd_6402670 := by exact prefixLift 6402670
  have htrace : WordTrace (prefixWord ++ tailWord_6402670) baseStart_6402670 baseEnd_6402670 := by
    simpa [prefixWord, tailWord_6402670, baseEnd_6402670] using wordTrace_append hprefix tailTrace_6402670
  have hstable : (prefixWord ++ tailWord_6402670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402670).length < 2 ^ (prefixWord ++ tailWord_6402670).sum := by decide
  have hdescent : baseEnd_6402670 < baseStart_6402670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402677 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_6402677 : Nat := 118140960795 + 6402677 * 2 ^ 59
def prefixEnd_6402677 : Nat := 4983230072969 + 3 ^ 40 * 6402677 * 2
def baseEnd_6402677 : Nat := 1095883592162383743497377

theorem tailTrace_6402677 : CollatzResearch.WordTrace tailWord_6402677 prefixEnd_6402677 1095883592162383743497377 := by
  unfold tailWord_6402677
  simp only [CollatzResearch.WordTrace]
  refine ⟨233524815025202194019510285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155683210016801462679673523 233524815025202194019510285)
  ·
    refine ⟨87571805634450822757316357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233524815025202194019510285 87571805634450822757316357)
    ·
      refine ⟨16419713556459529266996817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87571805634450822757316357 16419713556459529266996817)
      ·
        refine ⟨12314785167344646950247613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16419713556459529266996817 12314785167344646950247613)
        ·
          refine ⟨4618044437754242606342855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12314785167344646950247613 4618044437754242606342855)
          ·
            refine ⟨6927066656631363909514283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618044437754242606342855 6927066656631363909514283)
            ·
              refine ⟨10390599984947045864271425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927066656631363909514283 10390599984947045864271425)
              ·
                refine ⟨7792949988710284398203569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10390599984947045864271425 7792949988710284398203569)
                ·
                  refine ⟨5844712491532713298652677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7792949988710284398203569 5844712491532713298652677)
                  ·
                    refine ⟨1095883592162383743497377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5844712491532713298652677 1095883592162383743497377)
                    ·
                      rfl

theorem cell23_6402677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_6402677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402677 prefixEnd_6402677 := by exact prefixLift 6402677
  have htrace : WordTrace (prefixWord ++ tailWord_6402677) baseStart_6402677 baseEnd_6402677 := by
    simpa [prefixWord, tailWord_6402677, baseEnd_6402677] using wordTrace_append hprefix tailTrace_6402677
  have hstable : (prefixWord ++ tailWord_6402677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402677).length < 2 ^ (prefixWord ++ tailWord_6402677).sum := by decide
  have hdescent : baseEnd_6402677 < baseStart_6402677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402759 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 1, 7]
def baseStart_6402759 : Nat := 118140960795 + 6402759 * 2 ^ 59
def prefixEnd_6402759 : Nat := 4983230072969 + 3 ^ 40 * 6402759 * 2
def baseEnd_6402759 : Nat := 1095897627300273303222251

theorem tailTrace_6402759 : CollatzResearch.WordTrace tailWord_6402759 prefixEnd_6402759 1095897627300273303222251 := by
  unfold tailWord_6402759
  simp only [CollatzResearch.WordTrace]
  refine ⟨233527805810905122023995331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155685203873936748015996887 233527805810905122023995331)
  ·
    refine ⟨350291708716357683035992997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233527805810905122023995331 350291708716357683035992997)
    ·
      refine ⟨65679695384317065569248687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350291708716357683035992997 65679695384317065569248687)
      ·
        refine ⟨98519543076475598353873031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65679695384317065569248687 98519543076475598353873031)
        ·
          refine ⟨147779314614713397530809547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98519543076475598353873031 147779314614713397530809547)
          ·
            refine ⟨221668971922070096296214321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147779314614713397530809547 221668971922070096296214321)
            ·
              refine ⟨166251728941552572222160741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221668971922070096296214321 166251728941552572222160741)
              ·
                refine ⟨31172199176541107291655139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166251728941552572222160741 31172199176541107291655139)
                ·
                  refine ⟨46758298764811660937482709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31172199176541107291655139 46758298764811660937482709)
                  ·
                    refine ⟨1095897627300273303222251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46758298764811660937482709 1095897627300273303222251)
                    ·
                      rfl

theorem cell23_6402759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_6402759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402759 prefixEnd_6402759 := by exact prefixLift 6402759
  have htrace : WordTrace (prefixWord ++ tailWord_6402759) baseStart_6402759 baseEnd_6402759 := by
    simpa [prefixWord, tailWord_6402759, baseEnd_6402759] using wordTrace_append hprefix tailTrace_6402759
  have hstable : (prefixWord ++ tailWord_6402759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402759).length < 2 ^ (prefixWord ++ tailWord_6402759).sum := by decide
  have hdescent : baseEnd_6402759 < baseStart_6402759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402769 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_6402769 : Nat := 118140960795 + 6402769 * 2 ^ 59
def prefixEnd_6402769 : Nat := 4983230072969 + 3 ^ 40 * 6402769 * 2
def baseEnd_6402769 : Nat := 3287698016707364870541707

theorem tailTrace_6402769 : CollatzResearch.WordTrace tailWord_6402769 prefixEnd_6402769 3287698016707364870541707 := by
  unfold tailWord_6402769
  simp only [CollatzResearch.WordTrace]
  refine ⟨233528170540868893731859361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155685447027245929154572907 233528170540868893731859361)
  ·
    refine ⟨175146127905651670298894521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233528170540868893731859361 175146127905651670298894521)
    ·
      refine ⟨131359595929238752724170891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175146127905651670298894521 131359595929238752724170891)
      ·
        refine ⟨197039393893858129086256337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131359595929238752724170891 197039393893858129086256337)
        ·
          refine ⟨147779545420393596814692253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197039393893858129086256337 147779545420393596814692253)
          ·
            refine ⟨55417329532647598805509595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147779545420393596814692253 55417329532647598805509595)
            ·
              refine ⟨83125994298971398208264393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55417329532647598805509595 83125994298971398208264393)
              ·
                refine ⟨62344495724228548656198295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83125994298971398208264393 62344495724228548656198295)
                ·
                  refine ⟨93516743586342822984297443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62344495724228548656198295 93516743586342822984297443)
                  ·
                    refine ⟨140275115379514234476446165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93516743586342822984297443 140275115379514234476446165)
                    ·
                      refine ⟨3287698016707364870541707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140275115379514234476446165 3287698016707364870541707)
                      ·
                        rfl

theorem cell23_6402769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_6402769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402769 prefixEnd_6402769 := by exact prefixLift 6402769
  have htrace : WordTrace (prefixWord ++ tailWord_6402769) baseStart_6402769 baseEnd_6402769 := by
    simpa [prefixWord, tailWord_6402769, baseEnd_6402769] using wordTrace_append hprefix tailTrace_6402769
  have hstable : (prefixWord ++ tailWord_6402769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402769).length < 2 ^ (prefixWord ++ tailWord_6402769).sum := by decide
  have hdescent : baseEnd_6402769 < baseStart_6402769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402776 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_6402776 : Nat := 118140960795 + 6402776 * 2 ^ 59
def prefixEnd_6402776 : Nat := 4983230072969 + 3 ^ 40 * 6402776 * 2
def baseEnd_6402776 : Nat := 1095900537023982114384725

theorem tailTrace_6402776 : CollatzResearch.WordTrace tailWord_6402776 prefixEnd_6402776 1095900537023982114384725 := by
  unfold tailWord_6402776
  simp only [CollatzResearch.WordTrace]
  refine ⟨116764212925921766963682091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155685617234562355951576121 116764212925921766963682091)
  ·
    refine ⟨175146319388882650445523137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116764212925921766963682091 175146319388882650445523137)
    ·
      refine ⟨131359739541661987834142353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175146319388882650445523137 131359739541661987834142353)
      ·
        refine ⟨98519804656246490875606765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131359739541661987834142353 98519804656246490875606765)
        ·
          refine ⟨36944926746092434078352537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98519804656246490875606765 36944926746092434078352537)
          ·
            refine ⟨27708695059569325558764403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36944926746092434078352537 27708695059569325558764403)
            ·
              refine ⟨41563042589353988338146605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27708695059569325558764403 41563042589353988338146605)
              ·
                refine ⟨15586140971007745626804977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41563042589353988338146605 15586140971007745626804977)
                ·
                  refine ⟨11689605728255809220103733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15586140971007745626804977 11689605728255809220103733)
                  ·
                    refine ⟨1095900537023982114384725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11689605728255809220103733 1095900537023982114384725)
                    ·
                      rfl

theorem cell23_6402776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_6402776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402776 prefixEnd_6402776 := by exact prefixLift 6402776
  have htrace : WordTrace (prefixWord ++ tailWord_6402776) baseStart_6402776 baseEnd_6402776 := by
    simpa [prefixWord, tailWord_6402776, baseEnd_6402776] using wordTrace_append hprefix tailTrace_6402776
  have hstable : (prefixWord ++ tailWord_6402776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402776).length < 2 ^ (prefixWord ++ tailWord_6402776).sum := by decide
  have hdescent : baseEnd_6402776 < baseStart_6402776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402813 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_6402813 : Nat := 118140960795 + 6402813 * 2 ^ 59
def prefixEnd_6402813 : Nat := 4983230072969 + 3 ^ 40 * 6402813 * 2
def baseEnd_6402813 : Nat := 3287720609856162698391505

theorem tailTrace_6402813 : CollatzResearch.WordTrace tailWord_6402813 prefixEnd_6402813 3287720609856162698391505 := by
  unfold tailWord_6402813
  simp only [CollatzResearch.WordTrace]
  refine ⟨233529775352709489246461093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155686516901806326164307395 233529775352709489246461093)
  ·
    refine ⟨43786832878633029233711455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233529775352709489246461093 43786832878633029233711455)
    ·
      refine ⟨65680249317949543850567183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43786832878633029233711455 65680249317949543850567183)
      ·
        refine ⟨98520373976924315775850775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65680249317949543850567183 98520373976924315775850775)
        ·
          refine ⟨147780560965386473663776163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98520373976924315775850775 147780560965386473663776163)
          ·
            refine ⟨221670841448079710495664245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147780560965386473663776163 221670841448079710495664245)
            ·
              refine ⟨20781641385757472858968523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221670841448079710495664245 20781641385757472858968523)
              ·
                refine ⟨31172462078636209288452785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20781641385757472858968523 31172462078636209288452785)
                ·
                  refine ⟨23379346558977156966339589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31172462078636209288452785 23379346558977156966339589)
                  ·
                    refine ⟨4383627479808216931188673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23379346558977156966339589 4383627479808216931188673)
                    ·
                      refine ⟨3287720609856162698391505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383627479808216931188673 3287720609856162698391505)
                      ·
                        rfl

theorem cell23_6402813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_6402813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402813 prefixEnd_6402813 := by exact prefixLift 6402813
  have htrace : WordTrace (prefixWord ++ tailWord_6402813) baseStart_6402813 baseEnd_6402813 := by
    simpa [prefixWord, tailWord_6402813, baseEnd_6402813] using wordTrace_append hprefix tailTrace_6402813
  have hstable : (prefixWord ++ tailWord_6402813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402813).length < 2 ^ (prefixWord ++ tailWord_6402813).sum := by decide
  have hdescent : baseEnd_6402813 < baseStart_6402813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402819 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 10]
def baseStart_6402819 : Nat := 118140960795 + 6402819 * 2 ^ 59
def prefixEnd_6402819 : Nat := 4983230072969 + 3 ^ 40 * 6402819 * 2
def baseEnd_6402819 : Nat := 365302632304454408324053

theorem tailTrace_6402819 : CollatzResearch.WordTrace tailWord_6402819 prefixEnd_6402819 365302632304454408324053 := by
  unfold tailWord_6402819
  simp only [CollatzResearch.WordTrace]
  refine ⟨233529994190687752271179511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155686662793791834847453007 233529994190687752271179511)
  ·
    refine ⟨350294991286031628406769267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233529994190687752271179511 350294991286031628406769267)
    ·
      refine ⟨525442486929047442610153901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350294991286031628406769267 525442486929047442610153901)
      ·
        refine ⟨197040932598392790978807713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525442486929047442610153901 197040932598392790978807713)
        ·
          refine ⟨147780699448794593234105785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197040932598392790978807713 147780699448794593234105785)
          ·
            refine ⟨110835524586595944925579339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147780699448794593234105785 110835524586595944925579339)
            ·
              refine ⟨166253286879893917388369009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110835524586595944925579339 166253286879893917388369009)
              ·
                refine ⟨124689965159920438041276757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166253286879893917388369009 124689965159920438041276757)
                ·
                  refine ⟨365302632304454408324053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124689965159920438041276757 365302632304454408324053)
                  ·
                    rfl

theorem cell23_6402819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 10].length) (baseStart_6402819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402819 prefixEnd_6402819 := by exact prefixLift 6402819
  have htrace : WordTrace (prefixWord ++ tailWord_6402819) baseStart_6402819 baseEnd_6402819 := by
    simpa [prefixWord, tailWord_6402819, baseEnd_6402819] using wordTrace_append hprefix tailTrace_6402819
  have hstable : (prefixWord ++ tailWord_6402819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402819).length < 2 ^ (prefixWord ++ tailWord_6402819).sum := by decide
  have hdescent : baseEnd_6402819 < baseStart_6402819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402823 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 5, 4]
def baseStart_6402823 : Nat := 118140960795 + 6402823 * 2 ^ 59
def prefixEnd_6402823 : Nat := 4983230072969 + 3 ^ 40 * 6402823 * 2
def baseEnd_6402823 : Nat := 1095908581554235886422153

theorem tailTrace_6402823 : CollatzResearch.WordTrace tailWord_6402823 prefixEnd_6402823 1095908581554235886422153 := by
  unfold tailWord_6402823
  simp only [CollatzResearch.WordTrace]
  refine ⟨233530140082673260954325123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155686760055115507302883415 233530140082673260954325123)
  ·
    refine ⟨350295210124009891431487685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233530140082673260954325123 350295210124009891431487685)
    ·
      refine ⟨65680351898251854643403941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350295210124009891431487685 65680351898251854643403941)
      ·
        refine ⟨12315065980922222745638239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65680351898251854643403941 12315065980922222745638239)
        ·
          refine ⟨18472598971383334118457359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12315065980922222745638239 18472598971383334118457359)
          ·
            refine ⟨27708898457075001177686039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18472598971383334118457359 27708898457075001177686039)
            ·
              refine ⟨41563347685612501766529059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27708898457075001177686039 41563347685612501766529059)
              ·
                refine ⟨62345021528418752649793589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41563347685612501766529059 62345021528418752649793589)
                ·
                  refine ⟨5844845768289258060918149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62345021528418752649793589 5844845768289258060918149)
                  ·
                    refine ⟨1095908581554235886422153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5844845768289258060918149 1095908581554235886422153)
                    ·
                      rfl

theorem cell23_6402823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_6402823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402823 prefixEnd_6402823 := by exact prefixLift 6402823
  have htrace : WordTrace (prefixWord ++ tailWord_6402823) baseStart_6402823 baseEnd_6402823 := by
    simpa [prefixWord, tailWord_6402823, baseEnd_6402823] using wordTrace_append hprefix tailTrace_6402823
  have hstable : (prefixWord ++ tailWord_6402823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402823).length < 2 ^ (prefixWord ++ tailWord_6402823).sum := by decide
  have hdescent : baseEnd_6402823 < baseStart_6402823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402833 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_6402833 : Nat := 118140960795 + 6402833 * 2 ^ 59
def prefixEnd_6402833 : Nat := 4983230072969 + 3 ^ 40 * 6402833 * 2
def baseEnd_6402833 : Nat := 3287730879469252620141413

theorem tailTrace_6402833 : CollatzResearch.WordTrace tailWord_6402833 prefixEnd_6402833 3287730879469252620141413 := by
  unfold tailWord_6402833
  simp only [CollatzResearch.WordTrace]
  refine ⟨233530504812637032662189153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155687003208424688441459435 233530504812637032662189153)
  ·
    refine ⟨175147878609477774496641865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233530504812637032662189153 175147878609477774496641865)
    ·
      refine ⟨131360908957108330872481399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175147878609477774496641865 131360908957108330872481399)
      ·
        refine ⟨197041363435662496308722099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131360908957108330872481399 197041363435662496308722099)
        ·
          refine ⟨295562045153493744463083149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197041363435662496308722099 295562045153493744463083149)
          ·
            refine ⟨110835766932560154173656181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295562045153493744463083149 110835766932560154173656181)
            ·
              refine ⟨10390853149927514453780267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110835766932560154173656181 10390853149927514453780267)
              ·
                refine ⟨15586279724891271680670401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10390853149927514453780267 15586279724891271680670401)
                ·
                  refine ⟨11689709793668453760502801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15586279724891271680670401 11689709793668453760502801)
                  ·
                    refine ⟨8767282345251340320377101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11689709793668453760502801 8767282345251340320377101)
                    ·
                      refine ⟨3287730879469252620141413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767282345251340320377101 3287730879469252620141413)
                      ·
                        rfl

theorem cell23_6402833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_6402833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402833 prefixEnd_6402833 := by exact prefixLift 6402833
  have htrace : WordTrace (prefixWord ++ tailWord_6402833) baseStart_6402833 baseEnd_6402833 := by
    simpa [prefixWord, tailWord_6402833, baseEnd_6402833] using wordTrace_append hprefix tailTrace_6402833
  have hstable : (prefixWord ++ tailWord_6402833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402833).length < 2 ^ (prefixWord ++ tailWord_6402833).sum := by decide
  have hdescent : baseEnd_6402833 < baseStart_6402833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402856 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6402856 : Nat := 118140960795 + 6402856 * 2 ^ 59
def prefixEnd_6402856 : Nat := 4983230072969 + 3 ^ 40 * 6402856 * 2
def baseEnd_6402856 : Nat := 3287742689524306030153807

theorem tailTrace_6402856 : CollatzResearch.WordTrace tailWord_6402856 prefixEnd_6402856 3287742689524306030153807 := by
  unfold tailWord_6402856
  simp only [CollatzResearch.WordTrace]
  refine ⟨116765671845776853795138211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155687562461035805060184281 116765671845776853795138211)
  ·
    refine ⟨175148507768665280692707317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116765671845776853795138211 175148507768665280692707317)
    ·
      refine ⟨16420172603312370064941311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175148507768665280692707317 16420172603312370064941311)
      ·
        refine ⟨24630258904968555097411967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16420172603312370064941311 24630258904968555097411967)
        ·
          refine ⟨36945388357452832646117951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24630258904968555097411967 36945388357452832646117951)
          ·
            refine ⟨55418082536179248969176927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36945388357452832646117951 55418082536179248969176927)
            ·
              refine ⟨83127123804268873453765391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55418082536179248969176927 83127123804268873453765391)
              ·
                refine ⟨124690685706403310180648087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83127123804268873453765391 124690685706403310180648087)
                ·
                  refine ⟨187036028559604965270972131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124690685706403310180648087 187036028559604965270972131)
                  ·
                    refine ⟨280554042839407447906458197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187036028559604965270972131 280554042839407447906458197)
                    ·
                      refine ⟨3287742689524306030153807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 280554042839407447906458197 3287742689524306030153807)
                      ·
                        rfl

theorem cell23_6402856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6402856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402856 prefixEnd_6402856 := by exact prefixLift 6402856
  have htrace : WordTrace (prefixWord ++ tailWord_6402856) baseStart_6402856 baseEnd_6402856 := by
    simpa [prefixWord, tailWord_6402856, baseEnd_6402856] using wordTrace_append hprefix tailTrace_6402856
  have hstable : (prefixWord ++ tailWord_6402856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402856).length < 2 ^ (prefixWord ++ tailWord_6402856).sum := by decide
  have hdescent : baseEnd_6402856 < baseStart_6402856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402883 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 1, 5]
def baseStart_6402883 : Nat := 118140960795 + 6402883 * 2 ^ 59
def prefixEnd_6402883 : Nat := 4983230072969 + 3 ^ 40 * 6402883 * 2
def baseEnd_6402883 : Nat := 1095918851167325808172061

theorem tailTrace_6402883 : CollatzResearch.WordTrace tailWord_6402883 prefixEnd_6402883 1095918851167325808172061 := by
  unfold tailWord_6402883
  simp only [CollatzResearch.WordTrace]
  refine ⟨233532328462455891201509303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155688218974970594134339535 233532328462455891201509303)
  ·
    refine ⟨350298492693683836802263955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233532328462455891201509303 350298492693683836802263955)
    ·
      refine ⟨525447739040525755203395933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350298492693683836802263955 525447739040525755203395933)
      ·
        refine ⟨197042902140197158201273475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525447739040525755203395933 197042902140197158201273475)
        ·
          refine ⟨295564353210295737301910213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197042902140197158201273475 295564353210295737301910213)
          ·
            refine ⟨55418316226930450744108165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295564353210295737301910213 55418316226930450744108165)
            ·
              refine ⟨10390934292549459514520281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55418316226930450744108165 10390934292549459514520281)
              ·
                refine ⟨7793200719412094635890211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10390934292549459514520281 7793200719412094635890211)
                ·
                  refine ⟨11689801079118141953835317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793200719412094635890211 11689801079118141953835317)
                  ·
                    refine ⟨1095918851167325808172061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11689801079118141953835317 1095918851167325808172061)
                    ·
                      rfl

theorem cell23_6402883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 5].length) (baseStart_6402883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402883 prefixEnd_6402883 := by exact prefixLift 6402883
  have htrace : WordTrace (prefixWord ++ tailWord_6402883) baseStart_6402883 baseEnd_6402883 := by
    simpa [prefixWord, tailWord_6402883, baseEnd_6402883] using wordTrace_append hprefix tailTrace_6402883
  have hstable : (prefixWord ++ tailWord_6402883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402883).length < 2 ^ (prefixWord ++ tailWord_6402883).sum := by decide
  have hdescent : baseEnd_6402883 < baseStart_6402883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402896 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_6402896 : Nat := 118140960795 + 6402896 * 2 ^ 59
def prefixEnd_6402896 : Nat := 4983230072969 + 3 ^ 40 * 6402896 * 2
def baseEnd_6402896 : Nat := 1095921076250161957884541

theorem tailTrace_6402896 : CollatzResearch.WordTrace tailWord_6402896 prefixEnd_6402896 1095921076250161957884541 := by
  unfold tailWord_6402896
  simp only [CollatzResearch.WordTrace]
  refine ⟨116766401305704397210866271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155688535074272529614488361 116766401305704397210866271)
  ·
    refine ⟨175149601958556595816299407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116766401305704397210866271 175149601958556595816299407)
    ·
      refine ⟨262724402937834893724449111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175149601958556595816299407 262724402937834893724449111)
      ·
        refine ⟨394086604406752340586673667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262724402937834893724449111 394086604406752340586673667)
        ·
          refine ⟨591129906610128510880010501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394086604406752340586673667 591129906610128510880010501)
          ·
            refine ⟨110836857489399095790001969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 591129906610128510880010501 110836857489399095790001969)
            ·
              refine ⟨83127643117049321842501477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110836857489399095790001969 83127643117049321842501477)
              ·
                refine ⟨15586433084446747845469027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83127643117049321842501477 15586433084446747845469027)
                ·
                  refine ⟨23379649626670121768203541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15586433084446747845469027 23379649626670121768203541)
                  ·
                    refine ⟨1095921076250161957884541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23379649626670121768203541 1095921076250161957884541)
                    ·
                      rfl

theorem cell23_6402896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_6402896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402896 prefixEnd_6402896 := by exact prefixLift 6402896
  have htrace : WordTrace (prefixWord ++ tailWord_6402896) baseStart_6402896 baseEnd_6402896 := by
    simpa [prefixWord, tailWord_6402896, baseEnd_6402896] using wordTrace_append hprefix tailTrace_6402896
  have hstable : (prefixWord ++ tailWord_6402896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402896).length < 2 ^ (prefixWord ++ tailWord_6402896).sum := by decide
  have hdescent : baseEnd_6402896 < baseStart_6402896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402914 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_6402914 : Nat := 118140960795 + 6402914 * 2 ^ 59
def prefixEnd_6402914 : Nat := 4983230072969 + 3 ^ 40 * 6402914 * 2
def baseEnd_6402914 : Nat := 3287772471402266803228541

theorem tailTrace_6402914 : CollatzResearch.WordTrace tailWord_6402914 prefixEnd_6402914 3287772471402266803228541 := by
  unfold tailWord_6402914
  simp only [CollatzResearch.WordTrace]
  refine ⟨58383364781335895873971949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155688972750229055663925197 58383364781335895873971949)
  ·
    refine ⟨21893761793000960952739481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58383364781335895873971949 21893761793000960952739481)
    ·
      refine ⟨16420321344750720714554611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21893761793000960952739481 16420321344750720714554611)
      ·
        refine ⟨24630482017126081071831917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16420321344750720714554611 24630482017126081071831917)
        ·
          refine ⟨9236430756422280401936969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24630482017126081071831917 9236430756422280401936969)
          ·
            refine ⟨6927323067316710301452727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9236430756422280401936969 6927323067316710301452727)
            ·
              refine ⟨10390984600975065452179091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927323067316710301452727 10390984600975065452179091)
              ·
                refine ⟨15586476901462598178268637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10390984600975065452179091 15586476901462598178268637)
                ·
                  refine ⟨5844928838048474316850739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15586476901462598178268637 5844928838048474316850739)
                  ·
                    refine ⟨8767393257072711475276109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5844928838048474316850739 8767393257072711475276109)
                    ·
                      refine ⟨3287772471402266803228541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767393257072711475276109 3287772471402266803228541)
                      ·
                        rfl

theorem cell23_6402914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_6402914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402914 prefixEnd_6402914 := by exact prefixLift 6402914
  have htrace : WordTrace (prefixWord ++ tailWord_6402914) baseStart_6402914 baseEnd_6402914 := by
    simpa [prefixWord, tailWord_6402914, baseEnd_6402914] using wordTrace_append hprefix tailTrace_6402914
  have hstable : (prefixWord ++ tailWord_6402914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402914).length < 2 ^ (prefixWord ++ tailWord_6402914).sum := by decide
  have hdescent : baseEnd_6402914 < baseStart_6402914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402933 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6402933 : Nat := 118140960795 + 6402933 * 2 ^ 59
def prefixEnd_6402933 : Nat := 4983230072969 + 3 ^ 40 * 6402933 * 2
def baseEnd_6402933 : Nat := 3287782227534702228890953

theorem tailTrace_6402933 : CollatzResearch.WordTrace tailWord_6402933 prefixEnd_6402933 3287782227534702228890953 := by
  unfold tailWord_6402933
  simp only [CollatzResearch.WordTrace]
  refine ⟨233534152112274749740829453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155689434741516499827219635 233534152112274749740829453)
  ·
    refine ⟨87575307042103031152811045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233534152112274749740829453 87575307042103031152811045)
    ·
      refine ⟨16420370070394318341152071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87575307042103031152811045 16420370070394318341152071)
      ·
        refine ⟨24630555105591477511728107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16420370070394318341152071 24630555105591477511728107)
        ·
          refine ⟨36945832658387216267592161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24630555105591477511728107 36945832658387216267592161)
          ·
            refine ⟨27709374493790412200694121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36945832658387216267592161 27709374493790412200694121)
            ·
              refine ⟨20782030870342809150520591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27709374493790412200694121 20782030870342809150520591)
              ·
                refine ⟨31173046305514213725780887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20782030870342809150520591 31173046305514213725780887)
                ·
                  refine ⟨46759569458271320588671331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31173046305514213725780887 46759569458271320588671331)
                  ·
                    refine ⟨70139354187406980883006997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46759569458271320588671331 70139354187406980883006997)
                    ·
                      refine ⟨3287782227534702228890953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70139354187406980883006997 3287782227534702228890953)
                      ·
                        rfl

theorem cell23_6402933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6402933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402933 prefixEnd_6402933 := by exact prefixLift 6402933
  have htrace : WordTrace (prefixWord ++ tailWord_6402933) baseStart_6402933 baseEnd_6402933 := by
    simpa [prefixWord, tailWord_6402933, baseEnd_6402933] using wordTrace_append hprefix tailTrace_6402933
  have hstable : (prefixWord ++ tailWord_6402933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402933).length < 2 ^ (prefixWord ++ tailWord_6402933).sum := by decide
  have hdescent : baseEnd_6402933 < baseStart_6402933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402953 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_6402953 : Nat := 118140960795 + 6402953 * 2 ^ 59
def prefixEnd_6402953 : Nat := 4983230072969 + 3 ^ 40 * 6402953 * 2
def baseEnd_6402953 : Nat := 3287792497147792150640861

theorem tailTrace_6402953 : CollatzResearch.WordTrace tailWord_6402953 prefixEnd_6402953 3287792497147792150640861 := by
  unfold tailWord_6402953
  simp only [CollatzResearch.WordTrace]
  refine ⟨233534881572202293156557513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155689921048134862104371675 233534881572202293156557513)
  ·
    refine ⟨175151161179151719867418135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233534881572202293156557513 175151161179151719867418135)
    ·
      refine ⟨262726741768727579801127203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175151161179151719867418135 262726741768727579801127203)
      ·
        refine ⟨394090112653091369701690805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262726741768727579801127203 394090112653091369701690805)
        ·
          refine ⟨36945948061227315909533513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 394090112653091369701690805 36945948061227315909533513)
          ·
            refine ⟨27709461045920486932150135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36945948061227315909533513 27709461045920486932150135)
            ·
              refine ⟨41564191568880730398225203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27709461045920486932150135 41564191568880730398225203)
              ·
                refine ⟨62346287353321095597337805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41564191568880730398225203 62346287353321095597337805)
                ·
                  refine ⟨23379857757495410849001677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62346287353321095597337805 23379857757495410849001677)
                  ·
                    refine ⟨8767446659060779068375629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23379857757495410849001677 8767446659060779068375629)
                    ·
                      refine ⟨3287792497147792150640861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767446659060779068375629 3287792497147792150640861)
                      ·
                        rfl

theorem cell23_6402953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_6402953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402953 prefixEnd_6402953 := by exact prefixLift 6402953
  have htrace : WordTrace (prefixWord ++ tailWord_6402953) baseStart_6402953 baseEnd_6402953 := by
    simpa [prefixWord, tailWord_6402953, baseEnd_6402953] using wordTrace_append hprefix tailTrace_6402953
  have hstable : (prefixWord ++ tailWord_6402953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402953).length < 2 ^ (prefixWord ++ tailWord_6402953).sum := by decide
  have hdescent : baseEnd_6402953 < baseStart_6402953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402980 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_6402980 : Nat := 118140960795 + 6402980 * 2 ^ 59
def prefixEnd_6402980 : Nat := 4983230072969 + 3 ^ 40 * 6402980 * 2
def baseEnd_6402980 : Nat := 3287806361125463545003237

theorem tailTrace_6402980 : CollatzResearch.WordTrace tailWord_6402980 prefixEnd_6402980 3287806361125463545003237 := by
  unfold tailWord_6402980
  simp only [CollatzResearch.WordTrace]
  refine ⟨116767933171552238383895197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155690577562069651178526929 116767933171552238383895197)
  ·
    refine ⟨43787974939332089393960699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116767933171552238383895197 43787974939332089393960699)
    ·
      refine ⟨65681962408998134090941049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43787974939332089393960699 65681962408998134090941049)
      ·
        refine ⟨49261471806748600568205787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65681962408998134090941049 49261471806748600568205787)
        ·
          refine ⟨73892207710122900852308681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49261471806748600568205787 73892207710122900852308681)
          ·
            refine ⟨55419155782592175639231511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73892207710122900852308681 55419155782592175639231511)
            ·
              refine ⟨83128733673888263458847267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55419155782592175639231511 83128733673888263458847267)
              ·
                refine ⟨124693100510832395188270901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83128733673888263458847267 124693100510832395188270901)
                ·
                  refine ⟨11689978172890537048900397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124693100510832395188270901 11689978172890537048900397)
                  ·
                    refine ⟨4383741814833951393337649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11689978172890537048900397 4383741814833951393337649)
                    ·
                      refine ⟨3287806361125463545003237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383741814833951393337649 3287806361125463545003237)
                      ·
                        rfl

theorem cell23_6402980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_6402980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402980 prefixEnd_6402980 := by exact prefixLift 6402980
  have htrace : WordTrace (prefixWord ++ tailWord_6402980) baseStart_6402980 baseEnd_6402980 := by
    simpa [prefixWord, tailWord_6402980, baseEnd_6402980] using wordTrace_append hprefix tailTrace_6402980
  have hstable : (prefixWord ++ tailWord_6402980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402980).length < 2 ^ (prefixWord ++ tailWord_6402980).sum := by decide
  have hdescent : baseEnd_6402980 < baseStart_6402980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6402997 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_6402997 : Nat := 118140960795 + 6402997 * 2 ^ 59
def prefixEnd_6402997 : Nat := 4983230072969 + 3 ^ 40 * 6402997 * 2
def baseEnd_6402997 : Nat := 3287815090296589978490659

theorem tailTrace_6402997 : CollatzResearch.WordTrace tailWord_6402997 prefixEnd_6402997 3287815090296589978490659 := by
  unfold tailWord_6402997
  simp only [CollatzResearch.WordTrace]
  refine ⟨233536486384042888671159245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155690990922695259114106163 233536486384042888671159245)
  ·
    refine ⟨87576182394016083251684717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233536486384042888671159245 87576182394016083251684717)
    ·
      refine ⟨32841068397756031219381769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87576182394016083251684717 32841068397756031219381769)
      ·
        refine ⟨24630801298317023414536327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32841068397756031219381769 24630801298317023414536327)
        ·
          refine ⟨36946201947475535121804491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24630801298317023414536327 36946201947475535121804491)
          ·
            refine ⟨55419302921213302682706737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36946201947475535121804491 55419302921213302682706737)
            ·
              refine ⟨41564477190909977012030053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55419302921213302682706737 41564477190909977012030053)
              ·
                refine ⟨7793339473295620689755635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41564477190909977012030053 7793339473295620689755635)
                ·
                  refine ⟨11690009209943431034633453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793339473295620689755635 11690009209943431034633453)
                  ·
                    refine ⟨4383753453728786637987545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11690009209943431034633453 4383753453728786637987545)
                    ·
                      refine ⟨3287815090296589978490659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383753453728786637987545 3287815090296589978490659)
                      ·
                        rfl

theorem cell23_6402997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_6402997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6402997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6402997 prefixEnd_6402997 := by exact prefixLift 6402997
  have htrace : WordTrace (prefixWord ++ tailWord_6402997) baseStart_6402997 baseEnd_6402997 := by
    simpa [prefixWord, tailWord_6402997, baseEnd_6402997] using wordTrace_append hprefix tailTrace_6402997
  have hstable : (prefixWord ++ tailWord_6402997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6402997).length < 2 ^ (prefixWord ++ tailWord_6402997).sum := by decide
  have hdescent : baseEnd_6402997 < baseStart_6402997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6402997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403023 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_6403023 : Nat := 118140960795 + 6403023 * 2 ^ 59
def prefixEnd_6403023 : Nat := 4983230072969 + 3 ^ 40 * 6403023 * 2
def baseEnd_6403023 : Nat := 3287828440793606876765539

theorem tailTrace_6403023 : CollatzResearch.WordTrace tailWord_6403023 prefixEnd_6403023 3287828440793606876765539 := by
  unfold tailWord_6403023
  simp only [CollatzResearch.WordTrace]
  refine ⟨233537434681948695111605723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155691623121299130074403815 233537434681948695111605723)
  ·
    refine ⟨350306152022923042667408585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233537434681948695111605723 350306152022923042667408585)
    ·
      refine ⟨262729614017192282000556439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350306152022923042667408585 262729614017192282000556439)
      ·
        refine ⟨394094421025788423000834659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262729614017192282000556439 394094421025788423000834659)
        ·
          refine ⟨591141631538682634501251989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394094421025788423000834659 591141631538682634501251989)
          ·
            refine ⟨27709763978375748492246187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 591141631538682634501251989 27709763978375748492246187)
            ·
              refine ⟨41564645967563622738369281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27709763978375748492246187 41564645967563622738369281)
              ·
                refine ⟨31173484475672717053776961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41564645967563622738369281 31173484475672717053776961)
                ·
                  refine ⟨23380113356754537790332721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31173484475672717053776961 23380113356754537790332721)
                  ·
                    refine ⟨17535085017565903342749541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23380113356754537790332721 17535085017565903342749541)
                    ·
                      refine ⟨3287828440793606876765539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17535085017565903342749541 3287828440793606876765539)
                      ·
                        rfl

theorem cell23_6403023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_6403023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403023 prefixEnd_6403023 := by exact prefixLift 6403023
  have htrace : WordTrace (prefixWord ++ tailWord_6403023) baseStart_6403023 baseEnd_6403023 := by
    simpa [prefixWord, tailWord_6403023, baseEnd_6403023] using wordTrace_append hprefix tailTrace_6403023
  have hstable : (prefixWord ++ tailWord_6403023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403023).length < 2 ^ (prefixWord ++ tailWord_6403023).sum := by decide
  have hdescent : baseEnd_6403023 < baseStart_6403023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403033 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 7]
def baseStart_6403033 : Nat := 118140960795 + 6403033 * 2 ^ 59
def prefixEnd_6403033 : Nat := 4983230072969 + 3 ^ 40 * 6403033 * 2
def baseEnd_6403033 : Nat := 365314841733350204182277

theorem tailTrace_6403033 : CollatzResearch.WordTrace tailWord_6403033 prefixEnd_6403033 365314841733350204182277 := by
  unfold tailWord_6403033
  simp only [CollatzResearch.WordTrace]
  refine ⟨233537799411912466819469753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155691866274608311212979835 233537799411912466819469753)
  ·
    refine ⟨175153349558934350114602315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233537799411912466819469753 175153349558934350114602315)
    ·
      refine ⟨262730024338401525171903473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175153349558934350114602315 262730024338401525171903473)
      ·
        refine ⟨197047518253801143878927605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262730024338401525171903473 197047518253801143878927605)
        ·
          refine ⟨18473204836293857238649463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197047518253801143878927605 18473204836293857238649463)
          ·
            refine ⟨27709807254440785857974195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18473204836293857238649463 27709807254440785857974195)
            ·
              refine ⟨41564710881661178786961293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27709807254440785857974195 41564710881661178786961293)
              ·
                refine ⟨15586766580622942045110485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41564710881661178786961293 15586766580622942045110485)
                ·
                  refine ⟨365314841733350204182277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15586766580622942045110485 365314841733350204182277)
                  ·
                    rfl

theorem cell23_6403033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_6403033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403033 prefixEnd_6403033 := by exact prefixLift 6403033
  have htrace : WordTrace (prefixWord ++ tailWord_6403033) baseStart_6403033 baseEnd_6403033 := by
    simpa [prefixWord, tailWord_6403033, baseEnd_6403033] using wordTrace_append hprefix tailTrace_6403033
  have hstable : (prefixWord ++ tailWord_6403033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403033).length < 2 ^ (prefixWord ++ tailWord_6403033).sum := by decide
  have hdescent : baseEnd_6403033 < baseStart_6403033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403080 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_6403080 : Nat := 118140960795 + 6403080 * 2 ^ 59
def prefixEnd_6403080 : Nat := 4983230072969 + 3 ^ 40 * 6403080 * 2
def baseEnd_6403080 : Nat := 1095952569730304384584259

theorem tailTrace_6403080 : CollatzResearch.WordTrace tailWord_6403080 prefixEnd_6403080 1095952569730304384584259 := by
  unfold tailWord_6403080
  simp only [CollatzResearch.WordTrace]
  refine ⟨116769756821371096923215347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155693009095161462564287129 116769756821371096923215347)
  ·
    refine ⟨175154635232056645384823021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116769756821371096923215347 175154635232056645384823021)
    ·
      refine ⟨65682988212021242019308633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175154635232056645384823021 65682988212021242019308633)
      ·
        refine ⟨49262241159015931514481475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65682988212021242019308633 49262241159015931514481475)
        ·
          refine ⟨73893361738523897271722213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49262241159015931514481475 73893361738523897271722213)
          ·
            refine ⟨13855005325973230738447915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73893361738523897271722213 13855005325973230738447915)
            ·
              refine ⟨20782507988959846107671873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13855005325973230738447915 20782507988959846107671873)
              ·
                refine ⟨15586880991719884580753905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20782507988959846107671873 15586880991719884580753905)
                ·
                  refine ⟨11690160743789913435565429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15586880991719884580753905 11690160743789913435565429)
                  ·
                    refine ⟨1095952569730304384584259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11690160743789913435565429 1095952569730304384584259)
                    ·
                      rfl

theorem cell23_6403080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_6403080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403080 prefixEnd_6403080 := by exact prefixLift 6403080
  have htrace : WordTrace (prefixWord ++ tailWord_6403080) baseStart_6403080 baseEnd_6403080 := by
    simpa [prefixWord, tailWord_6403080, baseEnd_6403080] using wordTrace_append hprefix tailTrace_6403080
  have hstable : (prefixWord ++ tailWord_6403080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403080).length < 2 ^ (prefixWord ++ tailWord_6403080).sum := by decide
  have hdescent : baseEnd_6403080 < baseStart_6403080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403127 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 1, 4]
def baseStart_6403127 : Nat := 118140960795 + 6403127 * 2 ^ 59
def prefixEnd_6403127 : Nat := 4983230072969 + 3 ^ 40 * 6403127 * 2
def baseEnd_6403127 : Nat := 1095960614260558156621687

theorem tailTrace_6403127 : CollatzResearch.WordTrace tailWord_6403127 prefixEnd_6403127 1095960614260558156621687 := by
  unfold tailWord_6403127
  simp only [CollatzResearch.WordTrace]
  refine ⟨233541227873571920873391635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155694151915714613915594423 233541227873571920873391635)
  ·
    refine ⟨350311841810357881310087453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233541227873571920873391635 350311841810357881310087453)
    ·
      refine ⟨131366940678884205491282795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350311841810357881310087453 131366940678884205491282795)
      ·
        refine ⟨197050411018326308236924193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131366940678884205491282795 197050411018326308236924193)
        ·
          refine ⟨147787808263744731177693145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197050411018326308236924193 147787808263744731177693145)
          ·
            refine ⟨110840856197808548383269859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147787808263744731177693145 110840856197808548383269859)
            ·
              refine ⟨166261284296712822574904789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110840856197808548383269859 166261284296712822574904789)
              ·
                refine ⟨3896748850704206779099331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166261284296712822574904789 3896748850704206779099331)
                ·
                  refine ⟨5845123276056310168648997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896748850704206779099331 5845123276056310168648997)
                  ·
                    refine ⟨1095960614260558156621687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5845123276056310168648997 1095960614260558156621687)
                    ·
                      rfl

theorem cell23_6403127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_6403127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403127 prefixEnd_6403127 := by exact prefixLift 6403127
  have htrace : WordTrace (prefixWord ++ tailWord_6403127) baseStart_6403127 baseEnd_6403127 := by
    simpa [prefixWord, tailWord_6403127, baseEnd_6403127] using wordTrace_append hprefix tailTrace_6403127
  have hstable : (prefixWord ++ tailWord_6403127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403127).length < 2 ^ (prefixWord ++ tailWord_6403127).sum := by decide
  have hdescent : baseEnd_6403127 < baseStart_6403127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403167 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 3]
def baseStart_6403167 : Nat := 118140960795 + 6403167 * 2 ^ 59
def prefixEnd_6403167 : Nat := 4983230072969 + 3 ^ 40 * 6403167 * 2
def baseEnd_6403167 : Nat := 3287902382007854313364877

theorem tailTrace_6403167 : CollatzResearch.WordTrace tailWord_6403167 prefixEnd_6403167 3287902382007854313364877 := by
  unfold tailWord_6403167
  simp only [CollatzResearch.WordTrace]
  refine ⟨233542686793427007704847755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155695124528951338469898503 233542686793427007704847755)
  ·
    refine ⟨350314030190140511557271633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233542686793427007704847755 350314030190140511557271633)
    ·
      refine ⟨262735522642605383667953725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350314030190140511557271633 262735522642605383667953725)
      ·
        refine ⟨98525820990977018875482647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262735522642605383667953725 98525820990977018875482647)
        ·
          refine ⟨147788731486465528313223971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98525820990977018875482647 147788731486465528313223971)
          ·
            refine ⟨221683097229698292469835957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147788731486465528313223971 221683097229698292469835957)
            ·
              refine ⟨20782790365284214919047121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221683097229698292469835957 20782790365284214919047121)
              ·
                refine ⟨15587092773963161189285341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20782790365284214919047121 15587092773963161189285341)
                ·
                  refine ⟨5845159790236185445982003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15587092773963161189285341 5845159790236185445982003)
                  ·
                    refine ⟨8767739685354278168973005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5845159790236185445982003 8767739685354278168973005)
                    ·
                      refine ⟨3287902382007854313364877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767739685354278168973005 3287902382007854313364877)
                      ·
                        rfl

theorem cell23_6403167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_6403167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403167 prefixEnd_6403167 := by exact prefixLift 6403167
  have htrace : WordTrace (prefixWord ++ tailWord_6403167) baseStart_6403167 baseEnd_6403167 := by
    simpa [prefixWord, tailWord_6403167, baseEnd_6403167] using wordTrace_append hprefix tailTrace_6403167
  have hstable : (prefixWord ++ tailWord_6403167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403167).length < 2 ^ (prefixWord ++ tailWord_6403167).sum := by decide
  have hdescent : baseEnd_6403167 < baseStart_6403167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403177 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 1, 5, 2]
def baseStart_6403177 : Nat := 118140960795 + 6403177 * 2 ^ 59
def prefixEnd_6403177 : Nat := 4983230072969 + 3 ^ 40 * 6403177 * 2
def baseEnd_6403177 : Nat := 3287907516814399274239831

theorem tailTrace_6403177 : CollatzResearch.WordTrace tailWord_6403177 prefixEnd_6403177 3287907516814399274239831 := by
  unfold tailWord_6403177
  simp only [CollatzResearch.WordTrace]
  refine ⟨233543051523390779412711785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155695367682260519608474523 233543051523390779412711785)
  ·
    refine ⟨175157288642543084559533839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233543051523390779412711785 175157288642543084559533839)
    ·
      refine ⟨262735932963814626839300759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175157288642543084559533839 262735932963814626839300759)
      ·
        refine ⟨394103899445721940258951139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262735932963814626839300759 394103899445721940258951139)
        ·
          refine ⟨591155849168582910388426709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394103899445721940258951139 591155849168582910388426709)
          ·
            refine ⟨13855215214888661962228751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 591155849168582910388426709 13855215214888661962228751)
            ·
              refine ⟨20782822822332992943343127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13855215214888661962228751 20782822822332992943343127)
              ·
                refine ⟨31174234233499489415014691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20782822822332992943343127 31174234233499489415014691)
                ·
                  refine ⟨46761351350249234122522037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31174234233499489415014691 46761351350249234122522037)
                  ·
                    refine ⟨4383876689085865698986441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46761351350249234122522037 4383876689085865698986441)
                    ·
                      refine ⟨3287907516814399274239831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383876689085865698986441 3287907516814399274239831)
                      ·
                        rfl

theorem cell23_6403177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 5, 2].length) (baseStart_6403177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403177 prefixEnd_6403177 := by exact prefixLift 6403177
  have htrace : WordTrace (prefixWord ++ tailWord_6403177) baseStart_6403177 baseEnd_6403177 := by
    simpa [prefixWord, tailWord_6403177, baseEnd_6403177] using wordTrace_append hprefix tailTrace_6403177
  have hstable : (prefixWord ++ tailWord_6403177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403177).length < 2 ^ (prefixWord ++ tailWord_6403177).sum := by decide
  have hdescent : baseEnd_6403177 < baseStart_6403177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403201 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_6403201 : Nat := 118140960795 + 6403201 * 2 ^ 59
def prefixEnd_6403201 : Nat := 4983230072969 + 3 ^ 40 * 6403201 * 2
def baseEnd_6403201 : Nat := 3287919840350107180339721

theorem tailTrace_6403201 : CollatzResearch.WordTrace tailWord_6403201 prefixEnd_6403201 3287919840350107180339721 := by
  unfold tailWord_6403201
  simp only [CollatzResearch.WordTrace]
  refine ⟨233543926875303831511585457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155695951250202554341056971 233543926875303831511585457)
  ·
    refine ⟨175157945156477873633689093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233543926875303831511585457 175157945156477873633689093)
    ·
      refine ⟨32842114716839601306316705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175157945156477873633689093 32842114716839601306316705)
      ·
        refine ⟨24631586037629700979737529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32842114716839601306316705 24631586037629700979737529)
        ·
          refine ⟨18473689528222275734803147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24631586037629700979737529 18473689528222275734803147)
          ·
            refine ⟨27710534292333413602204721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18473689528222275734803147 27710534292333413602204721)
            ·
              refine ⟨20782900719250060201653541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27710534292333413602204721 20782900719250060201653541)
              ·
                refine ⟨3896793884859386287810039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20782900719250060201653541 3896793884859386287810039)
                ·
                  refine ⟨5845190827289079431715059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896793884859386287810039 5845190827289079431715059)
                  ·
                    refine ⟨8767786240933619147572589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5845190827289079431715059 8767786240933619147572589)
                    ·
                      refine ⟨3287919840350107180339721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767786240933619147572589 3287919840350107180339721)
                      ·
                        rfl

theorem cell23_6403201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_6403201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403201 prefixEnd_6403201 := by exact prefixLift 6403201
  have htrace : WordTrace (prefixWord ++ tailWord_6403201) baseStart_6403201 baseEnd_6403201 := by
    simpa [prefixWord, tailWord_6403201, baseEnd_6403201] using wordTrace_append hprefix tailTrace_6403201
  have hstable : (prefixWord ++ tailWord_6403201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403201).length < 2 ^ (prefixWord ++ tailWord_6403201).sum := by decide
  have hdescent : baseEnd_6403201 < baseStart_6403201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403224 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6403224 : Nat := 118140960795 + 6403224 * 2 ^ 59
def prefixEnd_6403224 : Nat := 4983230072969 + 3 ^ 40 * 6403224 * 2
def baseEnd_6403224 : Nat := 3287931650405160590352115

theorem tailTrace_6403224 : CollatzResearch.WordTrace tailWord_6403224 prefixEnd_6403224 3287931650405160590352115 := by
  unfold tailWord_6403224
  simp only [CollatzResearch.WordTrace]
  refine ⟨116772382877110253219836363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155696510502813670959781817 116772382877110253219836363)
  ·
    refine ⟨175158574315665379829754545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116772382877110253219836363 175158574315665379829754545)
    ·
      refine ⟨131368930736749034872315909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175158574315665379829754545 131368930736749034872315909)
      ·
        refine ⟨24631674513140444038559233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131368930736749034872315909 24631674513140444038559233)
        ·
          refine ⟨18473755884855333028919425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24631674513140444038559233 18473755884855333028919425)
          ·
            refine ⟨13855316913641499771689569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18473755884855333028919425 13855316913641499771689569)
            ·
              refine ⟨10391487685231124828767177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13855316913641499771689569 10391487685231124828767177)
              ·
                refine ⟨7793615763923343621575383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10391487685231124828767177 7793615763923343621575383)
                ·
                  refine ⟨11690423645885015432363075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793615763923343621575383 11690423645885015432363075)
                  ·
                    refine ⟨17535635468827523148544613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11690423645885015432363075 17535635468827523148544613)
                    ·
                      refine ⟨3287931650405160590352115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17535635468827523148544613 3287931650405160590352115)
                      ·
                        rfl

theorem cell23_6403224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6403224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403224 prefixEnd_6403224 := by exact prefixLift 6403224
  have htrace : WordTrace (prefixWord ++ tailWord_6403224) baseStart_6403224 baseEnd_6403224 := by
    simpa [prefixWord, tailWord_6403224, baseEnd_6403224] using wordTrace_append hprefix tailTrace_6403224
  have hstable : (prefixWord ++ tailWord_6403224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403224).length < 2 ^ (prefixWord ++ tailWord_6403224).sum := by decide
  have hdescent : baseEnd_6403224 < baseStart_6403224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403268 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6403268 : Nat := 118140960795 + 6403268 * 2 ^ 59
def prefixEnd_6403268 : Nat := 4983230072969 + 3 ^ 40 * 6403268 * 2
def baseEnd_6403268 : Nat := 1095984747851319472733971

theorem tailTrace_6403268 : CollatzResearch.WordTrace tailWord_6403268 prefixEnd_6403268 1095984747851319472733971 := by
  unfold tailWord_6403268
  simp only [CollatzResearch.WordTrace]
  refine ⟨116773185283030550977137229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155697580377374067969516305 116773185283030550977137229)
  ·
    refine ⟨43789944481136456616426461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116773185283030550977137229 43789944481136456616426461)
    ·
      refine ⟨16421229180426171231159923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43789944481136456616426461 16421229180426171231159923)
      ·
        refine ⟨24631843770639256846739885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16421229180426171231159923 24631843770639256846739885)
        ·
          refine ⟨9236941413989721317527457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24631843770639256846739885 9236941413989721317527457)
          ·
            refine ⟨6927706060492290988145593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9236941413989721317527457 6927706060492290988145593)
            ·
              refine ⟨5195779545369218241109195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927706060492290988145593 5195779545369218241109195)
              ·
                refine ⟨7793669318053827361663793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195779545369218241109195 7793669318053827361663793)
                ·
                  refine ⟨5845251988540370521247845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7793669318053827361663793 5845251988540370521247845)
                  ·
                    refine ⟨1095984747851319472733971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5845251988540370521247845 1095984747851319472733971)
                    ·
                      rfl

theorem cell23_6403268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6403268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403268 prefixEnd_6403268 := by exact prefixLift 6403268
  have htrace : WordTrace (prefixWord ++ tailWord_6403268) baseStart_6403268 baseEnd_6403268 := by
    simpa [prefixWord, tailWord_6403268, baseEnd_6403268] using wordTrace_append hprefix tailTrace_6403268
  have hstable : (prefixWord ++ tailWord_6403268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403268).length < 2 ^ (prefixWord ++ tailWord_6403268).sum := by decide
  have hdescent : baseEnd_6403268 < baseStart_6403268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403278 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_6403278 : Nat := 118140960795 + 6403278 * 2 ^ 59
def prefixEnd_6403278 : Nat := 4983230072969 + 3 ^ 40 * 6403278 * 2
def baseEnd_6403278 : Nat := 3287959378360503379076867

theorem tailTrace_6403278 : CollatzResearch.WordTrace tailWord_6403278 prefixEnd_6403278 3287959378360503379076867 := by
  unfold tailWord_6403278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29193341912003109207767311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155697823530683249108092325 29193341912003109207767311)
  ·
    refine ⟨43790012868004663811650967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29193341912003109207767311 43790012868004663811650967)
    ·
      refine ⟨65685019302006995717476451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43790012868004663811650967 65685019302006995717476451)
      ·
        refine ⟨98527528953010493576214677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65685019302006995717476451 98527528953010493576214677)
        ·
          refine ⟨4618477919672366886385063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98527528953010493576214677 4618477919672366886385063)
          ·
            refine ⟨6927716879508550329577595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618477919672366886385063 6927716879508550329577595)
            ·
              refine ⟨10391575319262825494366393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927716879508550329577595 10391575319262825494366393)
              ·
                refine ⟨7793681489447119120774795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10391575319262825494366393 7793681489447119120774795)
                ·
                  refine ⟨11690522234170678681162193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793681489447119120774795 11690522234170678681162193)
                  ·
                    refine ⟨8767891675628009010871645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11690522234170678681162193 8767891675628009010871645)
                    ·
                      refine ⟨3287959378360503379076867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8767891675628009010871645 3287959378360503379076867)
                      ·
                        rfl

theorem cell23_6403278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_6403278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403278 prefixEnd_6403278 := by exact prefixLift 6403278
  have htrace : WordTrace (prefixWord ++ tailWord_6403278) baseStart_6403278 baseEnd_6403278 := by
    simpa [prefixWord, tailWord_6403278, baseEnd_6403278] using wordTrace_append hprefix tailTrace_6403278
  have hstable : (prefixWord ++ tailWord_6403278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403278).length < 2 ^ (prefixWord ++ tailWord_6403278).sum := by decide
  have hdescent : baseEnd_6403278 < baseStart_6403278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403290 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_6403290 : Nat := 118140960795 + 6403290 * 2 ^ 59
def prefixEnd_6403290 : Nat := 4983230072969 + 3 ^ 40 * 6403290 * 2
def baseEnd_6403290 : Nat := 1095988513376119110708937

theorem tailTrace_6403290 : CollatzResearch.WordTrace tailWord_6403290 prefixEnd_6403290 1095988513376119110708937 := by
  unfold tailWord_6403290
  simp only [CollatzResearch.WordTrace]
  refine ⟨58386793242995349927893831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155698115314654266474383549 58386793242995349927893831)
  ·
    refine ⟨87580189864493024891840747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58386793242995349927893831 87580189864493024891840747)
    ·
      refine ⟨131370284796739537337761121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87580189864493024891840747 131370284796739537337761121)
      ·
        refine ⟨98527713597554653003320841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131370284796739537337761121 98527713597554653003320841)
        ·
          refine ⟨73895785198165989752490631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98527713597554653003320841 73895785198165989752490631)
          ·
            refine ⟨110843677797248984628735947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73895785198165989752490631 110843677797248984628735947)
            ·
              refine ⟨166265516695873476943103921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110843677797248984628735947 166265516695873476943103921)
              ·
                refine ⟨124699137521905107707327941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166265516695873476943103921 124699137521905107707327941)
                ·
                  refine ⟨23381088285357207695123989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124699137521905107707327941 23381088285357207695123989)
                  ·
                    refine ⟨1095988513376119110708937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23381088285357207695123989 1095988513376119110708937)
                    ·
                      rfl

theorem cell23_6403290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_6403290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403290 prefixEnd_6403290 := by exact prefixLift 6403290
  have htrace : WordTrace (prefixWord ++ tailWord_6403290) baseStart_6403290 baseEnd_6403290 := by
    simpa [prefixWord, tailWord_6403290, baseEnd_6403290] using wordTrace_append hprefix tailTrace_6403290
  have hstable : (prefixWord ++ tailWord_6403290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403290).length < 2 ^ (prefixWord ++ tailWord_6403290).sum := by decide
  have hdescent : baseEnd_6403290 < baseStart_6403290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403327 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_6403327 : Nat := 118140960795 + 6403327 * 2 ^ 59
def prefixEnd_6403327 : Nat := 4983230072969 + 3 ^ 40 * 6403327 * 2
def baseEnd_6403327 : Nat := 3287984538912573687364141

theorem tailTrace_6403327 : CollatzResearch.WordTrace tailWord_6403327 prefixEnd_6403327 3287984538912573687364141 := by
  unfold tailWord_6403327
  simp only [CollatzResearch.WordTrace]
  refine ⟨233548522472847355030672235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155699014981898236687114823 233548522472847355030672235)
  ·
    refine ⟨350322783709271032546008353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233548522472847355030672235 350322783709271032546008353)
    ·
      refine ⟨262742087781953274409506265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350322783709271032546008353 262742087781953274409506265)
      ·
        refine ⟨197056565836464955807129699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262742087781953274409506265 197056565836464955807129699)
        ·
          refine ⟨295584848754697433710694549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197056565836464955807129699 295584848754697433710694549)
          ·
            refine ⟨13855539785376442205188807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 295584848754697433710694549 13855539785376442205188807)
            ·
              refine ⟨20783309678064663307783211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13855539785376442205188807 20783309678064663307783211)
              ·
                refine ⟨31174964517096994961674817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20783309678064663307783211 31174964517096994961674817)
                ·
                  refine ⟨23381223387822746221256113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31174964517096994961674817 23381223387822746221256113)
                  ·
                    refine ⟨17535917540867059665942085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23381223387822746221256113 17535917540867059665942085)
                    ·
                      refine ⟨3287984538912573687364141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17535917540867059665942085 3287984538912573687364141)
                      ·
                        rfl

theorem cell23_6403327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_6403327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403327 prefixEnd_6403327 := by exact prefixLift 6403327
  have htrace : WordTrace (prefixWord ++ tailWord_6403327) baseStart_6403327 baseEnd_6403327 := by
    simpa [prefixWord, tailWord_6403327, baseEnd_6403327] using wordTrace_append hprefix tailTrace_6403327
  have hstable : (prefixWord ++ tailWord_6403327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403327).length < 2 ^ (prefixWord ++ tailWord_6403327).sum := by decide
  have hdescent : baseEnd_6403327 < baseStart_6403327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403331 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 2, 2, 2]
def baseStart_6403331 : Nat := 118140960795 + 6403331 * 2 ^ 59
def prefixEnd_6403331 : Nat := 4983230072969 + 3 ^ 40 * 6403331 * 2
def baseEnd_6403331 : Nat := 3287986592835191671714123

theorem tailTrace_6403331 : CollatzResearch.WordTrace tailWord_6403331 prefixEnd_6403331 3287986592835191671714123 := by
  unfold tailWord_6403331
  simp only [CollatzResearch.WordTrace]
  refine ⟨233548668364832863713817847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155699112243221909142545231 233548668364832863713817847)
  ·
    refine ⟨350323002547249295570726771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233548668364832863713817847 350323002547249295570726771)
    ·
      refine ⟨525484503820873943356090157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350323002547249295570726771 525484503820873943356090157)
      ·
        refine ⟨197056688932827728758533809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525484503820873943356090157 197056688932827728758533809)
        ·
          refine ⟨147792516699620796568900357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197056688932827728758533809 147792516699620796568900357)
          ·
            refine ⟨27711096881178899356668817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147792516699620796568900357 27711096881178899356668817)
            ·
              refine ⟨20783322660884174517501613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27711096881178899356668817 20783322660884174517501613)
              ·
                refine ⟨7793745997831565444063105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20783322660884174517501613 7793745997831565444063105)
                ·
                  refine ⟨5845309498373674083047329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7793745997831565444063105 5845309498373674083047329)
                  ·
                    refine ⟨4383982123780255562285497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5845309498373674083047329 4383982123780255562285497)
                    ·
                      refine ⟨3287986592835191671714123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4383982123780255562285497 3287986592835191671714123)
                      ·
                        rfl

theorem cell23_6403331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_6403331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403331 prefixEnd_6403331 := by exact prefixLift 6403331
  have htrace : WordTrace (prefixWord ++ tailWord_6403331) baseStart_6403331 baseEnd_6403331 := by
    simpa [prefixWord, tailWord_6403331, baseEnd_6403331] using wordTrace_append hprefix tailTrace_6403331
  have hstable : (prefixWord ++ tailWord_6403331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403331).length < 2 ^ (prefixWord ++ tailWord_6403331).sum := by decide
  have hdescent : baseEnd_6403331 < baseStart_6403331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403354 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_6403354 : Nat := 118140960795 + 6403354 * 2 ^ 59
def prefixEnd_6403354 : Nat := 4983230072969 + 3 ^ 40 * 6403354 * 2
def baseEnd_6403354 : Nat := 365333155876693897969613

theorem tailTrace_6403354 : CollatzResearch.WordTrace tailWord_6403354 prefixEnd_6403354 365333155876693897969613 := by
  unfold tailWord_6403354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58387376810937384660476279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155699671495833025761270077 58387376810937384660476279)
  ·
    refine ⟨87581065216406076990714419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58387376810937384660476279 87581065216406076990714419)
    ·
      refine ⟨131371597824609115486071629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87581065216406076990714419 131371597824609115486071629)
      ·
        refine ⟨49264349184228418307276861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131371597824609115486071629 49264349184228418307276861)
        ·
          refine ⟨18474130944085656865228823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49264349184228418307276861 18474130944085656865228823)
          ·
            refine ⟨27711196416128485297843235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18474130944085656865228823 27711196416128485297843235)
            ·
              refine ⟨41566794624192727946764853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27711196416128485297843235 41566794624192727946764853)
              ·
                refine ⟨3896886996018068245009205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41566794624192727946764853 3896886996018068245009205)
                ·
                  refine ⟨365333155876693897969613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896886996018068245009205 365333155876693897969613)
                  ·
                    rfl

theorem cell23_6403354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_6403354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403354 prefixEnd_6403354 := by exact prefixLift 6403354
  have htrace : WordTrace (prefixWord ++ tailWord_6403354) baseStart_6403354 baseEnd_6403354 := by
    simpa [prefixWord, tailWord_6403354, baseEnd_6403354] using wordTrace_append hprefix tailTrace_6403354
  have hstable : (prefixWord ++ tailWord_6403354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403354).length < 2 ^ (prefixWord ++ tailWord_6403354).sum := by decide
  have hdescent : baseEnd_6403354 < baseStart_6403354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403382 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6403382 : Nat := 118140960795 + 6403382 * 2 ^ 59
def prefixEnd_6403382 : Nat := 4983230072969 + 3 ^ 40 * 6403382 * 2
def baseEnd_6403382 : Nat := 3288012780348570972176389

theorem tailTrace_6403382 : CollatzResearch.WordTrace tailWord_6403382 prefixEnd_6403382 3288012780348570972176389 := by
  unfold tailWord_6403382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596908030478006213995275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155700352325098732949282933 14596908030478006213995275)
  ·
    refine ⟨21895362045717009320992913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14596908030478006213995275 21895362045717009320992913)
    ·
      refine ⟨16421521534287756990744685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21895362045717009320992913 16421521534287756990744685)
      ·
        refine ⟨6158070575357908871529257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16421521534287756990744685 6158070575357908871529257)
        ·
          refine ⟨4618552931518431653646943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6158070575357908871529257 4618552931518431653646943)
          ·
            refine ⟨6927829397277647480470415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618552931518431653646943 6927829397277647480470415)
            ·
              refine ⟨10391744095916471220705623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927829397277647480470415 10391744095916471220705623)
              ·
                refine ⟨15587616143874706831058435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10391744095916471220705623 15587616143874706831058435)
                ·
                  refine ⟨23381424215812060246587653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15587616143874706831058435 23381424215812060246587653)
                  ·
                    refine ⟨4384017040464761296235185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23381424215812060246587653 4384017040464761296235185)
                    ·
                      refine ⟨3288012780348570972176389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384017040464761296235185 3288012780348570972176389)
                      ·
                        rfl

theorem cell23_6403382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6403382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403382 prefixEnd_6403382 := by exact prefixLift 6403382
  have htrace : WordTrace (prefixWord ++ tailWord_6403382) baseStart_6403382 baseEnd_6403382 := by
    simpa [prefixWord, tailWord_6403382, baseEnd_6403382] using wordTrace_append hprefix tailTrace_6403382
  have hstable : (prefixWord ++ tailWord_6403382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403382).length < 2 ^ (prefixWord ++ tailWord_6403382).sum := by decide
  have hdescent : baseEnd_6403382 < baseStart_6403382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403405 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6403405 : Nat := 118140960795 + 6403405 * 2 ^ 59
def prefixEnd_6403405 : Nat := 4983230072969 + 3 ^ 40 * 6403405 * 2
def baseEnd_6403405 : Nat := 365336065600402709132087

theorem tailTrace_6403405 : CollatzResearch.WordTrace tailWord_6403405 prefixEnd_6403405 365336065600402709132087 := by
  unfold tailWord_6403405
  simp only [CollatzResearch.WordTrace]
  refine ⟨233551367366564774352011669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155700911577709849568007779 233551367366564774352011669)
  ·
    refine ⟨10947720345307723797750547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 233551367366564774352011669 10947720345307723797750547)
    ·
      refine ⟨16421580517961585696625821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10947720345307723797750547 16421580517961585696625821)
      ·
        refine ⟨6158092694235594636234683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16421580517961585696625821 6158092694235594636234683)
        ·
          refine ⟨9237139041353391954352025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6158092694235594636234683 9237139041353391954352025)
          ·
            refine ⟨6927854281015043965764019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9237139041353391954352025 6927854281015043965764019)
            ·
              refine ⟨10391781421522565948646029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927854281015043965764019 10391781421522565948646029)
              ·
                refine ⟨3896918033070962230742261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10391781421522565948646029 3896918033070962230742261)
                ·
                  refine ⟨365336065600402709132087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896918033070962230742261 365336065600402709132087)
                  ·
                    rfl

theorem cell23_6403405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6403405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403405 prefixEnd_6403405 := by exact prefixLift 6403405
  have htrace : WordTrace (prefixWord ++ tailWord_6403405) baseStart_6403405 baseEnd_6403405 := by
    simpa [prefixWord, tailWord_6403405, baseEnd_6403405] using wordTrace_append hprefix tailTrace_6403405
  have hstable : (prefixWord ++ tailWord_6403405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403405).length < 2 ^ (prefixWord ++ tailWord_6403405).sum := by decide
  have hdescent : baseEnd_6403405 < baseStart_6403405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403424 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_6403424 : Nat := 118140960795 + 6403424 * 2 ^ 59
def prefixEnd_6403424 : Nat := 4983230072969 + 3 ^ 40 * 6403424 * 2
def baseEnd_6403424 : Nat := 3288034346536059807851195

theorem tailTrace_6403424 : CollatzResearch.WordTrace tailWord_6403424 prefixEnd_6403424 3288034346536059807851195 := by
  unfold tailWord_6403424
  simp only [CollatzResearch.WordTrace]
  refine ⟨116776030176747970298476663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155701373568997293731302217 116776030176747970298476663)
  ·
    refine ⟨175164045265121955447714995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116776030176747970298476663 175164045265121955447714995)
    ·
      refine ⟨262746067897682933171572493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175164045265121955447714995 262746067897682933171572493)
      ·
        refine ⟨98529775461631099939339685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262746067897682933171572493 98529775461631099939339685)
        ·
          refine ⟨18474332899055831238626191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98529775461631099939339685 18474332899055831238626191)
          ·
            refine ⟨27711499348583746857939287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18474332899055831238626191 27711499348583746857939287)
            ·
              refine ⟨41567249022875620286908931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27711499348583746857939287 41567249022875620286908931)
              ·
                refine ⟨62350873534313430430363397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41567249022875620286908931 62350873534313430430363397)
                ·
                  refine ⟨11690788787683768205693137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62350873534313430430363397 11690788787683768205693137)
                  ·
                    refine ⟨8768091590762826154269853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11690788787683768205693137 8768091590762826154269853)
                    ·
                      refine ⟨3288034346536059807851195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8768091590762826154269853 3288034346536059807851195)
                      ·
                        rfl

theorem cell23_6403424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_6403424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403424 prefixEnd_6403424 := by exact prefixLift 6403424
  have htrace : WordTrace (prefixWord ++ tailWord_6403424) baseStart_6403424 baseEnd_6403424 := by
    simpa [prefixWord, tailWord_6403424, baseEnd_6403424] using wordTrace_append hprefix tailTrace_6403424
  have hstable : (prefixWord ++ tailWord_6403424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403424).length < 2 ^ (prefixWord ++ tailWord_6403424).sum := by decide
  have hdescent : baseEnd_6403424 < baseStart_6403424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403427 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 8]
def baseStart_6403427 : Nat := 118140960795 + 6403427 * 2 ^ 59
def prefixEnd_6403427 : Nat := 4983230072969 + 3 ^ 40 * 6403427 * 2
def baseEnd_6403427 : Nat := 365337320775335921790409

theorem tailTrace_6403427 : CollatzResearch.WordTrace tailWord_6403427 prefixEnd_6403427 365337320775335921790409 := by
  unfold tailWord_6403427
  simp only [CollatzResearch.WordTrace]
  refine ⟨233552169772485072109312535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155701446514990048072875023 233552169772485072109312535)
  ·
    refine ⟨350328254658727608163968803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233552169772485072109312535 350328254658727608163968803)
    ·
      refine ⟨525492381988091412245953205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350328254658727608163968803 525492381988091412245953205)
      ·
        refine ⟨49264910811383569898058113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 525492381988091412245953205 49264910811383569898058113)
        ·
          refine ⟨36948683108537677423543585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49264910811383569898058113 36948683108537677423543585)
          ·
            refine ⟨27711512331403258067657689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36948683108537677423543585 27711512331403258067657689)
            ·
              refine ⟨20783634248552443550743267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27711512331403258067657689 20783634248552443550743267)
              ·
                refine ⟨31175451372828665326114901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20783634248552443550743267 31175451372828665326114901)
                ·
                  refine ⟨365337320775335921790409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31175451372828665326114901 365337320775335921790409)
                  ·
                    rfl

theorem cell23_6403427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 8].length) (baseStart_6403427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403427 prefixEnd_6403427 := by exact prefixLift 6403427
  have htrace : WordTrace (prefixWord ++ tailWord_6403427) baseStart_6403427 baseEnd_6403427 := by
    simpa [prefixWord, tailWord_6403427, baseEnd_6403427] using wordTrace_append hprefix tailTrace_6403427
  have hstable : (prefixWord ++ tailWord_6403427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403427).length < 2 ^ (prefixWord ++ tailWord_6403427).sum := by decide
  have hdescent : baseEnd_6403427 < baseStart_6403427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403458 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_6403458 : Nat := 118140960795 + 6403458 * 2 ^ 59
def prefixEnd_6403458 : Nat := 4983230072969 + 3 ^ 40 * 6403458 * 2
def baseEnd_6403458 : Nat := 3288051804878312674826039

theorem tailTrace_6403458 : CollatzResearch.WordTrace tailWord_6403458 prefixEnd_6403458 3288051804878312674826039 := by
  unfold tailWord_6403458
  simp only [CollatzResearch.WordTrace]
  refine ⟨58388325108843191100922757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155702200290248509602460685 58388325108843191100922757)
  ·
    refine ⟨10947810957908098331423017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58388325108843191100922757 10947810957908098331423017)
    ·
      refine ⟨8210858218431073748567263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10947810957908098331423017 8210858218431073748567263)
      ·
        refine ⟨12316287327646610622850895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8210858218431073748567263 12316287327646610622850895)
        ·
          refine ⟨18474430991469915934276343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316287327646610622850895 18474430991469915934276343)
          ·
            refine ⟨27711646487204873901414515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18474430991469915934276343 27711646487204873901414515)
            ·
              refine ⟨41567469730807310852121773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27711646487204873901414515 41567469730807310852121773)
              ·
                refine ⟨15587801149052741569545665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41567469730807310852121773 15587801149052741569545665)
                ·
                  refine ⟨11690850861789556177159249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15587801149052741569545665 11690850861789556177159249)
                  ·
                    refine ⟨8768138146342167132869437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11690850861789556177159249 8768138146342167132869437)
                    ·
                      refine ⟨3288051804878312674826039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8768138146342167132869437 3288051804878312674826039)
                      ·
                        rfl

theorem cell23_6403458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_6403458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403458 prefixEnd_6403458 := by exact prefixLift 6403458
  have htrace : WordTrace (prefixWord ++ tailWord_6403458) baseStart_6403458 baseEnd_6403458 := by
    simpa [prefixWord, tailWord_6403458, baseEnd_6403458] using wordTrace_append hprefix tailTrace_6403458
  have hstable : (prefixWord ++ tailWord_6403458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403458).length < 2 ^ (prefixWord ++ tailWord_6403458).sum := by decide
  have hdescent : baseEnd_6403458 < baseStart_6403458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403481 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 2, 3, 2]
def baseStart_6403481 : Nat := 118140960795 + 6403481 * 2 ^ 59
def prefixEnd_6403481 : Nat := 4983230072969 + 3 ^ 40 * 6403481 * 2
def baseEnd_6403481 : Nat := 3288063614933366084838433

theorem tailTrace_6403481 : CollatzResearch.WordTrace tailWord_6403481 prefixEnd_6403481 3288063614933366084838433 := by
  unfold tailWord_6403481
  simp only [CollatzResearch.WordTrace]
  refine ⟨233554139314289439331778297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155702759542859626221185531 233554139314289439331778297)
  ·
    refine ⟨175165604485717079498833723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233554139314289439331778297 175165604485717079498833723)
    ·
      refine ⟨262748406728575619248250585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175165604485717079498833723 262748406728575619248250585)
      ·
        refine ⟨197061305046431714436187939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262748406728575619248250585 197061305046431714436187939)
        ·
          refine ⟨295591957569647571654281909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197061305046431714436187939 295591957569647571654281909)
          ·
            refine ⟨27711746022154459842588929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295591957569647571654281909 27711746022154459842588929)
            ·
              refine ⟨20783809516615844881941697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27711746022154459842588929 20783809516615844881941697)
              ·
                refine ⟨15587857137461883661456273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20783809516615844881941697 15587857137461883661456273)
                ·
                  refine ⟨11690892853096412746092205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15587857137461883661456273 11690892853096412746092205)
                  ·
                    refine ⟨4384084819911154779784577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11690892853096412746092205 4384084819911154779784577)
                    ·
                      refine ⟨3288063614933366084838433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384084819911154779784577 3288063614933366084838433)
                      ·
                        rfl

theorem cell23_6403481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_6403481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403481 prefixEnd_6403481 := by exact prefixLift 6403481
  have htrace : WordTrace (prefixWord ++ tailWord_6403481) baseStart_6403481 baseEnd_6403481 := by
    simpa [prefixWord, tailWord_6403481, baseEnd_6403481] using wordTrace_append hprefix tailTrace_6403481
  have hstable : (prefixWord ++ tailWord_6403481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403481).length < 2 ^ (prefixWord ++ tailWord_6403481).sum := by decide
  have hdescent : baseEnd_6403481 < baseStart_6403481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403488 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 1, 1, 3]
def baseStart_6403488 : Nat := 118140960795 + 6403488 * 2 ^ 59
def prefixEnd_6403488 : Nat := 4983230072969 + 3 ^ 40 * 6403488 * 2
def baseEnd_6403488 : Nat := 3288067209297947557450901

theorem tailTrace_6403488 : CollatzResearch.WordTrace tailWord_6403488 prefixEnd_6403488 3288067209297947557450901 := by
  unfold tailWord_6403488
  simp only [CollatzResearch.WordTrace]
  refine ⟨116777197312632039763641559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155702929750176053018188745 116777197312632039763641559)
  ·
    refine ⟨175165795968948059645462339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116777197312632039763641559 175165795968948059645462339)
    ·
      refine ⟨262748693953422089468193509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175165795968948059645462339 262748693953422089468193509)
      ·
        refine ⟨49265380116266641775286283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262748693953422089468193509 49265380116266641775286283)
        ·
          refine ⟨73898070174399962662929425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49265380116266641775286283 73898070174399962662929425)
          ·
            refine ⟨55423552630799971997197069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73898070174399962662929425 55423552630799971997197069)
            ·
              refine ⟨20783832236549989498948901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55423552630799971997197069 20783832236549989498948901)
              ·
                refine ⟨3896968544353123031052919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20783832236549989498948901 3896968544353123031052919)
                ·
                  refine ⟨5845452816529684546579379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896968544353123031052919 5845452816529684546579379)
                  ·
                    refine ⟨8768179224794526819869069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5845452816529684546579379 8768179224794526819869069)
                    ·
                      refine ⟨3288067209297947557450901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8768179224794526819869069 3288067209297947557450901)
                      ·
                        rfl

theorem cell23_6403488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_6403488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403488 prefixEnd_6403488 := by exact prefixLift 6403488
  have htrace : WordTrace (prefixWord ++ tailWord_6403488) baseStart_6403488 baseEnd_6403488 := by
    simpa [prefixWord, tailWord_6403488, baseEnd_6403488] using wordTrace_append hprefix tailTrace_6403488
  have hstable : (prefixWord ++ tailWord_6403488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403488).length < 2 ^ (prefixWord ++ tailWord_6403488).sum := by decide
  have hdescent : baseEnd_6403488 < baseStart_6403488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403507 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6]
def baseStart_6403507 : Nat := 118140960795 + 6403507 * 2 ^ 59
def prefixEnd_6403507 : Nat := 4983230072969 + 3 ^ 40 * 6403507 * 2
def baseEnd_6403507 : Nat := 3288076965430382983113313

theorem tailTrace_6403507 : CollatzResearch.WordTrace tailWord_6403507 prefixEnd_6403507 3288076965430382983113313 := by
  unfold tailWord_6403507
  simp only [CollatzResearch.WordTrace]
  refine ⟨233555087612195245772224775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155703391741463497181483183 233555087612195245772224775)
  ·
    refine ⟨350332631418292868658337163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233555087612195245772224775 350332631418292868658337163)
    ·
      refine ⟨525498947127439302987505745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350332631418292868658337163 525498947127439302987505745)
      ·
        refine ⟨394124210345579477240629309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525498947127439302987505745 394124210345579477240629309)
        ·
          refine ⟨147796578879592303965235991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394124210345579477240629309 147796578879592303965235991)
          ·
            refine ⟨221694868319388455947853987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147796578879592303965235991 221694868319388455947853987)
            ·
              refine ⟨332542302479082683921780981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221694868319388455947853987 332542302479082683921780981)
              ·
                refine ⟨31175840857414001617666967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332542302479082683921780981 31175840857414001617666967)
                ·
                  refine ⟨46763761286121002426500451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31175840857414001617666967 46763761286121002426500451)
                  ·
                    refine ⟨70145641929181503639750677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46763761286121002426500451 70145641929181503639750677)
                    ·
                      refine ⟨3288076965430382983113313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70145641929181503639750677 3288076965430382983113313)
                      ·
                        rfl

theorem cell23_6403507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_6403507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403507 prefixEnd_6403507 := by exact prefixLift 6403507
  have htrace : WordTrace (prefixWord ++ tailWord_6403507) baseStart_6403507 baseEnd_6403507 := by
    simpa [prefixWord, tailWord_6403507, baseEnd_6403507] using wordTrace_append hprefix tailTrace_6403507
  have hstable : (prefixWord ++ tailWord_6403507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403507).length < 2 ^ (prefixWord ++ tailWord_6403507).sum := by decide
  have hdescent : baseEnd_6403507 < baseStart_6403507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403537 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_6403537 : Nat := 118140960795 + 6403537 * 2 ^ 59
def prefixEnd_6403537 : Nat := 4983230072969 + 3 ^ 40 * 6403537 * 2
def baseEnd_6403537 : Nat := 3288092369850017865738175

theorem tailTrace_6403537 : CollatzResearch.WordTrace tailWord_6403537 prefixEnd_6403537 3288092369850017865738175 := by
  unfold tailWord_6403537
  simp only [CollatzResearch.WordTrace]
  refine ⟨233556181802086560895816865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155704121201391040597211243 233556181802086560895816865)
  ·
    refine ⟨175167136351564920671862649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233556181802086560895816865 175167136351564920671862649)
    ·
      refine ⟨131375352263673690503896987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175167136351564920671862649 131375352263673690503896987)
      ·
        refine ⟨197063028395510535755845481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131375352263673690503896987 197063028395510535755845481)
        ·
          refine ⟨147797271296632901816884111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197063028395510535755845481 147797271296632901816884111)
          ·
            refine ⟨221695906944949352725326167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147797271296632901816884111 221695906944949352725326167)
            ·
              refine ⟨332543860417424029087989251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221695906944949352725326167 332543860417424029087989251)
              ·
                refine ⟨498815790626136043631983877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332543860417424029087989251 498815790626136043631983877)
                ·
                  refine ⟨93527960742400508180996977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498815790626136043631983877 93527960742400508180996977)
                  ·
                    refine ⟨70145970556800381135747733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93527960742400508180996977 70145970556800381135747733)
                    ·
                      refine ⟨3288092369850017865738175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70145970556800381135747733 3288092369850017865738175)
                      ·
                        rfl

theorem cell23_6403537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_6403537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403537 prefixEnd_6403537 := by exact prefixLift 6403537
  have htrace : WordTrace (prefixWord ++ tailWord_6403537) baseStart_6403537 baseEnd_6403537 := by
    simpa [prefixWord, tailWord_6403537, baseEnd_6403537] using wordTrace_append hprefix tailTrace_6403537
  have hstable : (prefixWord ++ tailWord_6403537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403537).length < 2 ^ (prefixWord ++ tailWord_6403537).sum := by decide
  have hdescent : baseEnd_6403537 < baseStart_6403537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403544 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_6403544 : Nat := 118140960795 + 6403544 * 2 ^ 59
def prefixEnd_6403544 : Nat := 4983230072969 + 3 ^ 40 * 6403544 * 2
def baseEnd_6403544 : Nat := 3288095964214599338350643

theorem tailTrace_6403544 : CollatzResearch.WordTrace tailWord_6403544 prefixEnd_6403544 3288095964214599338350643 := by
  unfold tailWord_6403544
  simp only [CollatzResearch.WordTrace]
  refine ⟨116778218556530600545660843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155704291408707467394214457 116778218556530600545660843)
  ·
    refine ⟨175167327834795900818491265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116778218556530600545660843 175167327834795900818491265)
    ·
      refine ⟨131375495876096925613868449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175167327834795900818491265 131375495876096925613868449)
      ·
        refine ⟨98531621907072694210401337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131375495876096925613868449 98531621907072694210401337)
        ·
          refine ⟨73898716430304520657801003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98531621907072694210401337 73898716430304520657801003)
          ·
            refine ⟨110848074645456780986701505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73898716430304520657801003 110848074645456780986701505)
            ·
              refine ⟨83136055984092585740026129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110848074645456780986701505 83136055984092585740026129)
              ·
                refine ⟨62352041988069439305019597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83136055984092585740026129 62352041988069439305019597)
                ·
                  refine ⟨23382015745526039739382349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62352041988069439305019597 23382015745526039739382349)
                  ·
                    refine ⟨8768255904572264902268381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23382015745526039739382349 8768255904572264902268381)
                    ·
                      refine ⟨3288095964214599338350643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8768255904572264902268381 3288095964214599338350643)
                      ·
                        rfl

theorem cell23_6403544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_6403544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403544 prefixEnd_6403544 := by exact prefixLift 6403544
  have htrace : WordTrace (prefixWord ++ tailWord_6403544) baseStart_6403544 baseEnd_6403544 := by
    simpa [prefixWord, tailWord_6403544, baseEnd_6403544] using wordTrace_append hprefix tailTrace_6403544
  have hstable : (prefixWord ++ tailWord_6403544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403544).length < 2 ^ (prefixWord ++ tailWord_6403544).sum := by decide
  have hdescent : baseEnd_6403544 < baseStart_6403544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403545 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 1, 2, 2]
def baseStart_6403545 : Nat := 118140960795 + 6403545 * 2 ^ 59
def prefixEnd_6403545 : Nat := 4983230072969 + 3 ^ 40 * 6403545 * 2
def baseEnd_6403545 : Nat := 3288096477695253834438139

theorem tailTrace_6403545 : CollatzResearch.WordTrace tailWord_6403545 prefixEnd_6403545 3288096477695253834438139 := by
  unfold tailWord_6403545
  simp only [CollatzResearch.WordTrace]
  refine ⟨233556473586057578262108089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155704315724038385508072059 233556473586057578262108089)
  ·
    refine ⟨175167355189543183696581067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233556473586057578262108089 175167355189543183696581067)
    ·
      refine ⟨262751032784314775544871601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175167355189543183696581067 262751032784314775544871601)
      ·
        refine ⟨197063274588236081658653701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262751032784314775544871601 197063274588236081658653701)
        ·
          refine ⟨36949363985294265310997569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197063274588236081658653701 36949363985294265310997569)
          ·
            refine ⟨27712022988970698983248177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36949363985294265310997569 27712022988970698983248177)
            ·
              refine ⟨20784017241728024237436133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27712022988970698983248177 20784017241728024237436133)
              ·
                refine ⟨3897003232824004544519275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20784017241728024237436133 3897003232824004544519275)
                ·
                  refine ⟨5845504849236006816778913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897003232824004544519275 5845504849236006816778913)
                  ·
                    refine ⟨4384128636927005112584185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5845504849236006816778913 4384128636927005112584185)
                    ·
                      refine ⟨3288096477695253834438139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384128636927005112584185 3288096477695253834438139)
                      ·
                        rfl

theorem cell23_6403545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_6403545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403545 prefixEnd_6403545 := by exact prefixLift 6403545
  have htrace : WordTrace (prefixWord ++ tailWord_6403545) baseStart_6403545 baseEnd_6403545 := by
    simpa [prefixWord, tailWord_6403545, baseEnd_6403545] using wordTrace_append hprefix tailTrace_6403545
  have hstable : (prefixWord ++ tailWord_6403545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403545).length < 2 ^ (prefixWord ++ tailWord_6403545).sum := by decide
  have hdescent : baseEnd_6403545 < baseStart_6403545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403565 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6403565 : Nat := 118140960795 + 6403565 * 2 ^ 59
def prefixEnd_6403565 : Nat := 4983230072969 + 3 ^ 40 * 6403565 * 2
def baseEnd_6403565 : Nat := 3288106747308343756188047

theorem tailTrace_6403565 : CollatzResearch.WordTrace tailWord_6403565 prefixEnd_6403565 3288106747308343756188047 := by
  unfold tailWord_6403565
  simp only [CollatzResearch.WordTrace]
  refine ⟨233557203045985121677836149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155704802030656747785224099 233557203045985121677836149)
  ·
    refine ⟨21895987785561105157297139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233557203045985121677836149 21895987785561105157297139)
    ·
      refine ⟨32843981678341657735945709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21895987785561105157297139 32843981678341657735945709)
      ·
        refine ⟨12316493129378121650979641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32843981678341657735945709 12316493129378121650979641)
        ·
          refine ⟨9237369847033591238234731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12316493129378121650979641 9237369847033591238234731)
          ·
            refine ⟨13856054770550386857352097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9237369847033591238234731 13856054770550386857352097)
            ·
              refine ⟨10392041077912790143014073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13856054770550386857352097 10392041077912790143014073)
              ·
                refine ⟨7794030808434592607260555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10392041077912790143014073 7794030808434592607260555)
                ·
                  refine ⟨11691046212651888910890833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7794030808434592607260555 11691046212651888910890833)
                  ·
                    refine ⟨8768284659488916683168125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11691046212651888910890833 8768284659488916683168125)
                    ·
                      refine ⟨3288106747308343756188047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8768284659488916683168125 3288106747308343756188047)
                      ·
                        rfl

theorem cell23_6403565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6403565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403565 prefixEnd_6403565 := by exact prefixLift 6403565
  have htrace : WordTrace (prefixWord ++ tailWord_6403565) baseStart_6403565 baseEnd_6403565 := by
    simpa [prefixWord, tailWord_6403565, baseEnd_6403565] using wordTrace_append hprefix tailTrace_6403565
  have hstable : (prefixWord ++ tailWord_6403565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403565).length < 2 ^ (prefixWord ++ tailWord_6403565).sum := by decide
  have hdescent : baseEnd_6403565 < baseStart_6403565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403664 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_6403664 : Nat := 118140960795 + 6403664 * 2 ^ 59
def prefixEnd_6403664 : Nat := 4983230072969 + 3 ^ 40 * 6403664 * 2
def baseEnd_6403664 : Nat := 3288157581893138868850091

theorem tailTrace_6403664 : CollatzResearch.WordTrace tailWord_6403664 prefixEnd_6403664 3288157581893138868850091 := by
  unfold tailWord_6403664
  simp only [CollatzResearch.WordTrace]
  refine ⟨116780406936313230792845023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155707209248417641057126697 116780406936313230792845023)
  ·
    refine ⟨175170610404469846189267535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116780406936313230792845023 175170610404469846189267535)
    ·
      refine ⟨262755915606704769283901303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175170610404469846189267535 262755915606704769283901303)
      ·
        refine ⟨394133873410057153925851955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262755915606704769283901303 394133873410057153925851955)
        ·
          refine ⟨591200810115085730888777933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394133873410057153925851955 591200810115085730888777933)
          ·
            refine ⟨221700303793157149083291725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591200810115085730888777933 221700303793157149083291725)
            ·
              refine ⟨83137613922433930906234397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221700303793157149083291725 83137613922433930906234397)
              ·
                refine ⟨31176605220912724089837899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83137613922433930906234397 31176605220912724089837899)
                ·
                  refine ⟨46764907831369086134756849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31176605220912724089837899 46764907831369086134756849)
                  ·
                    refine ⟨35073680873526814601067637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46764907831369086134756849 35073680873526814601067637)
                    ·
                      refine ⟨3288157581893138868850091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35073680873526814601067637 3288157581893138868850091)
                      ·
                        rfl

theorem cell23_6403664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_6403664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403664 prefixEnd_6403664 := by exact prefixLift 6403664
  have htrace : WordTrace (prefixWord ++ tailWord_6403664) baseStart_6403664 baseEnd_6403664 := by
    simpa [prefixWord, tailWord_6403664, baseEnd_6403664] using wordTrace_append hprefix tailTrace_6403664
  have hstable : (prefixWord ++ tailWord_6403664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403664).length < 2 ^ (prefixWord ++ tailWord_6403664).sum := by decide
  have hdescent : baseEnd_6403664 < baseStart_6403664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403688 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6403688 : Nat := 118140960795 + 6403688 * 2 ^ 59
def prefixEnd_6403688 : Nat := 4983230072969 + 3 ^ 40 * 6403688 * 2
def baseEnd_6403688 : Nat := 1096056635142948924983327

theorem tailTrace_6403688 : CollatzResearch.WordTrace tailWord_6403688 prefixEnd_6403688 1096056635142948924983327 := by
  unfold tailWord_6403688
  simp only [CollatzResearch.WordTrace]
  refine ⟨116780844612269756842281859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155707792816359675789709145 116780844612269756842281859)
  ·
    refine ⟨175171266918404635263422789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116780844612269756842281859 175171266918404635263422789)
    ·
      refine ⟨32844612547200869111891773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175171266918404635263422789 32844612547200869111891773)
      ·
        refine ⟨12316729705200325916959415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32844612547200869111891773 12316729705200325916959415)
        ·
          refine ⟨18475094557800488875439123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316729705200325916959415 18475094557800488875439123)
          ·
            refine ⟨27712641836700733313158685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18475094557800488875439123 27712641836700733313158685)
            ·
              refine ⟨10392240688762774992434507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27712641836700733313158685 10392240688762774992434507)
              ·
                refine ⟨15588361033144162488651761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10392240688762774992434507 15588361033144162488651761)
                ·
                  refine ⟨11691270774858121866488821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15588361033144162488651761 11691270774858121866488821)
                  ·
                    refine ⟨1096056635142948924983327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11691270774858121866488821 1096056635142948924983327)
                    ·
                      rfl

theorem cell23_6403688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6403688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403688 prefixEnd_6403688 := by exact prefixLift 6403688
  have htrace : WordTrace (prefixWord ++ tailWord_6403688) baseStart_6403688 baseEnd_6403688 := by
    simpa [prefixWord, tailWord_6403688, baseEnd_6403688] using wordTrace_append hprefix tailTrace_6403688
  have hstable : (prefixWord ++ tailWord_6403688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403688).length < 2 ^ (prefixWord ++ tailWord_6403688).sum := by decide
  have hdescent : baseEnd_6403688 < baseStart_6403688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403741 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_6403741 : Nat := 118140960795 + 6403741 * 2 ^ 59
def prefixEnd_6403741 : Nat := 4983230072969 + 3 ^ 40 * 6403741 * 2
def baseEnd_6403741 : Nat := 3288197119903535067587237

theorem tailTrace_6403741 : CollatzResearch.WordTrace tailWord_6403741 prefixEnd_6403741 3288197119903535067587237 := by
  unfold tailWord_6403741
  simp only [CollatzResearch.WordTrace]
  refine ⟨233563622293347503736243077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155709081528898335824162051 233563622293347503736243077)
  ·
    refine ⟨43793179180002656950545577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233563622293347503736243077 43793179180002656950545577)
    ·
      refine ⟨32844884385001992712909183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43793179180002656950545577 32844884385001992712909183)
      ·
        refine ⟨49267326577502989069363775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32844884385001992712909183 49267326577502989069363775)
        ·
          refine ⟨73900989866254483604045663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49267326577502989069363775 73900989866254483604045663)
          ·
            refine ⟨110851484799381725406068495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73900989866254483604045663 110851484799381725406068495)
            ·
              refine ⟨166277227199072588109102743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110851484799381725406068495 166277227199072588109102743)
              ·
                refine ⟨249415840798608882163654115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166277227199072588109102743 249415840798608882163654115)
                ·
                  refine ⟨374123761197913323245481173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249415840798608882163654115 374123761197913323245481173)
                  ·
                    refine ⟨8768525653076093513565965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 374123761197913323245481173 8768525653076093513565965)
                    ·
                      refine ⟨3288197119903535067587237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8768525653076093513565965 3288197119903535067587237)
                      ·
                        rfl

theorem cell23_6403741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_6403741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403741 prefixEnd_6403741 := by exact prefixLift 6403741
  have htrace : WordTrace (prefixWord ++ tailWord_6403741) baseStart_6403741 baseEnd_6403741 := by
    simpa [prefixWord, tailWord_6403741, baseEnd_6403741] using wordTrace_append hprefix tailTrace_6403741
  have hstable : (prefixWord ++ tailWord_6403741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403741).length < 2 ^ (prefixWord ++ tailWord_6403741).sum := by decide
  have hdescent : baseEnd_6403741 < baseStart_6403741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403781 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_6403781 : Nat := 118140960795 + 6403781 * 2 ^ 59
def prefixEnd_6403781 : Nat := 4983230072969 + 3 ^ 40 * 6403781 * 2
def baseEnd_6403781 : Nat := 3288217659129714911087053

theorem tailTrace_6403781 : CollatzResearch.WordTrace tailWord_6403781 prefixEnd_6403781 3288217659129714911087053 := by
  unfold tailWord_6403781
  simp only [CollatzResearch.WordTrace]
  refine ⟨233565081213202590567699197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155710054142135060378466131 233565081213202590567699197)
  ·
    refine ⟨87586905454950971462887199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233565081213202590567699197 87586905454950971462887199)
    ·
      refine ⟨131380358182426457194330799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87586905454950971462887199 131380358182426457194330799)
      ·
        refine ⟨197070537273639685791496199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131380358182426457194330799 197070537273639685791496199)
        ·
          refine ⟨295605805910459528687244299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197070537273639685791496199 295605805910459528687244299)
          ·
            refine ⟨443408708865689293030866449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295605805910459528687244299 443408708865689293030866449)
            ·
              refine ⟨332556531649266969773149837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443408708865689293030866449 332556531649266969773149837)
              ·
                refine ⟨124708699368475113664931189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332556531649266969773149837 124708699368475113664931189)
                ·
                  refine ⟨11691440565794541906087299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124708699368475113664931189 11691440565794541906087299)
                  ·
                    refine ⟨17537160848691812859130949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11691440565794541906087299 17537160848691812859130949)
                    ·
                      refine ⟨3288217659129714911087053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17537160848691812859130949 3288217659129714911087053)
                      ·
                        rfl

theorem cell23_6403781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_6403781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403781 prefixEnd_6403781 := by exact prefixLift 6403781
  have htrace : WordTrace (prefixWord ++ tailWord_6403781) baseStart_6403781 baseEnd_6403781 := by
    simpa [prefixWord, tailWord_6403781, baseEnd_6403781] using wordTrace_append hprefix tailTrace_6403781
  have hstable : (prefixWord ++ tailWord_6403781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403781).length < 2 ^ (prefixWord ++ tailWord_6403781).sum := by decide
  have hdescent : baseEnd_6403781 < baseStart_6403781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403782 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_6403782 : Nat := 118140960795 + 6403782 * 2 ^ 59
def prefixEnd_6403782 : Nat := 4983230072969 + 3 ^ 40 * 6403782 * 2
def baseEnd_6403782 : Nat := 365357574734485489686061

theorem tailTrace_6403782 : CollatzResearch.WordTrace tailWord_6403782 prefixEnd_6403782 365357574734485489686061 := by
  unfold tailWord_6403782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298909927693717741827675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155710078457465978492323733 7298909927693717741827675)
  ·
    refine ⟨10948364891540576612741513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7298909927693717741827675 10948364891540576612741513)
    ·
      refine ⟨8211273668655432459556135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10948364891540576612741513 8211273668655432459556135)
      ·
        refine ⟨12316910502983148689334203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211273668655432459556135 12316910502983148689334203)
        ·
          refine ⟨18475365754474723034001305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316910502983148689334203 18475365754474723034001305)
          ·
            refine ⟨13856524315856042275500979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18475365754474723034001305 13856524315856042275500979)
            ·
              refine ⟨20784786473784063413251469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13856524315856042275500979 20784786473784063413251469)
              ·
                refine ⟨7794294927669023779969301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20784786473784063413251469 7794294927669023779969301)
                ·
                  refine ⟨365357574734485489686061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7794294927669023779969301 365357574734485489686061)
                  ·
                    rfl

theorem cell23_6403782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_6403782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403782 prefixEnd_6403782 := by exact prefixLift 6403782
  have htrace : WordTrace (prefixWord ++ tailWord_6403782) baseStart_6403782 baseEnd_6403782 := by
    simpa [prefixWord, tailWord_6403782, baseEnd_6403782] using wordTrace_append hprefix tailTrace_6403782
  have hstable : (prefixWord ++ tailWord_6403782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403782).length < 2 ^ (prefixWord ++ tailWord_6403782).sum := by decide
  have hdescent : baseEnd_6403782 < baseStart_6403782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403818 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_6403818 : Nat := 118140960795 + 6403818 * 2 ^ 59
def prefixEnd_6403818 : Nat := 4983230072969 + 3 ^ 40 * 6403818 * 2
def baseEnd_6403818 : Nat := 3288236657913931266324383

theorem tailTrace_6403818 : CollatzResearch.WordTrace tailWord_6403818 prefixEnd_6403818 3288236657913931266324383 := by
  unfold tailWord_6403818
  simp only [CollatzResearch.WordTrace]
  refine ⟨58391607678517136471699027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155710953809379030591197405 58391607678517136471699027)
  ·
    refine ⟨87587411517775704707548541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58391607678517136471699027 87587411517775704707548541)
    ·
      refine ⟨32845279319165889265330703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87587411517775704707548541 32845279319165889265330703)
      ·
        refine ⟨49267918978748833897996055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32845279319165889265330703 49267918978748833897996055)
        ·
          refine ⟨73901878468123250846994083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49267918978748833897996055 73901878468123250846994083)
          ·
            refine ⟨110852817702184876270491125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73901878468123250846994083 110852817702184876270491125)
            ·
              refine ⟨10392451659579832150358543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110852817702184876270491125 10392451659579832150358543)
              ·
                refine ⟨15588677489369748225537815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10392451659579832150358543 15588677489369748225537815)
                ·
                  refine ⟨23383016234054622338306723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15588677489369748225537815 23383016234054622338306723)
                  ·
                    refine ⟨35074524351081933507460085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23383016234054622338306723 35074524351081933507460085)
                    ·
                      refine ⟨3288236657913931266324383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35074524351081933507460085 3288236657913931266324383)
                      ·
                        rfl

theorem cell23_6403818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_6403818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403818 prefixEnd_6403818 := by exact prefixLift 6403818
  have htrace : WordTrace (prefixWord ++ tailWord_6403818) baseStart_6403818 baseEnd_6403818 := by
    simpa [prefixWord, tailWord_6403818, baseEnd_6403818] using wordTrace_append hprefix tailTrace_6403818
  have hstable : (prefixWord ++ tailWord_6403818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403818).length < 2 ^ (prefixWord ++ tailWord_6403818).sum := by decide
  have hdescent : baseEnd_6403818 < baseStart_6403818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403821 : List Nat := [1, 5, 1, 2, 1, 13]
def baseStart_6403821 : Nat := 118140960795 + 6403821 * 2 ^ 59
def prefixEnd_6403821 : Nat := 4983230072969 + 3 ^ 40 * 6403821 * 2
def baseEnd_6403821 : Nat := 13531844437678579236983

theorem tailTrace_6403821 : CollatzResearch.WordTrace tailWord_6403821 prefixEnd_6403821 13531844437678579236983 := by
  unfold tailWord_6403821
  simp only [CollatzResearch.WordTrace]
  refine ⟨233566540133057677399155317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155711026755371784932770211 233566540133057677399155317)
  ·
    refine ⟨21896863137474157256170811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233566540133057677399155317 21896863137474157256170811)
    ·
      refine ⟨32845294706211235884256217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21896863137474157256170811 32845294706211235884256217)
      ·
        refine ⟨24633971029658426913192163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32845294706211235884256217 24633971029658426913192163)
        ·
          refine ⟨36950956544487640369788245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24633971029658426913192163 36950956544487640369788245)
          ·
            refine ⟨13531844437678579236983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 36950956544487640369788245 13531844437678579236983)
            ·
              rfl

theorem cell23_6403821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 13].length) (baseStart_6403821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403821 prefixEnd_6403821 := by exact prefixLift 6403821
  have htrace : WordTrace (prefixWord ++ tailWord_6403821) baseStart_6403821 baseEnd_6403821 := by
    simpa [prefixWord, tailWord_6403821, baseEnd_6403821] using wordTrace_append hprefix tailTrace_6403821
  have hstable : (prefixWord ++ tailWord_6403821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403821).length < 2 ^ (prefixWord ++ tailWord_6403821).sum := by decide
  have hdescent : baseEnd_6403821 < baseStart_6403821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403825 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 2, 4]
def baseStart_6403825 : Nat := 118140960795 + 6403825 * 2 ^ 59
def prefixEnd_6403825 : Nat := 4983230072969 + 3 ^ 40 * 6403825 * 2
def baseEnd_6403825 : Nat := 1096080084092837579645617

theorem tailTrace_6403825 : CollatzResearch.WordTrace tailWord_6403825 prefixEnd_6403825 1096080084092837579645617 := by
  unfold tailWord_6403825
  simp only [CollatzResearch.WordTrace]
  refine ⟨233566686025043186082300929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155711124016695457388200619 233566686025043186082300929)
  ·
    refine ⟨175175014518782389561725697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233566686025043186082300929 175175014518782389561725697)
    ·
      refine ⟨131381260889086792171294273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175175014518782389561725697 131381260889086792171294273)
      ·
        refine ⟨98535945666815094128470705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131381260889086792171294273 98535945666815094128470705)
        ·
          refine ⟨73901959250111320596353029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98535945666815094128470705 73901959250111320596353029)
          ·
            refine ⟨13856617359395872611816193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73901959250111320596353029 13856617359395872611816193)
            ·
              refine ⟨10392463019546904458862145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13856617359395872611816193 10392463019546904458862145)
              ·
                refine ⟨7794347264660178344146609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10392463019546904458862145 7794347264660178344146609)
                ·
                  refine ⟨5845760448495133758109957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7794347264660178344146609 5845760448495133758109957)
                  ·
                    refine ⟨1096080084092837579645617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5845760448495133758109957 1096080084092837579645617)
                    ·
                      rfl

theorem cell23_6403825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_6403825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403825 prefixEnd_6403825 := by exact prefixLift 6403825
  have htrace : WordTrace (prefixWord ++ tailWord_6403825) baseStart_6403825 baseEnd_6403825 := by
    simpa [prefixWord, tailWord_6403825, baseEnd_6403825] using wordTrace_append hprefix tailTrace_6403825
  have hstable : (prefixWord ++ tailWord_6403825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403825).length < 2 ^ (prefixWord ++ tailWord_6403825).sum := by decide
  have hdescent : baseEnd_6403825 < baseStart_6403825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403841 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_6403841 : Nat := 118140960795 + 6403841 * 2 ^ 59
def prefixEnd_6403841 : Nat := 4983230072969 + 3 ^ 40 * 6403841 * 2
def baseEnd_6403841 : Nat := 3288248467968984676336777

theorem tailTrace_6403841 : CollatzResearch.WordTrace tailWord_6403841 prefixEnd_6403841 3288248467968984676336777 := by
  unfold tailWord_6403841
  simp only [CollatzResearch.WordTrace]
  refine ⟨233567269592985220814883377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155711513061990147209922251 233567269592985220814883377)
  ·
    refine ⟨175175452194738915611162533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233567269592985220814883377 175175452194738915611162533)
    ·
      refine ⟨32845397286513546677092975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175175452194738915611162533 32845397286513546677092975)
      ·
        refine ⟨49268095929770320015639463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32845397286513546677092975 49268095929770320015639463)
        ·
          refine ⟨73902143894655480023459195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49268095929770320015639463 73902143894655480023459195)
          ·
            refine ⟨110853215841983220035188793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73902143894655480023459195 110853215841983220035188793)
            ·
              refine ⟨83139911881487415026391595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110853215841983220035188793 83139911881487415026391595)
              ·
                refine ⟨124709867822231122539587393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83139911881487415026391595 124709867822231122539587393)
                ·
                  refine ⟨93532400866673341904690545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124709867822231122539587393 93532400866673341904690545)
                  ·
                    refine ⟨70149300650005006428517909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93532400866673341904690545 70149300650005006428517909)
                    ·
                      refine ⟨3288248467968984676336777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70149300650005006428517909 3288248467968984676336777)
                      ·
                        rfl

theorem cell23_6403841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_6403841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403841 prefixEnd_6403841 := by exact prefixLift 6403841
  have htrace : WordTrace (prefixWord ++ tailWord_6403841) baseStart_6403841 baseEnd_6403841 := by
    simpa [prefixWord, tailWord_6403841, baseEnd_6403841] using wordTrace_append hprefix tailTrace_6403841
  have hstable : (prefixWord ++ tailWord_6403841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403841).length < 2 ^ (prefixWord ++ tailWord_6403841).sum := by decide
  have hdescent : baseEnd_6403841 < baseStart_6403841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403888 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 8, 2]
def baseStart_6403888 : Nat := 118140960795 + 6403888 * 2 ^ 59
def prefixEnd_6403888 : Nat := 4983230072969 + 3 ^ 40 * 6403888 * 2
def baseEnd_6403888 : Nat := 3288272601559745992449061

theorem tailTrace_6403888 : CollatzResearch.WordTrace tailWord_6403888 prefixEnd_6403888 3288272601559745992449061 := by
  unfold tailWord_6403888
  simp only [CollatzResearch.WordTrace]
  refine ⟨116784491911907473920922159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155712655882543298561229545 116784491911907473920922159)
  ·
    refine ⟨175176737867861210881383239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116784491911907473920922159 175176737867861210881383239)
    ·
      refine ⟨262765106801791816322074859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175176737867861210881383239 262765106801791816322074859)
      ·
        refine ⟨394147660202687724483112289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262765106801791816322074859 394147660202687724483112289)
        ·
          refine ⟨295610745152015793362334217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394147660202687724483112289 295610745152015793362334217)
          ·
            refine ⟨221708058864011845021750663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295610745152015793362334217 221708058864011845021750663)
            ·
              refine ⟨332562088296017767532625995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221708058864011845021750663 332562088296017767532625995)
              ·
                refine ⟨498843132444026651298938993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332562088296017767532625995 498843132444026651298938993)
                ·
                  refine ⟨374132349333019988474204245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498843132444026651298938993 374132349333019988474204245)
                  ·
                    refine ⟨4384363468746327989932081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 374132349333019988474204245 4384363468746327989932081)
                    ·
                      refine ⟨3288272601559745992449061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384363468746327989932081 3288272601559745992449061)
                      ·
                        rfl

theorem cell23_6403888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 8, 2].length) (baseStart_6403888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403888 prefixEnd_6403888 := by exact prefixLift 6403888
  have htrace : WordTrace (prefixWord ++ tailWord_6403888) baseStart_6403888 baseEnd_6403888 := by
    simpa [prefixWord, tailWord_6403888, baseEnd_6403888] using wordTrace_append hprefix tailTrace_6403888
  have hstable : (prefixWord ++ tailWord_6403888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403888).length < 2 ^ (prefixWord ++ tailWord_6403888).sum := by decide
  have hdescent : baseEnd_6403888 < baseStart_6403888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403898 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_6403898 : Nat := 118140960795 + 6403898 * 2 ^ 59
def prefixEnd_6403898 : Nat := 4983230072969 + 3 ^ 40 * 6403898 * 2
def baseEnd_6403898 : Nat := 1096092578788763651108005

theorem tailTrace_6403898 : CollatzResearch.WordTrace tailWord_6403898 prefixEnd_6403898 1096092578788763651108005 := by
  unfold tailWord_6403898
  simp only [CollatzResearch.WordTrace]
  refine ⟨58392337138444679887427087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155712899035852479699805565 58392337138444679887427087)
  ·
    refine ⟨87588505707667019831140631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58392337138444679887427087 87588505707667019831140631)
    ·
      refine ⟨131382758561500529746710947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87588505707667019831140631 131382758561500529746710947)
      ·
        refine ⟨197074137842250794620066421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131382758561500529746710947 197074137842250794620066421)
        ·
          refine ⟨18475700422711011995631227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197074137842250794620066421 18475700422711011995631227)
          ·
            refine ⟨27713550634066517993446841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18475700422711011995631227 27713550634066517993446841)
            ·
              refine ⟨20785162975549888495085131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27713550634066517993446841 20785162975549888495085131)
              ·
                refine ⟨31177744463324832742627697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20785162975549888495085131 31177744463324832742627697)
                ·
                  refine ⟨23383308347493624556970773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31177744463324832742627697 23383308347493624556970773)
                  ·
                    refine ⟨1096092578788763651108005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23383308347493624556970773 1096092578788763651108005)
                    ·
                      rfl

theorem cell23_6403898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_6403898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403898 prefixEnd_6403898 := by exact prefixLift 6403898
  have htrace : WordTrace (prefixWord ++ tailWord_6403898) baseStart_6403898 baseEnd_6403898 := by
    simpa [prefixWord, tailWord_6403898, baseEnd_6403898] using wordTrace_append hprefix tailTrace_6403898
  have hstable : (prefixWord ++ tailWord_6403898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403898).length < 2 ^ (prefixWord ++ tailWord_6403898).sum := by decide
  have hdescent : baseEnd_6403898 < baseStart_6403898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403922 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_6403922 : Nat := 118140960795 + 6403922 * 2 ^ 59
def prefixEnd_6403922 : Nat := 4983230072969 + 3 ^ 40 * 6403922 * 2
def baseEnd_6403922 : Nat := 3288290059901998859423905

theorem tailTrace_6403922 : CollatzResearch.WordTrace tailWord_6403922 prefixEnd_6403922 3288290059901998859423905 := by
  unfold tailWord_6403922
  simp only [CollatzResearch.WordTrace]
  refine ⟨58392555976422942912145505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155713482603794514432388013 58392555976422942912145505)
  ·
    refine ⟨43794416982317207184109129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58392555976422942912145505 43794416982317207184109129)
    ·
      refine ⟨32845812736737905388081847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43794416982317207184109129 32845812736737905388081847)
      ·
        refine ⟨49268719105106858082122771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32845812736737905388081847 49268719105106858082122771)
        ·
          refine ⟨73903078657660287123184157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49268719105106858082122771 73903078657660287123184157)
          ·
            refine ⟨27713654496622607671194059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73903078657660287123184157 27713654496622607671194059)
            ·
              refine ⟨41570481744933911506791089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27713654496622607671194059 41570481744933911506791089)
              ·
                refine ⟨31177861308700433630093317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41570481744933911506791089 31177861308700433630093317)
                ·
                  refine ⟨5845848995381331305642497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31177861308700433630093317 5845848995381331305642497)
                  ·
                    refine ⟨4384386746535998479231873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5845848995381331305642497 4384386746535998479231873)
                    ·
                      refine ⟨3288290059901998859423905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384386746535998479231873 3288290059901998859423905)
                      ·
                        rfl

theorem cell23_6403922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_6403922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403922 prefixEnd_6403922 := by exact prefixLift 6403922
  have htrace : WordTrace (prefixWord ++ tailWord_6403922) baseStart_6403922 baseEnd_6403922 := by
    simpa [prefixWord, tailWord_6403922, baseEnd_6403922] using wordTrace_append hprefix tailTrace_6403922
  have hstable : (prefixWord ++ tailWord_6403922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403922).length < 2 ^ (prefixWord ++ tailWord_6403922).sum := by decide
  have hdescent : baseEnd_6403922 < baseStart_6403922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6403990 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6403990 : Nat := 118140960795 + 6403990 * 2 ^ 59
def prefixEnd_6403990 : Nat := 4983230072969 + 3 ^ 40 * 6403990 * 2
def baseEnd_6403990 : Nat := 3288324976586504593373593

theorem tailTrace_6403990 : CollatzResearch.WordTrace tailWord_6403990 prefixEnd_6403990 3288324976586504593373593 := by
  unfold tailWord_6403990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14598294004340338703878589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155715136046296946174704949 14598294004340338703878589)
  ·
    refine ⟨5474360251627627013954471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14598294004340338703878589 5474360251627627013954471)
    ·
      refine ⟨8211540377441440520931707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474360251627627013954471 8211540377441440520931707)
      ·
        refine ⟨12317310566162160781397561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211540377441440520931707 12317310566162160781397561)
        ·
          refine ⟨9237982924621620586048171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12317310566162160781397561 9237982924621620586048171)
          ·
            refine ⟨13856974386932430879072257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9237982924621620586048171 13856974386932430879072257)
            ·
              refine ⟨10392730790199323159304193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13856974386932430879072257 10392730790199323159304193)
              ·
                refine ⟨7794548092649492369478145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10392730790199323159304193 7794548092649492369478145)
                ·
                  refine ⟨5845911069487119277108609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7794548092649492369478145 5845911069487119277108609)
                  ·
                    refine ⟨4384433302115339457831457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5845911069487119277108609 4384433302115339457831457)
                    ·
                      refine ⟨3288324976586504593373593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384433302115339457831457 3288324976586504593373593)
                      ·
                        rfl

theorem cell23_6403990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6403990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6403990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6403990 prefixEnd_6403990 := by exact prefixLift 6403990
  have htrace : WordTrace (prefixWord ++ tailWord_6403990) baseStart_6403990 baseEnd_6403990 := by
    simpa [prefixWord, tailWord_6403990, baseEnd_6403990] using wordTrace_append hprefix tailTrace_6403990
  have hstable : (prefixWord ++ tailWord_6403990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6403990).length < 2 ^ (prefixWord ++ tailWord_6403990).sum := by decide
  have hdescent : baseEnd_6403990 < baseStart_6403990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6403990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404105 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_6404105 : Nat := 118140960795 + 6404105 * 2 ^ 59
def prefixEnd_6404105 : Nat := 4983230072969 + 3 ^ 40 * 6404105 * 2
def baseEnd_6404105 : Nat := 3288384026861771643435563

theorem tailTrace_6404105 : CollatzResearch.WordTrace tailWord_6404105 prefixEnd_6404105 3288384026861771643435563 := by
  unfold tailWord_6404105
  simp only [CollatzResearch.WordTrace]
  refine ⟨233576898464028793902493769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155717932309352529268329179 233576898464028793902493769)
  ·
    refine ⟨175182673848021595426870327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233576898464028793902493769 175182673848021595426870327)
    ·
      refine ⟨262774010772032393140305491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175182673848021595426870327 262774010772032393140305491)
      ·
        refine ⟨394161016158048589710458237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262774010772032393140305491 394161016158048589710458237)
        ·
          refine ⟨147810381059268221141421839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394161016158048589710458237 147810381059268221141421839)
          ·
            refine ⟨221715571588902331712132759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147810381059268221141421839 221715571588902331712132759)
            ·
              refine ⟨332573357383353497568199139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221715571588902331712132759 332573357383353497568199139)
              ·
                refine ⟨498860036075030246352298709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332573357383353497568199139 498860036075030246352298709)
                ·
                  refine ⟨11692032095508521398882001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 498860036075030246352298709 11692032095508521398882001)
                  ·
                    refine ⟨8769024071631391049161501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11692032095508521398882001 8769024071631391049161501)
                    ·
                      refine ⟨3288384026861771643435563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769024071631391049161501 3288384026861771643435563)
                      ·
                        rfl

theorem cell23_6404105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_6404105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404105 prefixEnd_6404105 := by exact prefixLift 6404105
  have htrace : WordTrace (prefixWord ++ tailWord_6404105) baseStart_6404105 baseEnd_6404105 := by
    simpa [prefixWord, tailWord_6404105, baseEnd_6404105] using wordTrace_append hprefix tailTrace_6404105
  have hstable : (prefixWord ++ tailWord_6404105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404105).length < 2 ^ (prefixWord ++ tailWord_6404105).sum := by decide
  have hdescent : baseEnd_6404105 < baseStart_6404105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404125 : List Nat := [1, 4, 2, 2, 2, 1, 1, 10]
def baseStart_6404125 : Nat := 118140960795 + 6404125 * 2 ^ 59
def prefixEnd_6404125 : Nat := 4983230072969 + 3 ^ 40 * 6404125 * 2
def baseEnd_6404125 : Nat := 121792381350920798710573

theorem tailTrace_6404125 : CollatzResearch.WordTrace tailWord_6404125 prefixEnd_6404125 121792381350920798710573 := by
  unfold tailWord_6404125
  simp only [CollatzResearch.WordTrace]
  refine ⟨233577627923956337318221829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155718418615970891545481219 233577627923956337318221829)
  ·
    refine ⟨43795805235741813247166593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233577627923956337318221829 43795805235741813247166593)
    ·
      refine ⟨32846853926806359935374945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43795805235741813247166593 32846853926806359935374945)
      ·
        refine ⟨24635140445104769951531209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32846853926806359935374945 24635140445104769951531209)
        ·
          refine ⟨18476355333828577463648407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24635140445104769951531209 18476355333828577463648407)
          ·
            refine ⟨27714533000742866195472611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18476355333828577463648407 27714533000742866195472611)
            ·
              refine ⟨41571799501114299293208917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27714533000742866195472611 41571799501114299293208917)
              ·
                refine ⟨121792381350920798710573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41571799501114299293208917 121792381350920798710573)
                ·
                  rfl

theorem cell23_6404125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 10].length) (baseStart_6404125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404125 prefixEnd_6404125 := by exact prefixLift 6404125
  have htrace : WordTrace (prefixWord ++ tailWord_6404125) baseStart_6404125 baseEnd_6404125 := by
    simpa [prefixWord, tailWord_6404125, baseEnd_6404125] using wordTrace_append hprefix tailTrace_6404125
  have hstable : (prefixWord ++ tailWord_6404125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404125).length < 2 ^ (prefixWord ++ tailWord_6404125).sum := by decide
  have hdescent : baseEnd_6404125 < baseStart_6404125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404129 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 2, 4]
def baseStart_6404129 : Nat := 118140960795 + 6404129 * 2 ^ 59
def prefixEnd_6404129 : Nat := 4983230072969 + 3 ^ 40 * 6404129 * 2
def baseEnd_6404129 : Nat := 1096132116799159849845151

theorem tailTrace_6404129 : CollatzResearch.WordTrace tailWord_6404129 prefixEnd_6404129 1096132116799159849845151 := by
  unfold tailWord_6404129
  simp only [CollatzResearch.WordTrace]
  refine ⟨233577773815941846001367441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155718515877294564000911627 233577773815941846001367441)
  ·
    refine ⟨175183330361956384501025581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233577773815941846001367441 175183330361956384501025581)
    ·
      refine ⟨65693748885733644187884593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175183330361956384501025581 65693748885733644187884593)
      ·
        refine ⟨49270311664300233140913445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65693748885733644187884593 49270311664300233140913445)
        ·
          refine ⟨9238183437056293713921271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49270311664300233140913445 9238183437056293713921271)
          ·
            refine ⟨13857275155584440570881907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9238183437056293713921271 13857275155584440570881907)
            ·
              refine ⟨20785912733376660856322861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13857275155584440570881907 20785912733376660856322861)
              ·
                refine ⟨7794717275016247821121073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20785912733376660856322861 7794717275016247821121073)
                ·
                  refine ⟨5846037956262185865840805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7794717275016247821121073 5846037956262185865840805)
                  ·
                    refine ⟨1096132116799159849845151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5846037956262185865840805 1096132116799159849845151)
                    ·
                      rfl

theorem cell23_6404129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_6404129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404129 prefixEnd_6404129 := by exact prefixLift 6404129
  have htrace : WordTrace (prefixWord ++ tailWord_6404129) baseStart_6404129 baseEnd_6404129 := by
    simpa [prefixWord, tailWord_6404129, baseEnd_6404129] using wordTrace_append hprefix tailTrace_6404129
  have hstable : (prefixWord ++ tailWord_6404129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404129).length < 2 ^ (prefixWord ++ tailWord_6404129).sum := by decide
  have hdescent : baseEnd_6404129 < baseStart_6404129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404169 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 3]
def baseStart_6404169 : Nat := 118140960795 + 6404169 * 2 ^ 59
def prefixEnd_6404169 : Nat := 4983230072969 + 3 ^ 40 * 6404169 * 2
def baseEnd_6404169 : Nat := 3288416889623659393035269

theorem tailTrace_6404169 : CollatzResearch.WordTrace tailWord_6404169 prefixEnd_6404169 3288416889623659393035269 := by
  unfold tailWord_6404169
  simp only [CollatzResearch.WordTrace]
  refine ⟨233579232735796932832823561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155719488490531288555215707 233579232735796932832823561)
  ·
    refine ⟨175184424551847699624617671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233579232735796932832823561 175184424551847699624617671)
    ·
      refine ⟨262776636827771549436926507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175184424551847699624617671 262776636827771549436926507)
      ·
        refine ⟨394164955241657324155389761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262776636827771549436926507 394164955241657324155389761)
        ·
          refine ⟨295623716431242993116542321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394164955241657324155389761 295623716431242993116542321)
          ·
            refine ⟨221717787323432244837406741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295623716431242993116542321 221717787323432244837406741)
            ·
              refine ⟨10393021280785886476753441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221717787323432244837406741 10393021280785886476753441)
              ·
                refine ⟨7794765960589414857565081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10393021280785886476753441 7794765960589414857565081)
                ·
                  refine ⟨5846074470442061143173811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7794765960589414857565081 5846074470442061143173811)
                  ·
                    refine ⟨8769111705663091714760717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846074470442061143173811 8769111705663091714760717)
                    ·
                      refine ⟨3288416889623659393035269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769111705663091714760717 3288416889623659393035269)
                      ·
                        rfl

theorem cell23_6404169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_6404169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404169 prefixEnd_6404169 := by exact prefixLift 6404169
  have htrace : WordTrace (prefixWord ++ tailWord_6404169) baseStart_6404169 baseEnd_6404169 := by
    simpa [prefixWord, tailWord_6404169, baseEnd_6404169] using wordTrace_append hprefix tailTrace_6404169
  have hstable : (prefixWord ++ tailWord_6404169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404169).length < 2 ^ (prefixWord ++ tailWord_6404169).sum := by decide
  have hdescent : baseEnd_6404169 < baseStart_6404169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404185 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_6404185 : Nat := 118140960795 + 6404185 * 2 ^ 59
def prefixEnd_6404185 : Nat := 4983230072969 + 3 ^ 40 * 6404185 * 2
def baseEnd_6404185 : Nat := 1096141701771377110145065

theorem tailTrace_6404185 : CollatzResearch.WordTrace tailWord_6404185 prefixEnd_6404185 1096141701771377110145065 := by
  unfold tailWord_6404185
  simp only [CollatzResearch.WordTrace]
  refine ⟨233579816303738967565406009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155719877535825978376937339 233579816303738967565406009)
  ·
    refine ⟨175184862227804225674054507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233579816303738967565406009 175184862227804225674054507)
    ·
      refine ⟨262777293341706338511081761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175184862227804225674054507 262777293341706338511081761)
      ·
        refine ⟨197082970006279753883311321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262777293341706338511081761 197082970006279753883311321)
        ·
          refine ⟨147812227504709815412483491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197082970006279753883311321 147812227504709815412483491)
          ·
            refine ⟨221718341257064723118725237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147812227504709815412483491 221718341257064723118725237)
            ·
              refine ⟨20786094492849817792380491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221718341257064723118725237 20786094492849817792380491)
              ·
                refine ⟨31179141739274726688570737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20786094492849817792380491 31179141739274726688570737)
                ·
                  refine ⟨23384356304456045016428053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31179141739274726688570737 23384356304456045016428053)
                  ·
                    refine ⟨1096141701771377110145065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23384356304456045016428053 1096141701771377110145065)
                    ·
                      rfl

theorem cell23_6404185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_6404185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404185 prefixEnd_6404185 := by exact prefixLift 6404185
  have htrace : WordTrace (prefixWord ++ tailWord_6404185) baseStart_6404185 baseEnd_6404185 := by
    simpa [prefixWord, tailWord_6404185, baseEnd_6404185] using wordTrace_append hprefix tailTrace_6404185
  have hstable : (prefixWord ++ tailWord_6404185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404185).length < 2 ^ (prefixWord ++ tailWord_6404185).sum := by decide
  have hdescent : baseEnd_6404185 < baseStart_6404185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404195 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5]
def baseStart_6404195 : Nat := 118140960795 + 6404195 * 2 ^ 59
def prefixEnd_6404195 : Nat := 4983230072969 + 3 ^ 40 * 6404195 * 2
def baseEnd_6404195 : Nat := 3288430240120676291310149

theorem tailTrace_6404195 : CollatzResearch.WordTrace tailWord_6404195 prefixEnd_6404195 3288430240120676291310149 := by
  unfold tailWord_6404195
  simp only [CollatzResearch.WordTrace]
  refine ⟨233580181033702739273270039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155720120689135159515513359 233580181033702739273270039)
  ·
    refine ⟨350370271550554108909905059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233580181033702739273270039 350370271550554108909905059)
    ·
      refine ⟨525555407325831163364857589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350370271550554108909905059 525555407325831163364857589)
      ·
        refine ⟨49270819436796671565455399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 525555407325831163364857589 49270819436796671565455399)
        ·
          refine ⟨73906229155195007348183099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49270819436796671565455399 73906229155195007348183099)
          ·
            refine ⟨110859343732792511022274649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73906229155195007348183099 110859343732792511022274649)
            ·
              refine ⟨83144507799594383266705987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110859343732792511022274649 83144507799594383266705987)
              ·
                refine ⟨124716761699391574900058981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83144507799594383266705987 124716761699391574900058981)
                ·
                  refine ⟨23384392818635920293761059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124716761699391574900058981 23384392818635920293761059)
                  ·
                    refine ⟨35076589227953880440641589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23384392818635920293761059 35076589227953880440641589)
                    ·
                      refine ⟨3288430240120676291310149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35076589227953880440641589 3288430240120676291310149)
                      ·
                        rfl

theorem cell23_6404195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_6404195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404195 prefixEnd_6404195 := by exact prefixLift 6404195
  have htrace : WordTrace (prefixWord ++ tailWord_6404195) baseStart_6404195 baseEnd_6404195 := by
    simpa [prefixWord, tailWord_6404195, baseEnd_6404195] using wordTrace_append hprefix tailTrace_6404195
  have hstable : (prefixWord ++ tailWord_6404195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404195).length < 2 ^ (prefixWord ++ tailWord_6404195).sum := by decide
  have hdescent : baseEnd_6404195 < baseStart_6404195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404209 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 4, 2, 2]
def baseStart_6404209 : Nat := 118140960795 + 6404209 * 2 ^ 59
def prefixEnd_6404209 : Nat := 4983230072969 + 3 ^ 40 * 6404209 * 2
def baseEnd_6404209 : Nat := 3288437428849839236535085

theorem tailTrace_6404209 : CollatzResearch.WordTrace tailWord_6404209 prefixEnd_6404209 3288437428849839236535085 := by
  unfold tailWord_6404209
  simp only [CollatzResearch.WordTrace]
  refine ⟨233580691655652019664279681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155720461103768013109519787 233580691655652019664279681)
  ·
    refine ⟨175185518741739014748209761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233580691655652019664279681 175185518741739014748209761)
    ·
      refine ⟨131389139056304261061157321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175185518741739014748209761 131389139056304261061157321)
      ·
        refine ⟨98541854292228195795867991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131389139056304261061157321 98541854292228195795867991)
        ·
          refine ⟨147812781438342293693801987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98541854292228195795867991 147812781438342293693801987)
          ·
            refine ⟨221719172157513440540702981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147812781438342293693801987 221719172157513440540702981)
            ·
              refine ⟨41572344779533770101381809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221719172157513440540702981 41572344779533770101381809)
              ·
                refine ⟨31179258584650327576036357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41572344779533770101381809 31179258584650327576036357)
                ·
                  refine ⟨5846110984621936420506817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31179258584650327576036357 5846110984621936420506817)
                  ·
                    refine ⟨4384583238466452315380113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5846110984621936420506817 4384583238466452315380113)
                    ·
                      refine ⟨3288437428849839236535085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384583238466452315380113 3288437428849839236535085)
                      ·
                        rfl

theorem cell23_6404209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_6404209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404209 prefixEnd_6404209 := by exact prefixLift 6404209
  have htrace : WordTrace (prefixWord ++ tailWord_6404209) baseStart_6404209 baseEnd_6404209 := by
    simpa [prefixWord, tailWord_6404209, baseEnd_6404209] using wordTrace_append hprefix tailTrace_6404209
  have hstable : (prefixWord ++ tailWord_6404209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404209).length < 2 ^ (prefixWord ++ tailWord_6404209).sum := by decide
  have hdescent : baseEnd_6404209 < baseStart_6404209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404232 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 7]
def baseStart_6404232 : Nat := 118140960795 + 6404232 * 2 ^ 59
def prefixEnd_6404232 : Nat := 4983230072969 + 3 ^ 40 * 6404232 * 2
def baseEnd_6404232 : Nat := 365383248767210294060831

theorem tailTrace_6404232 : CollatzResearch.WordTrace tailWord_6404232 prefixEnd_6404232 365383248767210294060831 := by
  unfold tailWord_6404232
  simp only [CollatzResearch.WordTrace]
  refine ⟨116790765267284347296183475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155721020356379129728244633 116790765267284347296183475)
  ·
    refine ⟨175186147900926520944275213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116790765267284347296183475 175186147900926520944275213)
    ·
      refine ⟨65694805462847445354103205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175186147900926520944275213 65694805462847445354103205)
      ·
        refine ⟨12317776024283896003894351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65694805462847445354103205 12317776024283896003894351)
        ·
          refine ⟨18476664036425844005841527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12317776024283896003894351 18476664036425844005841527)
          ·
            refine ⟨27714996054638766008762291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18476664036425844005841527 27714996054638766008762291)
            ·
              refine ⟨41572494081958149013143437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27714996054638766008762291 41572494081958149013143437)
              ·
                refine ⟨15589685280734305879928789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41572494081958149013143437 15589685280734305879928789)
                ·
                  refine ⟨365383248767210294060831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15589685280734305879928789 365383248767210294060831)
                  ·
                    rfl

theorem cell23_6404232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_6404232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404232 prefixEnd_6404232 := by exact prefixLift 6404232
  have htrace : WordTrace (prefixWord ++ tailWord_6404232) baseStart_6404232 baseEnd_6404232 := by
    simpa [prefixWord, tailWord_6404232, baseEnd_6404232] using wordTrace_append hprefix tailTrace_6404232
  have hstable : (prefixWord ++ tailWord_6404232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404232).length < 2 ^ (prefixWord ++ tailWord_6404232).sum := by decide
  have hdescent : baseEnd_6404232 < baseStart_6404232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404245 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_6404245 : Nat := 118140960795 + 6404245 * 2 ^ 59
def prefixEnd_6404245 : Nat := 4983230072969 + 3 ^ 40 * 6404245 * 2
def baseEnd_6404245 : Nat := 1096151971384467031894973

theorem tailTrace_6404245 : CollatzResearch.WordTrace tailWord_6404245 prefixEnd_6404245 1096151971384467031894973 := by
  unfold tailWord_6404245
  simp only [CollatzResearch.WordTrace]
  refine ⟨233582004683521597812590189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155721336455681065208393459 233582004683521597812590189)
  ·
    refine ⟨87593251756320599179721321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233582004683521597812590189 87593251756320599179721321)
    ·
      refine ⟨65694938817240449384790991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87593251756320599179721321 65694938817240449384790991)
      ·
        refine ⟨98542408225860674077186487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65694938817240449384790991 98542408225860674077186487)
        ·
          refine ⟨147813612338791011115779731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98542408225860674077186487 147813612338791011115779731)
          ·
            refine ⟨221720418508186516673669597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147813612338791011115779731 221720418508186516673669597)
            ·
              refine ⟨83145156940569943752626099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221720418508186516673669597 83145156940569943752626099)
              ·
                refine ⟨124717735410854915628939149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83145156940569943752626099 124717735410854915628939149)
                ·
                  refine ⟨46769150779070593360852181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124717735410854915628939149 46769150779070593360852181)
                  ·
                    refine ⟨1096151971384467031894973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46769150779070593360852181 1096151971384467031894973)
                    ·
                      rfl

theorem cell23_6404245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_6404245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404245 prefixEnd_6404245 := by exact prefixLift 6404245
  have htrace : WordTrace (prefixWord ++ tailWord_6404245) baseStart_6404245 baseEnd_6404245 := by
    simpa [prefixWord, tailWord_6404245, baseEnd_6404245] using wordTrace_append hprefix tailTrace_6404245
  have hstable : (prefixWord ++ tailWord_6404245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404245).length < 2 ^ (prefixWord ++ tailWord_6404245).sum := by decide
  have hdescent : baseEnd_6404245 < baseStart_6404245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404282 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_6404282 : Nat := 118140960795 + 6404282 * 2 ^ 59
def prefixEnd_6404282 : Nat := 4983230072969 + 3 ^ 40 * 6404282 * 2
def baseEnd_6404282 : Nat := 3288474912937617450922249

theorem tailTrace_6404282 : CollatzResearch.WordTrace tailWord_6404282 prefixEnd_6404282 3288474912937617450922249 := by
  unfold tailWord_6404282
  simp only [CollatzResearch.WordTrace]
  refine ⟨58395838546096888282921775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155722236122925035421124733 58395838546096888282921775)
  ·
    refine ⟨87593757819145332424382663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58395838546096888282921775 87593757819145332424382663)
    ·
      refine ⟨131390636728717998636573995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87593757819145332424382663 131390636728717998636573995)
      ·
        refine ⟨197085955093076997954860993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131390636728717998636573995 197085955093076997954860993)
        ·
          refine ⟨147814466319807748466145745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197085955093076997954860993 147814466319807748466145745)
          ·
            refine ⟨110860849739855811349609309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147814466319807748466145745 110860849739855811349609309)
            ·
              refine ⟨41572818652445929256103491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110860849739855811349609309 41572818652445929256103491)
              ·
                refine ⟨62359227978668893884155237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41572818652445929256103491 62359227978668893884155237)
                ·
                  refine ⟨11692355246000417603279107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62359227978668893884155237 11692355246000417603279107)
                  ·
                    refine ⟨17538532869000626404918661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11692355246000417603279107 17538532869000626404918661)
                    ·
                      refine ⟨3288474912937617450922249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17538532869000626404918661 3288474912937617450922249)
                      ·
                        rfl

theorem cell23_6404282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_6404282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404282 prefixEnd_6404282 := by exact prefixLift 6404282
  have htrace : WordTrace (prefixWord ++ tailWord_6404282) baseStart_6404282 baseEnd_6404282 := by
    simpa [prefixWord, tailWord_6404282, baseEnd_6404282] using wordTrace_append hprefix tailTrace_6404282
  have hstable : (prefixWord ++ tailWord_6404282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404282).length < 2 ^ (prefixWord ++ tailWord_6404282).sum := by decide
  have hdescent : baseEnd_6404282 < baseStart_6404282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404349 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_6404349 : Nat := 118140960795 + 6404349 * 2 ^ 59
def prefixEnd_6404349 : Nat := 4983230072969 + 3 ^ 40 * 6404349 * 2
def baseEnd_6404349 : Nat := 3288509316141468688784441

theorem tailTrace_6404349 : CollatzResearch.WordTrace tailWord_6404349 prefixEnd_6404349 3288509316141468688784441 := by
  unfold tailWord_6404349
  simp only [CollatzResearch.WordTrace]
  refine ⟨233585797875144823574376101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155723865250096549049584067 233585797875144823574376101)
  ·
    refine ⟨43797337101589654420195519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233585797875144823574376101 43797337101589654420195519)
    ·
      refine ⟨65696005652384481630293279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43797337101589654420195519 65696005652384481630293279)
      ·
        refine ⟨98544008478576722445439919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65696005652384481630293279 98544008478576722445439919)
        ·
          refine ⟨147816012717865083668159879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98544008478576722445439919 147816012717865083668159879)
          ·
            refine ⟨221724019076797625502239819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147816012717865083668159879 221724019076797625502239819)
            ·
              refine ⟨332586028615196438253359729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221724019076797625502239819 332586028615196438253359729)
              ·
                refine ⟨249439521461397328690019797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332586028615196438253359729 249439521461397328690019797)
                ·
                  refine ⟨5846238784251499891172339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 249439521461397328690019797 5846238784251499891172339)
                  ·
                    refine ⟨8769358176377249836758509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846238784251499891172339 8769358176377249836758509)
                    ·
                      refine ⟨3288509316141468688784441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769358176377249836758509 3288509316141468688784441)
                      ·
                        rfl

theorem cell23_6404349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_6404349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404349 prefixEnd_6404349 := by exact prefixLift 6404349
  have htrace : WordTrace (prefixWord ++ tailWord_6404349) baseStart_6404349 baseEnd_6404349 := by
    simpa [prefixWord, tailWord_6404349, baseEnd_6404349] using wordTrace_append hprefix tailTrace_6404349
  have hstable : (prefixWord ++ tailWord_6404349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404349).length < 2 ^ (prefixWord ++ tailWord_6404349).sum := by decide
  have hdescent : baseEnd_6404349 < baseStart_6404349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404352 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_6404352 : Nat := 118140960795 + 6404352 * 2 ^ 59
def prefixEnd_6404352 : Nat := 4983230072969 + 3 ^ 40 * 6404352 * 2
def baseEnd_6404352 : Nat := 1096170285527810725682309

theorem tailTrace_6404352 : CollatzResearch.WordTrace tailWord_6404352 prefixEnd_6404352 1096170285527810725682309 := by
  unfold tailWord_6404352
  simp only [CollatzResearch.WordTrace]
  refine ⟨116792953647066977543367655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155723938196089303391156873 116792953647066977543367655)
  ·
    refine ⟨175189430470600466315051483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116792953647066977543367655 175189430470600466315051483)
    ·
      refine ⟨262784145705900699472577225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175189430470600466315051483 262784145705900699472577225)
      ·
        refine ⟨197088109279425524604432919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262784145705900699472577225 197088109279425524604432919)
        ·
          refine ⟨295632163919138286906649379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197088109279425524604432919 295632163919138286906649379)
          ·
            refine ⟨443448245878707430359974069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295632163919138286906649379 443448245878707430359974069)
            ·
              refine ⟨41573273051128821596247569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 443448245878707430359974069 41573273051128821596247569)
              ·
                refine ⟨31179954788346616197185677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41573273051128821596247569 31179954788346616197185677)
                ·
                  refine ⟨11692483045629981073944629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31179954788346616197185677 11692483045629981073944629)
                  ·
                    refine ⟨1096170285527810725682309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11692483045629981073944629 1096170285527810725682309)
                    ·
                      rfl

theorem cell23_6404352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_6404352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404352 prefixEnd_6404352 := by exact prefixLift 6404352
  have htrace : WordTrace (prefixWord ++ tailWord_6404352) baseStart_6404352 baseEnd_6404352 := by
    simpa [prefixWord, tailWord_6404352, baseEnd_6404352] using wordTrace_append hprefix tailTrace_6404352
  have hstable : (prefixWord ++ tailWord_6404352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404352).length < 2 ^ (prefixWord ++ tailWord_6404352).sum := by decide
  have hdescent : baseEnd_6404352 < baseStart_6404352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404366 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6404366 : Nat := 118140960795 + 6404366 * 2 ^ 59
def prefixEnd_6404366 : Nat := 4983230072969 + 3 ^ 40 * 6404366 * 2
def baseEnd_6404366 : Nat := 3288518045312595122271863

theorem tailTrace_6404366 : CollatzResearch.WordTrace tailWord_6404366 prefixEnd_6404366 3288518045312595122271863 := by
  unfold tailWord_6404366
  simp only [CollatzResearch.WordTrace]
  refine ⟨29198302239510404434718119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155724278610722156985163301 29198302239510404434718119)
  ·
    refine ⟨43797453359265606652077179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29198302239510404434718119 43797453359265606652077179)
    ·
      refine ⟨65696180038898409978115769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43797453359265606652077179 65696180038898409978115769)
      ·
        refine ⟨49272135029173807483586827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65696180038898409978115769 49272135029173807483586827)
        ·
          refine ⟨73908202543760711225380241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49272135029173807483586827 73908202543760711225380241)
          ·
            refine ⟨55431151907820533419035181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73908202543760711225380241 55431151907820533419035181)
            ·
              refine ⟨20786681965432700032138193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55431151907820533419035181 20786681965432700032138193)
              ·
                refine ⟨15590011474074525024103645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20786681965432700032138193 15590011474074525024103645)
                ·
                  refine ⟨5846254302777946884038867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15590011474074525024103645 5846254302777946884038867)
                  ·
                    refine ⟨8769381454166920326058301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846254302777946884038867 8769381454166920326058301)
                    ·
                      refine ⟨3288518045312595122271863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769381454166920326058301 3288518045312595122271863)
                      ·
                        rfl

theorem cell23_6404366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6404366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404366 prefixEnd_6404366 := by exact prefixLift 6404366
  have htrace : WordTrace (prefixWord ++ tailWord_6404366) baseStart_6404366 baseEnd_6404366 := by
    simpa [prefixWord, tailWord_6404366, baseEnd_6404366] using wordTrace_append hprefix tailTrace_6404366
  have hstable : (prefixWord ++ tailWord_6404366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404366).length < 2 ^ (prefixWord ++ tailWord_6404366).sum := by decide
  have hdescent : baseEnd_6404366 < baseStart_6404366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404383 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 1, 1, 3]
def baseStart_6404383 : Nat := 118140960795 + 6404383 * 2 ^ 59
def prefixEnd_6404383 : Nat := 4983230072969 + 3 ^ 40 * 6404383 * 2
def baseEnd_6404383 : Nat := 3288526774483721555759285

theorem tailTrace_6404383 : CollatzResearch.WordTrace tailWord_6404383 prefixEnd_6404383 3288526774483721555759285 := by
  unfold tailWord_6404383
  simp only [CollatzResearch.WordTrace]
  refine ⟨233587037957021647381113803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155724691971347764920742535 233587037957021647381113803)
  ·
    refine ⟨350380556935532471071670705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233587037957021647381113803 350380556935532471071670705)
    ·
      refine ⟨262785417701649353303753029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350380556935532471071670705 262785417701649353303753029)
      ·
        refine ⟨49272265819059253744453693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262785417701649353303753029 49272265819059253744453693)
        ·
          refine ⟨18477099682147220154170135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49272265819059253744453693 18477099682147220154170135)
          ·
            refine ⟨27715649523220830231255203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18477099682147220154170135 27715649523220830231255203)
            ·
              refine ⟨41573474284831245346882805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27715649523220830231255203 41573474284831245346882805)
              ·
                refine ⟨3897513214202929251270263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41573474284831245346882805 3897513214202929251270263)
                ·
                  refine ⟨5846269821304393876905395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897513214202929251270263 5846269821304393876905395)
                  ·
                    refine ⟨8769404731956590815358093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846269821304393876905395 8769404731956590815358093)
                    ·
                      refine ⟨3288526774483721555759285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769404731956590815358093 3288526774483721555759285)
                      ·
                        rfl

theorem cell23_6404383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_6404383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404383 prefixEnd_6404383 := by exact prefixLift 6404383
  have htrace : WordTrace (prefixWord ++ tailWord_6404383) baseStart_6404383 baseEnd_6404383 := by
    simpa [prefixWord, tailWord_6404383, baseEnd_6404383] using wordTrace_append hprefix tailTrace_6404383
  have hstable : (prefixWord ++ tailWord_6404383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404383).length < 2 ^ (prefixWord ++ tailWord_6404383).sum := by decide
  have hdescent : baseEnd_6404383 < baseStart_6404383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404386 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_6404386 : Nat := 118140960795 + 6404386 * 2 ^ 59
def prefixEnd_6404386 : Nat := 4983230072969 + 3 ^ 40 * 6404386 * 2
def baseEnd_6404386 : Nat := 1096176104975228348007257

theorem tailTrace_6404386 : CollatzResearch.WordTrace tailWord_6404386 prefixEnd_6404386 1096176104975228348007257 := by
  unfold tailWord_6404386
  simp only [CollatzResearch.WordTrace]
  refine ⟨58396786844002694723368253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155724764917340519262315341 58396786844002694723368253)
  ·
    refine ⟨21898795066501010521263095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58396786844002694723368253 21898795066501010521263095)
    ·
      refine ⟨32848192599751515781894643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21898795066501010521263095 32848192599751515781894643)
      ·
        refine ⟨49272288899627273672841965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32848192599751515781894643 49272288899627273672841965)
        ·
          refine ⟨18477108337360227627315737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49272288899627273672841965 18477108337360227627315737)
          ·
            refine ⟨13857831253020170720486803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18477108337360227627315737 13857831253020170720486803)
            ·
              refine ⟨20786746879530256080730205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13857831253020170720486803 20786746879530256080730205)
              ·
                refine ⟨7795030079823846030273827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20786746879530256080730205 7795030079823846030273827)
                ·
                  refine ⟨11692545119735769045410741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795030079823846030273827 11692545119735769045410741)
                  ·
                    refine ⟨1096176104975228348007257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11692545119735769045410741 1096176104975228348007257)
                    ·
                      rfl

theorem cell23_6404386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_6404386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404386 prefixEnd_6404386 := by exact prefixLift 6404386
  have htrace : WordTrace (prefixWord ++ tailWord_6404386) baseStart_6404386 baseEnd_6404386 := by
    simpa [prefixWord, tailWord_6404386, baseEnd_6404386] using wordTrace_append hprefix tailTrace_6404386
  have hstable : (prefixWord ++ tailWord_6404386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404386).length < 2 ^ (prefixWord ++ tailWord_6404386).sum := by decide
  have hdescent : baseEnd_6404386 < baseStart_6404386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404409 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6404409 : Nat := 118140960795 + 6404409 * 2 ^ 59
def prefixEnd_6404409 : Nat := 4983230072969 + 3 ^ 40 * 6404409 * 2
def baseEnd_6404409 : Nat := 3288540124980738454034165

theorem tailTrace_6404409 : CollatzResearch.WordTrace tailWord_6404409 prefixEnd_6404409 3288540124980738454034165 := by
  unfold tailWord_6404409
  simp only [CollatzResearch.WordTrace]
  refine ⟨233587986254927453821560281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155725324169951635881040187 233587986254927453821560281)
  ·
    refine ⟨175190989691195590366170211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233587986254927453821560281 175190989691195590366170211)
    ·
      refine ⟨262786484536793385549255317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175190989691195590366170211 262786484536793385549255317)
      ·
        refine ⟨12318116462662189947621343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 262786484536793385549255317 12318116462662189947621343)
        ·
          refine ⟨18477174693993284921432015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12318116462662189947621343 18477174693993284921432015)
          ·
            refine ⟨27715762040989927382148023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18477174693993284921432015 27715762040989927382148023)
            ·
              refine ⟨41573643061484891073222035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27715762040989927382148023 41573643061484891073222035)
              ·
                refine ⟨62360464592227336609833053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41573643061484891073222035 62360464592227336609833053)
                ·
                  refine ⟨23385174222085251228687395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62360464592227336609833053 23385174222085251228687395)
                  ·
                    refine ⟨35077761333127876843031093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23385174222085251228687395 35077761333127876843031093)
                    ·
                      refine ⟨3288540124980738454034165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35077761333127876843031093 3288540124980738454034165)
                      ·
                        rfl

theorem cell23_6404409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6404409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404409 prefixEnd_6404409 := by exact prefixLift 6404409
  have htrace : WordTrace (prefixWord ++ tailWord_6404409) baseStart_6404409 baseEnd_6404409 := by
    simpa [prefixWord, tailWord_6404409, baseEnd_6404409] using wordTrace_append hprefix tailTrace_6404409
  have hstable : (prefixWord ++ tailWord_6404409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404409).length < 2 ^ (prefixWord ++ tailWord_6404409).sum := by decide
  have hdescent : baseEnd_6404409 < baseStart_6404409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404412 : List Nat := [2, 2, 2, 2, 1, 2, 2, 10]
def baseStart_6404412 : Nat := 118140960795 + 6404412 * 2 ^ 59
def prefixEnd_6404412 : Nat := 4983230072969 + 3 ^ 40 * 6404412 * 2
def baseEnd_6404412 : Nat := 121797839460100071936913

theorem tailTrace_6404412 : CollatzResearch.WordTrace tailWord_6404412 prefixEnd_6404412 121797839460100071936913 := by
  unfold tailWord_6404412
  simp only [CollatzResearch.WordTrace]
  refine ⟨116794047836958292666959745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155725397115944390222612993 116794047836958292666959745)
  ·
    refine ⟨87595535877718719500219809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116794047836958292666959745 87595535877718719500219809)
    ·
      refine ⟨65696651908289039625164857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87595535877718719500219809 65696651908289039625164857)
      ·
        refine ⟨49272488931216779718873643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65696651908289039625164857 49272488931216779718873643)
        ·
          refine ⟨73908733396825169578310465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49272488931216779718873643 73908733396825169578310465)
          ·
            refine ⟨55431550047618877183732849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73908733396825169578310465 55431550047618877183732849)
            ·
              refine ⟨41573662535714157887799637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55431550047618877183732849 41573662535714157887799637)
              ·
                refine ⟨121797839460100071936913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41573662535714157887799637 121797839460100071936913)
                ·
                  rfl

theorem cell23_6404412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 10].length) (baseStart_6404412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404412 prefixEnd_6404412 := by exact prefixLift 6404412
  have htrace : WordTrace (prefixWord ++ tailWord_6404412) baseStart_6404412 baseEnd_6404412 := by
    simpa [prefixWord, tailWord_6404412, baseEnd_6404412] using wordTrace_append hprefix tailTrace_6404412
  have hstable : (prefixWord ++ tailWord_6404412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404412).length < 2 ^ (prefixWord ++ tailWord_6404412).sum := by decide
  have hdescent : baseEnd_6404412 < baseStart_6404412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404419 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 4]
def baseStart_6404419 : Nat := 118140960795 + 6404419 * 2 ^ 59
def prefixEnd_6404419 : Nat := 4983230072969 + 3 ^ 40 * 6404419 * 2
def baseEnd_6404419 : Nat := 3288545259787283414909119

theorem tailTrace_6404419 : CollatzResearch.WordTrace tailWord_6404419 prefixEnd_6404419 3288545259787283414909119 := by
  unfold tailWord_6404419
  simp only [CollatzResearch.WordTrace]
  refine ⟨233588350984891225529424311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155725567323260817019616207 233588350984891225529424311)
  ·
    refine ⟨350382526477336838294136467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233588350984891225529424311 350382526477336838294136467)
    ·
      refine ⟨525573789716005257441204701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350382526477336838294136467 525573789716005257441204701)
      ·
        refine ⟨197090171143501971540451763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525573789716005257441204701 197090171143501971540451763)
        ·
          refine ⟨295635256715252957310677645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197090171143501971540451763 295635256715252957310677645)
          ·
            refine ⟨110863221268219858991504117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295635256715252957310677645 110863221268219858991504117)
            ·
              refine ⟨10393426993895611780453511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110863221268219858991504117 10393426993895611780453511)
              ·
                refine ⟨15590140490843417670680267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10393426993895611780453511 15590140490843417670680267)
                ·
                  refine ⟨23385210736265126506020401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15590140490843417670680267 23385210736265126506020401)
                  ·
                    refine ⟨17538908052198844879515301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23385210736265126506020401 17538908052198844879515301)
                    ·
                      refine ⟨3288545259787283414909119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17538908052198844879515301 3288545259787283414909119)
                      ·
                        rfl

theorem cell23_6404419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_6404419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404419 prefixEnd_6404419 := by exact prefixLift 6404419
  have htrace : WordTrace (prefixWord ++ tailWord_6404419) baseStart_6404419 baseEnd_6404419 := by
    simpa [prefixWord, tailWord_6404419, baseEnd_6404419] using wordTrace_append hprefix tailTrace_6404419
  have hstable : (prefixWord ++ tailWord_6404419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404419).length < 2 ^ (prefixWord ++ tailWord_6404419).sum := by decide
  have hdescent : baseEnd_6404419 < baseStart_6404419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404439 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_6404439 : Nat := 118140960795 + 6404439 * 2 ^ 59
def prefixEnd_6404439 : Nat := 4983230072969 + 3 ^ 40 * 6404439 * 2
def baseEnd_6404439 : Nat := 3288555529400373336659027

theorem tailTrace_6404439 : CollatzResearch.WordTrace tailWord_6404439 prefixEnd_6404439 3288555529400373336659027 := by
  unfold tailWord_6404439
  simp only [CollatzResearch.WordTrace]
  refine ⟨233589080444818768945152371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155726053629879179296768247 233589080444818768945152371)
  ·
    refine ⟨350383620667228153417728557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233589080444818768945152371 350383620667228153417728557)
    ·
      refine ⟨131393857750210557531648209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350383620667228153417728557 131393857750210557531648209)
      ·
        refine ⟨98545393312657918148736157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131393857750210557531648209 98545393312657918148736157)
        ·
          refine ⟨36954522492246719305776059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98545393312657918148736157 36954522492246719305776059)
          ·
            refine ⟨55431783738370078958664089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36954522492246719305776059 55431783738370078958664089)
            ·
              refine ⟨41573837803777559218998067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55431783738370078958664089 41573837803777559218998067)
              ·
                refine ⟨62360756705666338828497101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41573837803777559218998067 62360756705666338828497101)
                ·
                  refine ⟨23385283764624877060686413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62360756705666338828497101 23385283764624877060686413)
                  ·
                    refine ⟨8769481411734328897757405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23385283764624877060686413 8769481411734328897757405)
                    ·
                      refine ⟨3288555529400373336659027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769481411734328897757405 3288555529400373336659027)
                      ·
                        rfl

theorem cell23_6404439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_6404439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404439 prefixEnd_6404439 := by exact prefixLift 6404439
  have htrace : WordTrace (prefixWord ++ tailWord_6404439) baseStart_6404439 baseEnd_6404439 := by
    simpa [prefixWord, tailWord_6404439, baseEnd_6404439] using wordTrace_append hprefix tailTrace_6404439
  have hstable : (prefixWord ++ tailWord_6404439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404439).length < 2 ^ (prefixWord ++ tailWord_6404439).sum := by decide
  have hdescent : baseEnd_6404439 < baseStart_6404439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404442 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_6404442 : Nat := 118140960795 + 6404442 * 2 ^ 59
def prefixEnd_6404442 : Nat := 4983230072969 + 3 ^ 40 * 6404442 * 2
def baseEnd_6404442 : Nat := 1096185689947445608307171

theorem tailTrace_6404442 : CollatzResearch.WordTrace tailWord_6404442 prefixEnd_6404442 1096185689947445608307171 := by
  unfold tailWord_6404442
  simp only [CollatzResearch.WordTrace]
  refine ⟨58397297465951975114377895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155726126575871933638341053 58397297465951975114377895)
  ·
    refine ⟨87595946198927962671566843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58397297465951975114377895 87595946198927962671566843)
    ·
      refine ⟨131393919298391944007350265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87595946198927962671566843 131393919298391944007350265)
      ·
        refine ⟨98545439473793958005512699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131393919298391944007350265 98545439473793958005512699)
        ·
          refine ⟨147818159210690937008269049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98545439473793958005512699 147818159210690937008269049)
          ·
            refine ⟨110863619408018202756201787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147818159210690937008269049 110863619408018202756201787)
            ·
              refine ⟨166295429112027304134302681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110863619408018202756201787 166295429112027304134302681)
              ·
                refine ⟨124721571834020478100727011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166295429112027304134302681 124721571834020478100727011)
                ·
                  refine ⟨187082357751030717151090517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124721571834020478100727011 187082357751030717151090517)
                  ·
                    refine ⟨1096185689947445608307171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187082357751030717151090517 1096185689947445608307171)
                    ·
                      rfl

theorem cell23_6404442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_6404442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404442 prefixEnd_6404442 := by exact prefixLift 6404442
  have htrace : WordTrace (prefixWord ++ tailWord_6404442) baseStart_6404442 baseEnd_6404442 := by
    simpa [prefixWord, tailWord_6404442, baseEnd_6404442] using wordTrace_append hprefix tailTrace_6404442
  have hstable : (prefixWord ++ tailWord_6404442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404442).length < 2 ^ (prefixWord ++ tailWord_6404442).sum := by decide
  have hdescent : baseEnd_6404442 < baseStart_6404442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404483 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 3, 3, 2]
def baseStart_6404483 : Nat := 118140960795 + 6404483 * 2 ^ 59
def prefixEnd_6404483 : Nat := 4983230072969 + 3 ^ 40 * 6404483 * 2
def baseEnd_6404483 : Nat := 3288578122549171164508825

theorem tailTrace_6404483 : CollatzResearch.WordTrace tailWord_6404483 prefixEnd_6404483 3288578122549171164508825 := by
  unfold tailWord_6404483
  simp only [CollatzResearch.WordTrace]
  refine ⟨233590685256659364459754103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155727123504439576306502735 233590685256659364459754103)
  ·
    refine ⟨350386027884989046689631155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233590685256659364459754103 350386027884989046689631155)
    ·
      refine ⟨525579041827483570034446733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350386027884989046689631155 525579041827483570034446733)
      ·
        refine ⟨197092140685306338762917525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525579041827483570034446733 197092140685306338762917525)
        ·
          refine ⟨9238694094623734629511759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197092140685306338762917525 9238694094623734629511759)
          ·
            refine ⟨13858041141935601944267639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9238694094623734629511759 13858041141935601944267639)
            ·
              refine ⟨20787061712903402916401459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13858041141935601944267639 20787061712903402916401459)
              ·
                refine ⟨31180592569355104374602189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20787061712903402916401459 31180592569355104374602189)
                ·
                  refine ⟨11692722213508164140475821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31180592569355104374602189 11692722213508164140475821)
                  ·
                    refine ⟨4384770830065561552678433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11692722213508164140475821 4384770830065561552678433)
                    ·
                      refine ⟨3288578122549171164508825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384770830065561552678433 3288578122549171164508825)
                      ·
                        rfl

theorem cell23_6404483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_6404483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404483 prefixEnd_6404483 := by exact prefixLift 6404483
  have htrace : WordTrace (prefixWord ++ tailWord_6404483) baseStart_6404483 baseEnd_6404483 := by
    simpa [prefixWord, tailWord_6404483, baseEnd_6404483] using wordTrace_append hprefix tailTrace_6404483
  have hstable : (prefixWord ++ tailWord_6404483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404483).length < 2 ^ (prefixWord ++ tailWord_6404483).sum := by decide
  have hdescent : baseEnd_6404483 < baseStart_6404483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404586 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_6404586 : Nat := 118140960795 + 6404586 * 2 ^ 59
def prefixEnd_6404586 : Nat := 4983230072969 + 3 ^ 40 * 6404586 * 2
def baseEnd_6404586 : Nat := 3288631011056584261520851

theorem tailTrace_6404586 : CollatzResearch.WordTrace tailWord_6404586 prefixEnd_6404586 3288631011056584261520851 := by
  unfold tailWord_6404586
  simp only [CollatzResearch.WordTrace]
  refine ⟨58398610493821553262688403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155729627983524142033835741 58398610493821553262688403)
  ·
    refine ⟨87597915740732329894032605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58398610493821553262688403 87597915740732329894032605)
    ·
      refine ⟨32849218402774623710262227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87597915740732329894032605 32849218402774623710262227)
      ·
        refine ⟨49273827604161935565393341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32849218402774623710262227 49273827604161935565393341)
        ·
          refine ⟨18477685351560725837022503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49273827604161935565393341 18477685351560725837022503)
          ·
            refine ⟨27716528027341088755533755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18477685351560725837022503 27716528027341088755533755)
            ·
              refine ⟨41574792041011633133300633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27716528027341088755533755 41574792041011633133300633)
              ·
                refine ⟨31181094030758724849975475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41574792041011633133300633 31181094030758724849975475)
                ·
                  refine ⟨46771641046138087274963213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31181094030758724849975475 46771641046138087274963213)
                  ·
                    refine ⟨17539365392301782728111205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46771641046138087274963213 17539365392301782728111205)
                    ·
                      refine ⟨3288631011056584261520851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17539365392301782728111205 3288631011056584261520851)
                      ·
                        rfl

theorem cell23_6404586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_6404586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404586 prefixEnd_6404586 := by exact prefixLift 6404586
  have htrace : WordTrace (prefixWord ++ tailWord_6404586) baseStart_6404586 baseEnd_6404586 := by
    simpa [prefixWord, tailWord_6404586, baseEnd_6404586] using wordTrace_append hprefix tailTrace_6404586
  have hstable : (prefixWord ++ tailWord_6404586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404586).length < 2 ^ (prefixWord ++ tailWord_6404586).sum := by decide
  have hdescent : baseEnd_6404586 < baseStart_6404586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404639 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 9]
def baseStart_6404639 : Nat := 118140960795 + 6404639 * 2 ^ 59
def prefixEnd_6404639 : Nat := 4983230072969 + 3 ^ 40 * 6404639 * 2
def baseEnd_6404639 : Nat := 1096219408510424184719369

theorem tailTrace_6404639 : CollatzResearch.WordTrace tailWord_6404639 prefixEnd_6404639 1096219408510424184719369 := by
  unfold tailWord_6404639
  simp only [CollatzResearch.WordTrace]
  refine ⟨233596375044094203102432971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155730916696062802068288647 233596375044094203102432971)
  ·
    refine ⟨350394562566141304653649457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233596375044094203102432971 350394562566141304653649457)
    ·
      refine ⟨262795921924605978490237093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350394562566141304653649457 262795921924605978490237093)
      ·
        refine ⟨49274235360863620966919455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262795921924605978490237093 49274235360863620966919455)
        ·
          refine ⟨73911353041295431450379183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49274235360863620966919455 73911353041295431450379183)
          ·
            refine ⟨110867029561943147175568775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73911353041295431450379183 110867029561943147175568775)
            ·
              refine ⟨166300544342914720763353163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110867029561943147175568775 166300544342914720763353163)
              ·
                refine ⟨249450816514372081145029745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166300544342914720763353163 249450816514372081145029745)
                ·
                  refine ⟨187088112385779060858772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249450816514372081145029745 187088112385779060858772309)
                  ·
                    refine ⟨1096219408510424184719369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187088112385779060858772309 1096219408510424184719369)
                    ·
                      rfl

theorem cell23_6404639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_6404639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404639 prefixEnd_6404639 := by exact prefixLift 6404639
  have htrace : WordTrace (prefixWord ++ tailWord_6404639) baseStart_6404639 baseEnd_6404639 := by
    simpa [prefixWord, tailWord_6404639, baseEnd_6404639] using wordTrace_append hprefix tailTrace_6404639
  have hstable : (prefixWord ++ tailWord_6404639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404639).length < 2 ^ (prefixWord ++ tailWord_6404639).sum := by decide
  have hdescent : baseEnd_6404639 < baseStart_6404639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404643 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 6]
def baseStart_6404643 : Nat := 118140960795 + 6404643 * 2 ^ 59
def prefixEnd_6404643 : Nat := 4983230072969 + 3 ^ 40 * 6404643 * 2
def baseEnd_6404643 : Nat := 365406697717098948723121

theorem tailTrace_6404643 : CollatzResearch.WordTrace tailWord_6404643 prefixEnd_6404643 365406697717098948723121 := by
  unfold tailWord_6404643
  simp only [CollatzResearch.WordTrace]
  refine ⟨233596520936079711785578583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155731013957386474523719055 233596520936079711785578583)
  ·
    refine ⟨350394781404119567678367875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233596520936079711785578583 350394781404119567678367875)
    ·
      refine ⟨525592172106179351517551813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350394781404119567678367875 525592172106179351517551813)
      ·
        refine ⟨98548532269908628409540965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 525592172106179351517551813 98548532269908628409540965)
        ·
          refine ⟨18477849800607867826788931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98548532269908628409540965 18477849800607867826788931)
          ·
            refine ⟨27716774700911801740183397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18477849800607867826788931 27716774700911801740183397)
            ·
              refine ⟨5196895256420962826284387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27716774700911801740183397 5196895256420962826284387)
              ·
                refine ⟨7795342884631444239426581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196895256420962826284387 7795342884631444239426581)
                ·
                  refine ⟨365406697717098948723121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7795342884631444239426581 365406697717098948723121)
                  ·
                    rfl

theorem cell23_6404643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 6].length) (baseStart_6404643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404643 prefixEnd_6404643 := by exact prefixLift 6404643
  have htrace : WordTrace (prefixWord ++ tailWord_6404643) baseStart_6404643 baseEnd_6404643 := by
    simpa [prefixWord, tailWord_6404643, baseEnd_6404643] using wordTrace_append hprefix tailTrace_6404643
  have hstable : (prefixWord ++ tailWord_6404643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404643).length < 2 ^ (prefixWord ++ tailWord_6404643).sum := by decide
  have hdescent : baseEnd_6404643 < baseStart_6404643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404687 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 1, 1, 3]
def baseStart_6404687 : Nat := 118140960795 + 6404687 * 2 ^ 59
def prefixEnd_6404687 : Nat := 4983230072969 + 3 ^ 40 * 6404687 * 2
def baseEnd_6404687 : Nat := 3288682872602688366357887

theorem tailTrace_6404687 : CollatzResearch.WordTrace tailWord_6404687 prefixEnd_6404687 3288682872602688366357887 := by
  unfold tailWord_6404687
  simp only [CollatzResearch.WordTrace]
  refine ⟨233598125747920307300180315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155732083831946871533453543 233598125747920307300180315)
  ·
    refine ⟨350397188621880460950270473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233598125747920307300180315 350397188621880460950270473)
    ·
      refine ⟨262797891466410345712702855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350397188621880460950270473 262797891466410345712702855)
      ·
        refine ⟨394196837199615518569054283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262797891466410345712702855 394196837199615518569054283)
        ·
          refine ⟨591295255799423277853581425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394196837199615518569054283 591295255799423277853581425)
          ·
            refine ⟨443471441849567458390186069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591295255799423277853581425 443471441849567458390186069)
            ·
              refine ⟨5196930959174618653009993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 443471441849567458390186069 5196930959174618653009993)
              ·
                refine ⟨3897698219380963989757495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5196930959174618653009993 3897698219380963989757495)
                ·
                  refine ⟨5846547329071445984636243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897698219380963989757495 5846547329071445984636243)
                  ·
                    refine ⟨8769820993607168976954365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846547329071445984636243 8769820993607168976954365)
                    ·
                      refine ⟨3288682872602688366357887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769820993607168976954365 3288682872602688366357887)
                      ·
                        rfl

theorem cell23_6404687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 1, 3].length) (baseStart_6404687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404687 prefixEnd_6404687 := by exact prefixLift 6404687
  have htrace : WordTrace (prefixWord ++ tailWord_6404687) baseStart_6404687 baseEnd_6404687 := by
    simpa [prefixWord, tailWord_6404687, baseEnd_6404687] using wordTrace_append hprefix tailTrace_6404687
  have hstable : (prefixWord ++ tailWord_6404687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404687).length < 2 ^ (prefixWord ++ tailWord_6404687).sum := by decide
  have hdescent : baseEnd_6404687 < baseStart_6404687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404696 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6404696 : Nat := 118140960795 + 6404696 * 2 ^ 59
def prefixEnd_6404696 : Nat := 4983230072969 + 3 ^ 40 * 6404696 * 2
def baseEnd_6404696 : Nat := 3288687493928578831145345

theorem tailTrace_6404696 : CollatzResearch.WordTrace tailWord_6404696 prefixEnd_6404696 3288687493928578831145345 := by
  unfold tailWord_6404696
  simp only [CollatzResearch.WordTrace]
  refine ⟨116799227002443850918628971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155732302669925134558171961 116799227002443850918628971)
  ·
    refine ⟨175198840503665776377943457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116799227002443850918628971 175198840503665776377943457)
    ·
      refine ⟨131399130377749332283457593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175198840503665776377943457 131399130377749332283457593)
      ·
        refine ⟨98549347783311999212593195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131399130377749332283457593 98549347783311999212593195)
        ·
          refine ⟨147824021674967998818889793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98549347783311999212593195 147824021674967998818889793)
          ·
            refine ⟨110868016256225999114167345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147824021674967998818889793 110868016256225999114167345)
            ·
              refine ⟨83151012192169499335625509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110868016256225999114167345 83151012192169499335625509)
              ·
                refine ⟨15590814786031781125429783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83151012192169499335625509 15590814786031781125429783)
                ·
                  refine ⟨23386222179047671688144675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15590814786031781125429783 23386222179047671688144675)
                  ·
                    refine ⟨35079333268571507532217013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23386222179047671688144675 35079333268571507532217013)
                    ·
                      refine ⟨3288687493928578831145345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35079333268571507532217013 3288687493928578831145345)
                      ·
                        rfl

theorem cell23_6404696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6404696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404696 prefixEnd_6404696 := by exact prefixLift 6404696
  have htrace : WordTrace (prefixWord ++ tailWord_6404696) baseStart_6404696 baseEnd_6404696 := by
    simpa [prefixWord, tailWord_6404696, baseEnd_6404696] using wordTrace_append hprefix tailTrace_6404696
  have hstable : (prefixWord ++ tailWord_6404696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404696).length < 2 ^ (prefixWord ++ tailWord_6404696).sum := by decide
  have hdescent : baseEnd_6404696 < baseStart_6404696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404713 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 3]
def baseStart_6404713 : Nat := 118140960795 + 6404713 * 2 ^ 59
def prefixEnd_6404713 : Nat := 4983230072969 + 3 ^ 40 * 6404713 * 2
def baseEnd_6404713 : Nat := 3288696223099705264632767

theorem tailTrace_6404713 : CollatzResearch.WordTrace tailWord_6404713 prefixEnd_6404713 3288696223099705264632767 := by
  unfold tailWord_6404713
  simp only [CollatzResearch.WordTrace]
  refine ⟨233599074045826113740626793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155732716030550742493751195 233599074045826113740626793)
  ·
    refine ⟨175199305534369585305470095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233599074045826113740626793 175199305534369585305470095)
    ·
      refine ⟨262798958301554377958205143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175199305534369585305470095 262798958301554377958205143)
      ·
        refine ⟨394198437452331566937307715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262798958301554377958205143 394198437452331566937307715)
        ·
          refine ⟨591297656178497350405961573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394198437452331566937307715 591297656178497350405961573)
          ·
            refine ⟨110868310533468253201117795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 591297656178497350405961573 110868310533468253201117795)
            ·
              refine ⟨166302465800202379801676693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110868310533468253201117795 166302465800202379801676693)
              ·
                refine ⟨7795428084384486553203595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166302465800202379801676693 7795428084384486553203595)
                ·
                  refine ⟨11693142126576729829805393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795428084384486553203595 11693142126576729829805393)
                  ·
                    refine ⟨8769856594932547372354045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11693142126576729829805393 8769856594932547372354045)
                    ·
                      refine ⟨3288696223099705264632767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8769856594932547372354045 3288696223099705264632767)
                      ·
                        rfl

theorem cell23_6404713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_6404713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404713 prefixEnd_6404713 := by exact prefixLift 6404713
  have htrace : WordTrace (prefixWord ++ tailWord_6404713) baseStart_6404713 baseEnd_6404713 := by
    simpa [prefixWord, tailWord_6404713, baseEnd_6404713] using wordTrace_append hprefix tailTrace_6404713
  have hstable : (prefixWord ++ tailWord_6404713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404713).length < 2 ^ (prefixWord ++ tailWord_6404713).sum := by decide
  have hdescent : baseEnd_6404713 < baseStart_6404713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404727 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 1, 2, 2]
def baseStart_6404727 : Nat := 118140960795 + 6404727 * 2 ^ 59
def prefixEnd_6404727 : Nat := 4983230072969 + 3 ^ 40 * 6404727 * 2
def baseEnd_6404727 : Nat := 3288703411828868209857703

theorem tailTrace_6404727 : CollatzResearch.WordTrace tailWord_6404727 prefixEnd_6404727 3288703411828868209857703 := by
  unfold tailWord_6404727
  simp only [CollatzResearch.WordTrace]
  refine ⟨233599584667775394131636435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155733056445183596087757623 233599584667775394131636435)
  ·
    refine ⟨350399377001663091197454653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233599584667775394131636435 350399377001663091197454653)
    ·
      refine ⟨131399766375623659199045495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350399377001663091197454653 131399766375623659199045495)
      ·
        refine ⟨197099649563435488798568243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131399766375623659199045495 197099649563435488798568243)
        ·
          refine ⟨295649474345153233197852365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197099649563435488798568243 295649474345153233197852365)
          ·
            refine ⟨110868552879432462449194637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295649474345153233197852365 110868552879432462449194637)
            ·
              refine ⟨41575707329787173418447989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110868552879432462449194637 41575707329787173418447989)
              ·
                refine ⟨3897722562167547507979499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41575707329787173418447989 3897722562167547507979499)
                ·
                  refine ⟨5846583843251321261969249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897722562167547507979499 5846583843251321261969249)
                  ·
                    refine ⟨4384937882438490946476937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5846583843251321261969249 4384937882438490946476937)
                    ·
                      refine ⟨3288703411828868209857703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384937882438490946476937 3288703411828868209857703)
                      ·
                        rfl

theorem cell23_6404727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_6404727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404727 prefixEnd_6404727 := by exact prefixLift 6404727
  have htrace : WordTrace (prefixWord ++ tailWord_6404727) baseStart_6404727 baseEnd_6404727 := by
    simpa [prefixWord, tailWord_6404727, baseEnd_6404727] using wordTrace_append hprefix tailTrace_6404727
  have hstable : (prefixWord ++ tailWord_6404727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404727).length < 2 ^ (prefixWord ++ tailWord_6404727).sum := by decide
  have hdescent : baseEnd_6404727 < baseStart_6404727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404817 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 2, 2, 2]
def baseStart_6404817 : Nat := 118140960795 + 6404817 * 2 ^ 59
def prefixEnd_6404817 : Nat := 4983230072969 + 3 ^ 40 * 6404817 * 2
def baseEnd_6404817 : Nat := 3288749625087772857732289

theorem tailTrace_6404817 : CollatzResearch.WordTrace tailWord_6404817 prefixEnd_6404817 3288749625087772857732289 := by
  unfold tailWord_6404817
  simp only [CollatzResearch.WordTrace]
  refine ⟨233602867237449339502412705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155735244824966226334941803 233602867237449339502412705)
  ·
    refine ⟨175202150428087004626809529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233602867237449339502412705 175202150428087004626809529)
    ·
      refine ⟨131401612821065253470107147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175202150428087004626809529 131401612821065253470107147)
      ·
        refine ⟨197102419231597880205160721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131401612821065253470107147 197102419231597880205160721)
        ·
          refine ⟨147826814423698410153870541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197102419231597880205160721 147826814423698410153870541)
          ·
            refine ⟨55435055408886903807701453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147826814423698410153870541 55435055408886903807701453)
            ·
              refine ⟨20788145778332588927888045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55435055408886903807701453 20788145778332588927888045)
              ·
                refine ⟨7795554666874720847958017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20788145778332588927888045 7795554666874720847958017)
                ·
                  refine ⟨5846666000156040635968513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7795554666874720847958017 5846666000156040635968513)
                  ·
                    refine ⟨4384999500117030476976385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5846666000156040635968513 4384999500117030476976385)
                    ·
                      refine ⟨3288749625087772857732289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4384999500117030476976385 3288749625087772857732289)
                      ·
                        rfl

theorem cell23_6404817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_6404817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404817 prefixEnd_6404817 := by exact prefixLift 6404817
  have htrace : WordTrace (prefixWord ++ tailWord_6404817) baseStart_6404817 baseEnd_6404817 := by
    simpa [prefixWord, tailWord_6404817, baseEnd_6404817] using wordTrace_append hprefix tailTrace_6404817
  have hstable : (prefixWord ++ tailWord_6404817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404817).length < 2 ^ (prefixWord ++ tailWord_6404817).sum := by decide
  have hdescent : baseEnd_6404817 < baseStart_6404817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404821 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6404821 : Nat := 118140960795 + 6404821 * 2 ^ 59
def prefixEnd_6404821 : Nat := 4983230072969 + 3 ^ 40 * 6404821 * 2
def baseEnd_6404821 : Nat := 3288751679010390842082271

theorem tailTrace_6404821 : CollatzResearch.WordTrace tailWord_6404821 prefixEnd_6404821 3288751679010390842082271 := by
  unfold tailWord_6404821
  simp only [CollatzResearch.WordTrace]
  refine ⟨233603013129434848185558317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155735342086289898790372211 233603013129434848185558317)
  ·
    refine ⟨87601129923538068069584369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233603013129434848185558317 87601129923538068069584369)
    ·
      refine ⟨65700847442653551052188277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87601129923538068069584369 65700847442653551052188277)
      ·
        refine ⟨6159454447748770411142651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65700847442653551052188277 6159454447748770411142651)
        ·
          refine ⟨9239181671623155616713977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6159454447748770411142651 9239181671623155616713977)
          ·
            refine ⟨6929386253717366712535483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9239181671623155616713977 6929386253717366712535483)
            ·
              refine ⟨10394079380576050068803225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929386253717366712535483 10394079380576050068803225)
              ·
                refine ⟨7795559535432037551602419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10394079380576050068803225 7795559535432037551602419)
                ·
                  refine ⟨11693339303148056327403629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795559535432037551602419 11693339303148056327403629)
                  ·
                    refine ⟨4385002238680521122776361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11693339303148056327403629 4385002238680521122776361)
                    ·
                      refine ⟨3288751679010390842082271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385002238680521122776361 3288751679010390842082271)
                      ·
                        rfl

theorem cell23_6404821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6404821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404821 prefixEnd_6404821 := by exact prefixLift 6404821
  have htrace : WordTrace (prefixWord ++ tailWord_6404821) baseStart_6404821 baseEnd_6404821 := by
    simpa [prefixWord, tailWord_6404821, baseEnd_6404821] using wordTrace_append hprefix tailTrace_6404821
  have hstable : (prefixWord ++ tailWord_6404821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404821).length < 2 ^ (prefixWord ++ tailWord_6404821).sum := by decide
  have hdescent : baseEnd_6404821 < baseStart_6404821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404860 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_6404860 : Nat := 118140960795 + 6404860 * 2 ^ 59
def prefixEnd_6404860 : Nat := 4983230072969 + 3 ^ 40 * 6404860 * 2
def baseEnd_6404860 : Nat := 3288771704755916189494591

theorem tailTrace_6404860 : CollatzResearch.WordTrace tailWord_6404860 prefixEnd_6404860 3288771704755916189494591 := by
  unfold tailWord_6404860
  simp only [CollatzResearch.WordTrace]
  refine ⟨116802217788146778923114017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155736290384195705230818689 116802217788146778923114017)
  ·
    refine ⟨87601663341110084192335513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116802217788146778923114017 87601663341110084192335513)
    ·
      refine ⟨65701247505832563144251635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87601663341110084192335513 65701247505832563144251635)
      ·
        refine ⟨98551871258748844716377453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65701247505832563144251635 98551871258748844716377453)
        ·
          refine ⟨36956951722030816768641545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98551871258748844716377453 36956951722030816768641545)
          ·
            refine ⟨27717713791523112576481159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36956951722030816768641545 27717713791523112576481159)
            ·
              refine ⟨41576570687284668864721739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27717713791523112576481159 41576570687284668864721739)
              ·
                refine ⟨62364856030927003297082609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41576570687284668864721739 62364856030927003297082609)
                ·
                  refine ⟨46773642023195252472811957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62364856030927003297082609 46773642023195252472811957)
                  ·
                    refine ⟨4385028939674554919326121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46773642023195252472811957 4385028939674554919326121)
                    ·
                      refine ⟨3288771704755916189494591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385028939674554919326121 3288771704755916189494591)
                      ·
                        rfl

theorem cell23_6404860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_6404860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404860 prefixEnd_6404860 := by exact prefixLift 6404860
  have htrace : WordTrace (prefixWord ++ tailWord_6404860) baseStart_6404860 baseEnd_6404860 := by
    simpa [prefixWord, tailWord_6404860, baseEnd_6404860] using wordTrace_append hprefix tailTrace_6404860
  have hstable : (prefixWord ++ tailWord_6404860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404860).length < 2 ^ (prefixWord ++ tailWord_6404860).sum := by decide
  have hdescent : baseEnd_6404860 < baseStart_6404860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404873 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_6404873 : Nat := 118140960795 + 6404873 * 2 ^ 59
def prefixEnd_6404873 : Nat := 4983230072969 + 3 ^ 40 * 6404873 * 2
def baseEnd_6404873 : Nat := 3288778380004424638632031

theorem tailTrace_6404873 : CollatzResearch.WordTrace tailWord_6404873 prefixEnd_6404873 3288778380004424638632031 := by
  unfold tailWord_6404873
  simp only [CollatzResearch.WordTrace]
  refine ⟨233604909725246461066451273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155736606483497640710967515 233604909725246461066451273)
  ·
    refine ⟨175203682293934845799838455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233604909725246461066451273 175203682293934845799838455)
    ·
      refine ⟨262805523440902268699757683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175203682293934845799838455 262805523440902268699757683)
      ·
        refine ⟨394208285161353403049636525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262805523440902268699757683 394208285161353403049636525)
        ·
          refine ⟨147828106935507526143613697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394208285161353403049636525 147828106935507526143613697)
          ·
            refine ⟨110871080201630644607710273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147828106935507526143613697 110871080201630644607710273)
            ·
              refine ⟨83153310151222983455782705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110871080201630644607710273 83153310151222983455782705)
              ·
                refine ⟨62364982613417237591837029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83153310151222983455782705 62364982613417237591837029)
                ·
                  refine ⟨11693434240015732048469443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62364982613417237591837029 11693434240015732048469443)
                  ·
                    refine ⟨17540151360023598072704165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11693434240015732048469443 17540151360023598072704165)
                    ·
                      refine ⟨3288778380004424638632031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17540151360023598072704165 3288778380004424638632031)
                      ·
                        rfl

theorem cell23_6404873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_6404873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404873 prefixEnd_6404873 := by exact prefixLift 6404873
  have htrace : WordTrace (prefixWord ++ tailWord_6404873) baseStart_6404873 baseEnd_6404873 := by
    simpa [prefixWord, tailWord_6404873, baseEnd_6404873] using wordTrace_append hprefix tailTrace_6404873
  have hstable : (prefixWord ++ tailWord_6404873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404873).length < 2 ^ (prefixWord ++ tailWord_6404873).sum := by decide
  have hdescent : baseEnd_6404873 < baseStart_6404873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404887 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 2, 5]
def baseStart_6404887 : Nat := 118140960795 + 6404887 * 2 ^ 59
def prefixEnd_6404887 : Nat := 4983230072969 + 3 ^ 40 * 6404887 * 2
def baseEnd_6404887 : Nat := 1096261856244529194618989

theorem tailTrace_6404887 : CollatzResearch.WordTrace tailWord_6404887 prefixEnd_6404887 1096261856244529194618989 := by
  unfold tailWord_6404887
  simp only [CollatzResearch.WordTrace]
  refine ⟨233605420347195741457460915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155736946898130494304973943 233605420347195741457460915)
  ·
    refine ⟨350408130520793612186191373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233605420347195741457460915 350408130520793612186191373)
    ·
      refine ⟨131403048945297604569821765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350408130520793612186191373 131403048945297604569821765)
      ·
        refine ⟨24638071677243300856841581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131403048945297604569821765 24638071677243300856841581)
        ·
          refine ⟨9239276878966237821315593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24638071677243300856841581 9239276878966237821315593)
          ·
            refine ⟨6929457659224678365986695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9239276878966237821315593 6929457659224678365986695)
            ·
              refine ⟨10394186488837017548980043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929457659224678365986695 10394186488837017548980043)
              ·
                refine ⟨15591279733255526323470065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10394186488837017548980043 15591279733255526323470065)
                ·
                  refine ⟨11693459799941644742602549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15591279733255526323470065 11693459799941644742602549)
                  ·
                    refine ⟨1096261856244529194618989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693459799941644742602549 1096261856244529194618989)
                    ·
                      rfl

theorem cell23_6404887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_6404887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404887 prefixEnd_6404887 := by exact prefixLift 6404887
  have htrace : WordTrace (prefixWord ++ tailWord_6404887) baseStart_6404887 baseEnd_6404887 := by
    simpa [prefixWord, tailWord_6404887, baseEnd_6404887] using wordTrace_append hprefix tailTrace_6404887
  have hstable : (prefixWord ++ tailWord_6404887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404887).length < 2 ^ (prefixWord ++ tailWord_6404887).sum := by decide
  have hdescent : baseEnd_6404887 < baseStart_6404887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404890 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2]
def baseStart_6404890 : Nat := 118140960795 + 6404890 * 2 ^ 59
def prefixEnd_6404890 : Nat := 4983230072969 + 3 ^ 40 * 6404890 * 2
def baseEnd_6404890 : Nat := 3288787109175551072119453

theorem tailTrace_6404890 : CollatzResearch.WordTrace tailWord_6404890 prefixEnd_6404890 3288787109175551072119453 := by
  unfold tailWord_6404890
  simp only [CollatzResearch.WordTrace]
  refine ⟨58401382441546218242455031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155737019844123248646546749 58401382441546218242455031)
  ·
    refine ⟨87602073662319327363682547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58401382441546218242455031 87602073662319327363682547)
    ·
      refine ⟨131403110493478991045523821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87602073662319327363682547 131403110493478991045523821)
      ·
        refine ⟨49276166435054621642071433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131403110493478991045523821 49276166435054621642071433)
        ·
          refine ⟨36957124826290966231553575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49276166435054621642071433 36957124826290966231553575)
          ·
            refine ⟨55435687239436449347330363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36957124826290966231553575 55435687239436449347330363)
            ·
              refine ⟨83153530859154674020995545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55435687239436449347330363 83153530859154674020995545)
              ·
                refine ⟨62365148144366005515746659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83153530859154674020995545 62365148144366005515746659)
                ·
                  refine ⟨93547722216549008273619989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62365148144366005515746659 93547722216549008273619989)
                  ·
                    refine ⟨4385049478900734762825937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93547722216549008273619989 4385049478900734762825937)
                    ·
                      refine ⟨3288787109175551072119453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385049478900734762825937 3288787109175551072119453)
                      ·
                        rfl

theorem cell23_6404890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_6404890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404890 prefixEnd_6404890 := by exact prefixLift 6404890
  have htrace : WordTrace (prefixWord ++ tailWord_6404890) baseStart_6404890 baseEnd_6404890 := by
    simpa [prefixWord, tailWord_6404890, baseEnd_6404890] using wordTrace_append hprefix tailTrace_6404890
  have hstable : (prefixWord ++ tailWord_6404890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404890).length < 2 ^ (prefixWord ++ tailWord_6404890).sum := by decide
  have hdescent : baseEnd_6404890 < baseStart_6404890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404913 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 8]
def baseStart_6404913 : Nat := 118140960795 + 6404913 * 2 ^ 59
def prefixEnd_6404913 : Nat := 4983230072969 + 3 ^ 40 * 6404913 * 2
def baseEnd_6404913 : Nat := 365422102136733831347983

theorem tailTrace_6404913 : CollatzResearch.WordTrace tailWord_6404913 prefixEnd_6404913 365422102136733831347983 := by
  unfold tailWord_6404913
  simp only [CollatzResearch.WordTrace]
  refine ⟨233606368645101547897907393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155737579096734365265271595 233606368645101547897907393)
  ·
    refine ⟨175204776483826160923430545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233606368645101547897907393 175204776483826160923430545)
    ·
      refine ⟨131403582362869620692572909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175204776483826160923430545 131403582362869620692572909)
      ·
        refine ⟨49276343386076107759714841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131403582362869620692572909 49276343386076107759714841)
        ·
          refine ⟨36957257539557080819786131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49276343386076107759714841 36957257539557080819786131)
          ·
            refine ⟨55435886309335621229679197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36957257539557080819786131 55435886309335621229679197)
            ·
              refine ⟨20788457366000857961129699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55435886309335621229679197 20788457366000857961129699)
              ·
                refine ⟨31182686049001286941694549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20788457366000857961129699 31182686049001286941694549)
                ·
                  refine ⟨365422102136733831347983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31182686049001286941694549 365422102136733831347983)
                  ·
                    rfl

theorem cell23_6404913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_6404913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404913 prefixEnd_6404913 := by exact prefixLift 6404913
  have htrace : WordTrace (prefixWord ++ tailWord_6404913) baseStart_6404913 baseEnd_6404913 := by
    simpa [prefixWord, tailWord_6404913, baseEnd_6404913] using wordTrace_append hprefix tailTrace_6404913
  have hstable : (prefixWord ++ tailWord_6404913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404913).length < 2 ^ (prefixWord ++ tailWord_6404913).sum := by decide
  have hdescent : baseEnd_6404913 < baseStart_6404913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404917 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6404917 : Nat := 118140960795 + 6404917 * 2 ^ 59
def prefixEnd_6404917 : Nat := 4983230072969 + 3 ^ 40 * 6404917 * 2
def baseEnd_6404917 : Nat := 1096266991051074155493943

theorem tailTrace_6404917 : CollatzResearch.WordTrace tailWord_6404917 prefixEnd_6404917 1096266991051074155493943 := by
  unfold tailWord_6404917
  simp only [CollatzResearch.WordTrace]
  refine ⟨233606514537087056581053005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155737676358058037720702003 233606514537087056581053005)
  ·
    refine ⟨87602442951407646217894877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233606514537087056581053005 87602442951407646217894877)
    ·
      refine ⟨32850916106777867331710579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87602442951407646217894877 32850916106777867331710579)
      ·
        refine ⟨49276374160166800997565869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32850916106777867331710579 49276374160166800997565869)
        ·
          refine ⟨18478640310062550374087201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49276374160166800997565869 18478640310062550374087201)
          ·
            refine ⟨13858980232546912780565401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18478640310062550374087201 13858980232546912780565401)
            ·
              refine ⟨10394235174410184585424051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13858980232546912780565401 10394235174410184585424051)
              ·
                refine ⟨15591352761615276878136077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10394235174410184585424051 15591352761615276878136077)
                ·
                  refine ⟨5846757285605728829301029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15591352761615276878136077 5846757285605728829301029)
                  ·
                    refine ⟨1096266991051074155493943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5846757285605728829301029 1096266991051074155493943)
                    ·
                      rfl

theorem cell23_6404917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6404917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404917 prefixEnd_6404917 := by exact prefixLift 6404917
  have htrace : WordTrace (prefixWord ++ tailWord_6404917) baseStart_6404917 baseEnd_6404917 := by
    simpa [prefixWord, tailWord_6404917, baseEnd_6404917] using wordTrace_append hprefix tailTrace_6404917
  have hstable : (prefixWord ++ tailWord_6404917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404917).length < 2 ^ (prefixWord ++ tailWord_6404917).sum := by decide
  have hdescent : baseEnd_6404917 < baseStart_6404917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404960 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 1, 5]
def baseStart_6404960 : Nat := 118140960795 + 6404960 * 2 ^ 59
def prefixEnd_6404960 : Nat := 4983230072969 + 3 ^ 40 * 6404960 * 2
def baseEnd_6404960 : Nat := 1096274350940455266081377

theorem tailTrace_6404960 : CollatzResearch.WordTrace tailWord_6404960 prefixEnd_6404960 1096274350940455266081377 := by
  unfold tailWord_6404960
  simp only [CollatzResearch.WordTrace]
  refine ⟨116804041437965637462434167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155738721917287516616578889 116804041437965637462434167)
  ·
    refine ⟨175206062156948456193651251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116804041437965637462434167 175206062156948456193651251)
    ·
      refine ⟨262809093235422684290476877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175206062156948456193651251 262809093235422684290476877)
      ·
        refine ⟨98553409963283506608928829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262809093235422684290476877 98553409963283506608928829)
        ·
          refine ⟨36957528736231314978348311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98553409963283506608928829 36957528736231314978348311)
          ·
            refine ⟨55436293104346972467522467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36957528736231314978348311 55436293104346972467522467)
            ·
              refine ⟨83154439656520458701283701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55436293104346972467522467 83154439656520458701283701)
              ·
                refine ⟨7795728717798793003245347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83154439656520458701283701 7795728717798793003245347)
                ·
                  refine ⟨11693593076698189504868021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795728717798793003245347 11693593076698189504868021)
                  ·
                    refine ⟨1096274350940455266081377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693593076698189504868021 1096274350940455266081377)
                    ·
                      rfl

theorem cell23_6404960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_6404960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404960 prefixEnd_6404960 := by exact prefixLift 6404960
  have htrace : WordTrace (prefixWord ++ tailWord_6404960) baseStart_6404960 baseEnd_6404960 := by
    simpa [prefixWord, tailWord_6404960, baseEnd_6404960] using wordTrace_append hprefix tailTrace_6404960
  have hstable : (prefixWord ++ tailWord_6404960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404960).length < 2 ^ (prefixWord ++ tailWord_6404960).sum := by decide
  have hdescent : baseEnd_6404960 < baseStart_6404960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404967 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_6404967 : Nat := 118140960795 + 6404967 * 2 ^ 59
def prefixEnd_6404967 : Nat := 4983230072969 + 3 ^ 40 * 6404967 * 2
def baseEnd_6404967 : Nat := 3288826647185947270856599

theorem tailTrace_6404967 : CollatzResearch.WordTrace tailWord_6404967 prefixEnd_6404967 3288826647185947270856599 := by
  unfold tailWord_6404967
  simp only [CollatzResearch.WordTrace]
  refine ⟨233608338186905915120373155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155738892124603943413582103 233608338186905915120373155)
  ·
    refine ⟨350412507280358872680559733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233608338186905915120373155 350412507280358872680559733)
    ·
      refine ⟨32851172557533644313802475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 350412507280358872680559733 32851172557533644313802475)
      ·
        refine ⟨49276758836300466470703713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32851172557533644313802475 49276758836300466470703713)
        ·
          refine ⟨36957569127225349853027785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49276758836300466470703713 36957569127225349853027785)
          ·
            refine ⟨27718176845419012389770839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36957569127225349853027785 27718176845419012389770839)
            ·
              refine ⟨41577265268128518584656259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27718176845419012389770839 41577265268128518584656259)
              ·
                refine ⟨62365897902192777876984389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41577265268128518584656259 62365897902192777876984389)
                ·
                  refine ⟨11693605856661145851934573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62365897902192777876984389 11693605856661145851934573)
                  ·
                    refine ⟨4385102196247929694475465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11693605856661145851934573 4385102196247929694475465)
                    ·
                      refine ⟨3288826647185947270856599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385102196247929694475465 3288826647185947270856599)
                      ·
                        rfl

theorem cell23_6404967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_6404967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404967 prefixEnd_6404967 := by exact prefixLift 6404967
  have htrace : WordTrace (prefixWord ++ tailWord_6404967) baseStart_6404967 baseEnd_6404967 := by
    simpa [prefixWord, tailWord_6404967, baseEnd_6404967] using wordTrace_append hprefix tailTrace_6404967
  have hstable : (prefixWord ++ tailWord_6404967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404967).length < 2 ^ (prefixWord ++ tailWord_6404967).sum := by decide
  have hdescent : baseEnd_6404967 < baseStart_6404967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6404997 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_6404997 : Nat := 118140960795 + 6404997 * 2 ^ 59
def prefixEnd_6404997 : Nat := 4983230072969 + 3 ^ 40 * 6404997 * 2
def baseEnd_6404997 : Nat := 3288842051605582153481461

theorem tailTrace_6404997 : CollatzResearch.WordTrace tailWord_6404997 prefixEnd_6404997 3288842051605582153481461 := by
  unfold tailWord_6404997
  simp only [CollatzResearch.WordTrace]
  refine ⟨233609432376797230243965245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155739621584531486829310163 233609432376797230243965245)
  ·
    refine ⟨87603537141298961341486967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233609432376797230243965245 87603537141298961341486967)
    ·
      refine ⟨131405305711948442012230451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87603537141298961341486967 131405305711948442012230451)
      ·
        refine ⟨197107958567922663018345677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131405305711948442012230451 197107958567922663018345677)
        ·
          refine ⟨73915484462970998631879629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197107958567922663018345677 73915484462970998631879629)
          ·
            refine ⟨27718306673614124486954861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73915484462970998631879629 27718306673614124486954861)
            ·
              refine ⟨10394365002605296682608073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27718306673614124486954861 10394365002605296682608073)
              ·
                refine ⟨7795773751953972511956055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10394365002605296682608073 7795773751953972511956055)
                ·
                  refine ⟨11693660627930958767934083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795773751953972511956055 11693660627930958767934083)
                  ·
                    refine ⟨17540490941896438151901125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11693660627930958767934083 17540490941896438151901125)
                    ·
                      refine ⟨3288842051605582153481461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17540490941896438151901125 3288842051605582153481461)
                      ·
                        rfl

theorem cell23_6404997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_6404997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6404997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6404997 prefixEnd_6404997 := by exact prefixLift 6404997
  have htrace : WordTrace (prefixWord ++ tailWord_6404997) baseStart_6404997 baseEnd_6404997 := by
    simpa [prefixWord, tailWord_6404997, baseEnd_6404997] using wordTrace_append hprefix tailTrace_6404997
  have hstable : (prefixWord ++ tailWord_6404997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6404997).length < 2 ^ (prefixWord ++ tailWord_6404997).sum := by decide
  have hdescent : baseEnd_6404997 < baseStart_6404997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6404997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405003 : List Nat := [1, 1, 1, 1, 4, 2, 4, 9]
def baseStart_6405003 : Nat := 118140960795 + 6405003 * 2 ^ 59
def prefixEnd_6405003 : Nat := 4983230072969 + 3 ^ 40 * 6405003 * 2
def baseEnd_6405003 : Nat := 121809078981092930740979

theorem tailTrace_6405003 : CollatzResearch.WordTrace tailWord_6405003 prefixEnd_6405003 121809078981092930740979 := by
  unfold tailWord_6405003
  simp only [CollatzResearch.WordTrace]
  refine ⟨233609651214775493268683663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155739767476516995512455775 233609651214775493268683663)
  ·
    refine ⟨350414476822163239903025495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233609651214775493268683663 350414476822163239903025495)
    ·
      refine ⟨525621715233244859854538243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350414476822163239903025495 525621715233244859854538243)
      ·
        refine ⟨788432572849867289781807365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525621715233244859854538243 788432572849867289781807365)
        ·
          refine ⟨147831107409350116834088881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 788432572849867289781807365 147831107409350116834088881)
          ·
            refine ⟨110873330557012587625566661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147831107409350116834088881 110873330557012587625566661)
            ·
              refine ⟨20788749479439860179793749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110873330557012587625566661 20788749479439860179793749)
              ·
                refine ⟨121809078981092930740979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20788749479439860179793749 121809078981092930740979)
                ·
                  rfl

theorem cell23_6405003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 9].length) (baseStart_6405003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405003 prefixEnd_6405003 := by exact prefixLift 6405003
  have htrace : WordTrace (prefixWord ++ tailWord_6405003) baseStart_6405003 baseEnd_6405003 := by
    simpa [prefixWord, tailWord_6405003, baseEnd_6405003] using wordTrace_append hprefix tailTrace_6405003
  have hstable : (prefixWord ++ tailWord_6405003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405003).length < 2 ^ (prefixWord ++ tailWord_6405003).sum := by decide
  have hdescent : baseEnd_6405003 < baseStart_6405003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405020 : List Nat := [2, 2, 3, 3, 2, 11]
def baseStart_6405020 : Nat := 118140960795 + 6405020 * 2 ^ 59
def prefixEnd_6405020 : Nat := 4983230072969 + 3 ^ 40 * 6405020 * 2
def baseEnd_6405020 : Nat := 13534378031525249232485

theorem tailTrace_6405020 : CollatzResearch.WordTrace tailWord_6405020 prefixEnd_6405020 13534378031525249232485 := by
  unfold tailWord_6405020
  simp only [CollatzResearch.WordTrace]
  refine ⟨116805135627856952586026257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155740180837142603448035009 116805135627856952586026257)
  ·
    refine ⟨87603851720892714439519693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116805135627856952586026257 87603851720892714439519693)
    ·
      refine ⟨32851444395334767914819885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87603851720892714439519693 32851444395334767914819885)
      ·
        refine ⟨12319291648250537968057457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32851444395334767914819885 12319291648250537968057457)
        ·
          refine ⟨9239468736187903476043093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12319291648250537968057457 9239468736187903476043093)
          ·
            refine ⟨13534378031525249232485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9239468736187903476043093 13534378031525249232485)
            ·
              rfl

theorem cell23_6405020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 11].length) (baseStart_6405020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405020 prefixEnd_6405020 := by exact prefixLift 6405020
  have htrace : WordTrace (prefixWord ++ tailWord_6405020) baseStart_6405020 baseEnd_6405020 := by
    simpa [prefixWord, tailWord_6405020, baseEnd_6405020] using wordTrace_append hprefix tailTrace_6405020
  have hstable : (prefixWord ++ tailWord_6405020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405020).length < 2 ^ (prefixWord ++ tailWord_6405020).sum := by decide
  have hdescent : baseEnd_6405020 < baseStart_6405020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405033 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_6405033 : Nat := 118140960795 + 6405033 * 2 ^ 59
def prefixEnd_6405033 : Nat := 4983230072969 + 3 ^ 40 * 6405033 * 2
def baseEnd_6405033 : Nat := 1096286845636381337543765

theorem tailTrace_6405033 : CollatzResearch.WordTrace tailWord_6405033 prefixEnd_6405033 1096286845636381337543765 := by
  unfold tailWord_6405033
  simp only [CollatzResearch.WordTrace]
  refine ⟨233610745404666808392275753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155740496936444538928183835 233610745404666808392275753)
  ·
    refine ⟨175208059053500106294206815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233610745404666808392275753 175208059053500106294206815)
    ·
      refine ⟨262812088580250159441310223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175208059053500106294206815 262812088580250159441310223)
      ·
        refine ⟨394218132870375239161965335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262812088580250159441310223 394218132870375239161965335)
        ·
          refine ⟨591327199305562858742948003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394218132870375239161965335 591327199305562858742948003)
          ·
            refine ⟨886990798958344288114422005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591327199305562858742948003 886990798958344288114422005)
            ·
              refine ⟨83155387402344777010727063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 886990798958344288114422005 83155387402344777010727063)
              ·
                refine ⟨124733081103517165516090595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83155387402344777010727063 124733081103517165516090595)
                ·
                  refine ⟨187099621655275748274135893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124733081103517165516090595 187099621655275748274135893)
                  ·
                    refine ⟨1096286845636381337543765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187099621655275748274135893 1096286845636381337543765)
                    ·
                      rfl

theorem cell23_6405033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_6405033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405033 prefixEnd_6405033 := by exact prefixLift 6405033
  have htrace : WordTrace (prefixWord ++ tailWord_6405033) baseStart_6405033 baseEnd_6405033 := by
    simpa [prefixWord, tailWord_6405033, baseEnd_6405033] using wordTrace_append hprefix tailTrace_6405033
  have hstable : (prefixWord ++ tailWord_6405033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405033).length < 2 ^ (prefixWord ++ tailWord_6405033).sum := by decide
  have hdescent : baseEnd_6405033 < baseStart_6405033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405044 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6405044 : Nat := 118140960795 + 6405044 * 2 ^ 59
def prefixEnd_6405044 : Nat := 4983230072969 + 3 ^ 40 * 6405044 * 2
def baseEnd_6405044 : Nat := 3288866185196343469593745

theorem tailTrace_6405044 : CollatzResearch.WordTrace tailWord_6405044 prefixEnd_6405044 3288866185196343469593745 := by
  unfold tailWord_6405044
  simp only [CollatzResearch.WordTrace]
  refine ⟨116805573303813478635463093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155740764405084638180617457 116805573303813478635463093)
  ·
    refine ⟨10950522497232513622074665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116805573303813478635463093 10950522497232513622074665)
    ·
      refine ⟨8212891872924385216555999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10950522497232513622074665 8212891872924385216555999)
      ·
        refine ⟨12319337809386577824833999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212891872924385216555999 12319337809386577824833999)
        ·
          refine ⟨18479006714079866737250999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12319337809386577824833999 18479006714079866737250999)
          ·
            refine ⟨27718510071119800105876499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18479006714079866737250999 27718510071119800105876499)
            ·
              refine ⟨41577765106679700158814749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27718510071119800105876499 41577765106679700158814749)
              ·
                refine ⟨15591661915004887559555531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41577765106679700158814749 15591661915004887559555531)
                ·
                  refine ⟨23387492872507331339333297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15591661915004887559555531 23387492872507331339333297)
                  ·
                    refine ⟨17540619654380498504499973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23387492872507331339333297 17540619654380498504499973)
                    ·
                      refine ⟨3288866185196343469593745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17540619654380498504499973 3288866185196343469593745)
                      ·
                        rfl

theorem cell23_6405044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6405044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405044 prefixEnd_6405044 := by exact prefixLift 6405044
  have htrace : WordTrace (prefixWord ++ tailWord_6405044) baseStart_6405044 baseEnd_6405044 := by
    simpa [prefixWord, tailWord_6405044, baseEnd_6405044] using wordTrace_append hprefix tailTrace_6405044
  have hstable : (prefixWord ++ tailWord_6405044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405044).length < 2 ^ (prefixWord ++ tailWord_6405044).sum := by decide
  have hdescent : baseEnd_6405044 < baseStart_6405044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405062 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6405062 : Nat := 118140960795 + 6405062 * 2 ^ 59
def prefixEnd_6405062 : Nat := 4983230072969 + 3 ^ 40 * 6405062 * 2
def baseEnd_6405062 : Nat := 1096291809282708133056221

theorem tailTrace_6405062 : CollatzResearch.WordTrace tailWord_6405062 prefixEnd_6405062 1096291809282708133056221 := by
  unfold tailWord_6405062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300368847548804573283795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155741202081041164230054293 7300368847548804573283795)
  ·
    refine ⟨10950553271323206859925693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300368847548804573283795 10950553271323206859925693)
    ·
      refine ⟨4106457476746202572472135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10950553271323206859925693 4106457476746202572472135)
      ·
        refine ⟨6159686215119303858708203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106457476746202572472135 6159686215119303858708203)
        ·
          refine ⟨9239529322678955788062305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6159686215119303858708203 9239529322678955788062305)
          ·
            refine ⟨6929646992009216841046729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9239529322678955788062305 6929646992009216841046729)
            ·
              refine ⟨5197235244006912630785047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6929646992009216841046729 5197235244006912630785047)
              ·
                refine ⟨7795852866010368946177571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5197235244006912630785047 7795852866010368946177571)
                ·
                  refine ⟨11693779299015553419266357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795852866010368946177571 11693779299015553419266357)
                  ·
                    refine ⟨1096291809282708133056221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693779299015553419266357 1096291809282708133056221)
                    ·
                      rfl

theorem cell23_6405062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6405062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405062 prefixEnd_6405062 := by exact prefixLift 6405062
  have htrace : WordTrace (prefixWord ++ tailWord_6405062) baseStart_6405062 baseEnd_6405062 := by
    simpa [prefixWord, tailWord_6405062, baseEnd_6405062] using wordTrace_append hprefix tailTrace_6405062
  have hstable : (prefixWord ++ tailWord_6405062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405062).length < 2 ^ (prefixWord ++ tailWord_6405062).sum := by decide
  have hdescent : baseEnd_6405062 < baseStart_6405062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405080 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_6405080 : Nat := 118140960795 + 6405080 * 2 ^ 59
def prefixEnd_6405080 : Nat := 4983230072969 + 3 ^ 40 * 6405080 * 2
def baseEnd_6405080 : Nat := 1096294890166635109581193

theorem tailTrace_6405080 : CollatzResearch.WordTrace tailWord_6405080 prefixEnd_6405080 1096294890166635109581193 := by
  unfold tailWord_6405080
  simp only [CollatzResearch.WordTrace]
  refine ⟨116806229817748267709618347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155741639756997690279491129 116806229817748267709618347)
  ·
    refine ⟨175209344726622401564427521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116806229817748267709618347 175209344726622401564427521)
    ·
      refine ⟨131407008544966801173320641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175209344726622401564427521 131407008544966801173320641)
      ·
        refine ⟨98555256408725100879990481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131407008544966801173320641 98555256408725100879990481)
        ·
          refine ⟨73916442306543825659992861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98555256408725100879990481 73916442306543825659992861)
          ·
            refine ⟨27718665864953934622497323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73916442306543825659992861 27718665864953934622497323)
            ·
              refine ⟨41577998797430901933745985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27718665864953934622497323 41577998797430901933745985)
              ·
                refine ⟨31183499098073176450309489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41577998797430901933745985 31183499098073176450309489)
                ·
                  refine ⟨23387624323554882337732117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31183499098073176450309489 23387624323554882337732117)
                  ·
                    refine ⟨1096294890166635109581193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23387624323554882337732117 1096294890166635109581193)
                    ·
                      rfl

theorem cell23_6405080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_6405080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405080 prefixEnd_6405080 := by exact prefixLift 6405080
  have htrace : WordTrace (prefixWord ++ tailWord_6405080) baseStart_6405080 baseEnd_6405080 := by
    simpa [prefixWord, tailWord_6405080, baseEnd_6405080] using wordTrace_append hprefix tailTrace_6405080
  have hstable : (prefixWord ++ tailWord_6405080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405080).length < 2 ^ (prefixWord ++ tailWord_6405080).sum := by decide
  have hdescent : baseEnd_6405080 < baseStart_6405080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405081 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 3]
def baseStart_6405081 : Nat := 118140960795 + 6405081 * 2 ^ 59
def prefixEnd_6405081 : Nat := 4983230072969 + 3 ^ 40 * 6405081 * 2
def baseEnd_6405081 : Nat := 3288885183980559824831075

theorem tailTrace_6405081 : CollatzResearch.WordTrace tailWord_6405081 prefixEnd_6405081 3288885183980559824831075 := by
  unfold tailWord_6405081
  simp only [CollatzResearch.WordTrace]
  refine ⟨233612496108492912590023097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155741664072328608393348731 233612496108492912590023097)
  ·
    refine ⟨175209372081369684442517323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233612496108492912590023097 175209372081369684442517323)
    ·
      refine ⟨262814058122054526663775985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175209372081369684442517323 262814058122054526663775985)
      ·
        refine ⟨197110543591540894997831989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262814058122054526663775985 197110543591540894997831989)
        ·
          refine ⟨18479113461706958906046749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197110543591540894997831989 18479113461706958906046749)
          ·
            refine ⟨6929667548140109589767531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18479113461706958906046749 6929667548140109589767531)
            ·
              refine ⟨10394501322210164384651297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929667548140109589767531 10394501322210164384651297)
              ·
                refine ⟨7795875991657623288488473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10394501322210164384651297 7795875991657623288488473)
                ·
                  refine ⟨5846906993743217466366355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7795875991657623288488473 5846906993743217466366355)
                  ·
                    refine ⟨8770360490614826199549533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846906993743217466366355 8770360490614826199549533)
                    ·
                      refine ⟨3288885183980559824831075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8770360490614826199549533 3288885183980559824831075)
                      ·
                        rfl

theorem cell23_6405081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_6405081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405081 prefixEnd_6405081 := by exact prefixLift 6405081
  have htrace : WordTrace (prefixWord ++ tailWord_6405081) baseStart_6405081 baseEnd_6405081 := by
    simpa [prefixWord, tailWord_6405081, baseEnd_6405081] using wordTrace_append hprefix tailTrace_6405081
  have hstable : (prefixWord ++ tailWord_6405081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405081).length < 2 ^ (prefixWord ++ tailWord_6405081).sum := by decide
  have hdescent : baseEnd_6405081 < baseStart_6405081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405174 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6405174 : Nat := 118140960795 + 6405174 * 2 ^ 59
def prefixEnd_6405174 : Nat := 4983230072969 + 3 ^ 40 * 6405174 * 2
def baseEnd_6405174 : Nat := 1096310979227142653656049

theorem tailTrace_6405174 : CollatzResearch.WordTrace tailWord_6405174 prefixEnd_6405174 1096310979227142653656049 := by
  unfold tailWord_6405174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14600993006072249342072411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155743925398103992982105717 14600993006072249342072411)
  ·
    refine ⟨21901489509108374013108617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14600993006072249342072411 21901489509108374013108617)
    ·
      refine ⟨16426117131831280509831463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21901489509108374013108617 16426117131831280509831463)
      ·
        refine ⟨24639175697746920764747195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16426117131831280509831463 24639175697746920764747195)
        ·
          refine ⟨36958763546620381147120793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24639175697746920764747195 36958763546620381147120793)
          ·
            refine ⟨27719072659965285860340595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36958763546620381147120793 27719072659965285860340595)
            ·
              refine ⟨41578608989947928790510893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27719072659965285860340595 41578608989947928790510893)
              ·
                refine ⟨15591978371230473296441585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41578608989947928790510893 15591978371230473296441585)
                ·
                  refine ⟨11693983778422854972331189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15591978371230473296441585 11693983778422854972331189)
                  ·
                    refine ⟨1096310979227142653656049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693983778422854972331189 1096310979227142653656049)
                    ·
                      rfl

theorem cell23_6405174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6405174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405174 prefixEnd_6405174 := by exact prefixLift 6405174
  have htrace : WordTrace (prefixWord ++ tailWord_6405174) baseStart_6405174 baseEnd_6405174 := by
    simpa [prefixWord, tailWord_6405174, baseEnd_6405174] using wordTrace_append hprefix tailTrace_6405174
  have hstable : (prefixWord ++ tailWord_6405174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405174).length < 2 ^ (prefixWord ++ tailWord_6405174).sum := by decide
  have hdescent : baseEnd_6405174 < baseStart_6405174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405200 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 8]
def baseStart_6405200 : Nat := 118140960795 + 6405200 * 2 ^ 59
def prefixEnd_6405200 : Nat := 4983230072969 + 3 ^ 40 * 6405200 * 2
def baseEnd_6405200 : Nat := 365438476464271651027003

theorem tailTrace_6405200 : CollatzResearch.WordTrace tailWord_6405200 prefixEnd_6405200 365438476464271651027003 := by
  unfold tailWord_6405200
  simp only [CollatzResearch.WordTrace]
  refine ⟨116808418197530897956802527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155744557596707863942403369 116808418197530897956802527)
  ·
    refine ⟨175212627296296346935203791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116808418197530897956802527 175212627296296346935203791)
    ·
      refine ⟨262818940944444520402805687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175212627296296346935203791 262818940944444520402805687)
      ·
        refine ⟨394228411416666780604208531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262818940944444520402805687 394228411416666780604208531)
        ·
          refine ⟨591342617125000170906312797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394228411416666780604208531 591342617125000170906312797)
          ·
            refine ⟨221753481421875064089867299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591342617125000170906312797 221753481421875064089867299)
            ·
              refine ⟨332630222132812596134800949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221753481421875064089867299 332630222132812596134800949)
              ·
                refine ⟨31184083324951180887637589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332630222132812596134800949 31184083324951180887637589)
                ·
                  refine ⟨365438476464271651027003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31184083324951180887637589 365438476464271651027003)
                  ·
                    rfl

theorem cell23_6405200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_6405200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405200 prefixEnd_6405200 := by exact prefixLift 6405200
  have htrace : WordTrace (prefixWord ++ tailWord_6405200) baseStart_6405200 baseEnd_6405200 := by
    simpa [prefixWord, tailWord_6405200, baseEnd_6405200] using wordTrace_append hprefix tailTrace_6405200
  have hstable : (prefixWord ++ tailWord_6405200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405200).length < 2 ^ (prefixWord ++ tailWord_6405200).sum := by decide
  have hdescent : baseEnd_6405200 < baseStart_6405200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405217 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 6]
def baseStart_6405217 : Nat := 118140960795 + 6405217 * 2 ^ 59
def prefixEnd_6405217 : Nat := 4983230072969 + 3 ^ 40 * 6405217 * 2
def baseEnd_6405217 : Nat := 365439446372174588081161

theorem tailTrace_6405217 : CollatzResearch.WordTrace tailWord_6405217 prefixEnd_6405217 365439446372174588081161 := by
  unfold tailWord_6405217
  simp only [CollatzResearch.WordTrace]
  refine ⟨233617456436000207816973905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155744970957333471877982603 233617456436000207816973905)
  ·
    refine ⟨175213092327000155862730429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233617456436000207816973905 175213092327000155862730429)
    ·
      refine ⟨65704909622625058448523911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175213092327000155862730429 65704909622625058448523911)
      ·
        refine ⟨98557364433937587672785867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65704909622625058448523911 98557364433937587672785867)
        ·
          refine ⟨147836046650906381509178801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98557364433937587672785867 147836046650906381509178801)
          ·
            refine ⟨110877034988179786131884101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147836046650906381509178801 110877034988179786131884101)
            ·
              refine ⟨20789444060283709899728269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110877034988179786131884101 20789444060283709899728269)
              ·
                refine ⟨7796041522606391212398101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20789444060283709899728269 7796041522606391212398101)
                ·
                  refine ⟨365439446372174588081161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7796041522606391212398101 365439446372174588081161)
                  ·
                    rfl

theorem cell23_6405217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 6].length) (baseStart_6405217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405217 prefixEnd_6405217 := by exact prefixLift 6405217
  have htrace : WordTrace (prefixWord ++ tailWord_6405217) baseStart_6405217 baseEnd_6405217 := by
    simpa [prefixWord, tailWord_6405217, baseEnd_6405217] using wordTrace_append hprefix tailTrace_6405217
  have hstable : (prefixWord ++ tailWord_6405217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405217).length < 2 ^ (prefixWord ++ tailWord_6405217).sum := by decide
  have hdescent : baseEnd_6405217 < baseStart_6405217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405238 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_6405238 : Nat := 118140960795 + 6405238 * 2 ^ 59
def prefixEnd_6405238 : Nat := 4983230072969 + 3 ^ 40 * 6405238 * 2
def baseEnd_6405238 : Nat := 1096321933481105236855951

theorem tailTrace_6405238 : CollatzResearch.WordTrace tailWord_6405238 prefixEnd_6405238 1096321933481105236855951 := by
  unfold tailWord_6405238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601138898057758025218023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155745481579282752268992245 14601138898057758025218023)
  ·
    refine ⟨21901708347086637037827035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14601138898057758025218023 21901708347086637037827035)
    ·
      refine ⟨32852562520629955556740553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21901708347086637037827035 32852562520629955556740553)
      ·
        refine ⟨24639421890472466667555415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32852562520629955556740553 24639421890472466667555415)
        ·
          refine ⟨36959132835708700001333123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24639421890472466667555415 36959132835708700001333123)
          ·
            refine ⟨55438699253563050001999685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36959132835708700001333123 55438699253563050001999685)
            ·
              refine ⟨10394756110043071875374941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55438699253563050001999685 10394756110043071875374941)
              ·
                refine ⟨3898033541266151953265603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10394756110043071875374941 3898033541266151953265603)
                ·
                  refine ⟨5847050311899227929898405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898033541266151953265603 5847050311899227929898405)
                  ·
                    refine ⟨1096321933481105236855951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5847050311899227929898405 1096321933481105236855951)
                    ·
                      rfl

theorem cell23_6405238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_6405238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405238 prefixEnd_6405238 := by exact prefixLift 6405238
  have htrace : WordTrace (prefixWord ++ tailWord_6405238) baseStart_6405238 baseEnd_6405238 := by
    simpa [prefixWord, tailWord_6405238, baseEnd_6405238] using wordTrace_append hprefix tailTrace_6405238
  have hstable : (prefixWord ++ tailWord_6405238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405238).length < 2 ^ (prefixWord ++ tailWord_6405238).sum := by decide
  have hdescent : baseEnd_6405238 < baseStart_6405238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405244 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_6405244 : Nat := 118140960795 + 6405244 * 2 ^ 59
def prefixEnd_6405244 : Nat := 4983230072969 + 3 ^ 40 * 6405244 * 2
def baseEnd_6405244 : Nat := 3288968881327242687092825

theorem tailTrace_6405244 : CollatzResearch.WordTrace tailWord_6405244 prefixEnd_6405244 3288968881327242687092825 := by
  unfold tailWord_6405244
  simp only [CollatzResearch.WordTrace]
  refine ⟨116809220603451195714103393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155745627471268260952137857 116809220603451195714103393)
  ·
    refine ⟨87606915452588396785577545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116809220603451195714103393 87606915452588396785577545)
    ·
      refine ⟨65705186589441297589183159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87606915452588396785577545 65705186589441297589183159)
      ·
        refine ⟨98557779884161946383774739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65705186589441297589183159 98557779884161946383774739)
        ·
          refine ⟨147836669826242919575662109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98557779884161946383774739 147836669826242919575662109)
          ·
            refine ⟨55438751184841094840873291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147836669826242919575662109 55438751184841094840873291)
            ·
              refine ⟨83158126777261642261309937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55438751184841094840873291 83158126777261642261309937)
              ·
                refine ⟨62368595082946231695982453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83158126777261642261309937 62368595082946231695982453)
                ·
                  refine ⟨5847055789026209221498355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62368595082946231695982453 5847055789026209221498355)
                  ·
                    refine ⟨8770583683539313832247533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5847055789026209221498355 8770583683539313832247533)
                    ·
                      refine ⟨3288968881327242687092825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8770583683539313832247533 3288968881327242687092825)
                      ·
                        rfl

theorem cell23_6405244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_6405244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405244 prefixEnd_6405244 := by exact prefixLift 6405244
  have htrace : WordTrace (prefixWord ++ tailWord_6405244) baseStart_6405244 baseEnd_6405244 := by
    simpa [prefixWord, tailWord_6405244, baseEnd_6405244] using wordTrace_append hprefix tailTrace_6405244
  have hstable : (prefixWord ++ tailWord_6405244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405244).length < 2 ^ (prefixWord ++ tailWord_6405244).sum := by decide
  have hdescent : baseEnd_6405244 < baseStart_6405244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405267 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 4]
def baseStart_6405267 : Nat := 118140960795 + 6405267 * 2 ^ 59
def prefixEnd_6405267 : Nat := 4983230072969 + 3 ^ 40 * 6405267 * 2
def baseEnd_6405267 : Nat := 3288980691382296097105219

theorem tailTrace_6405267 : CollatzResearch.WordTrace tailWord_6405267 prefixEnd_6405267 3288980691382296097105219 := by
  unfold tailWord_6405267
  simp only [CollatzResearch.WordTrace]
  refine ⟨233619280085819066356294055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155746186723879377570862703 233619280085819066356294055)
  ·
    refine ⟨350428920128728599534441083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233619280085819066356294055 350428920128728599534441083)
    ·
      refine ⟨525643380193092899301661625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350428920128728599534441083 525643380193092899301661625)
      ·
        refine ⟨394232535144819674476246219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525643380193092899301661625 394232535144819674476246219)
        ·
          refine ⟨591348802717229511714369329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394232535144819674476246219 591348802717229511714369329)
          ·
            refine ⟨443511602037922133785776997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591348802717229511714369329 443511602037922133785776997)
            ·
              refine ⟨83158425382110400084833187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443511602037922133785776997 83158425382110400084833187)
              ·
                refine ⟨124737638073165600127249781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83158425382110400084833187 124737638073165600127249781)
                ·
                  refine ⟨11694153569359275011929667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124737638073165600127249781 11694153569359275011929667)
                  ·
                    refine ⟨17541230354038912517894501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11694153569359275011929667 17541230354038912517894501)
                    ·
                      refine ⟨3288980691382296097105219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17541230354038912517894501 3288980691382296097105219)
                      ·
                        rfl

theorem cell23_6405267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_6405267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405267 prefixEnd_6405267 := by exact prefixLift 6405267
  have htrace : WordTrace (prefixWord ++ tailWord_6405267) baseStart_6405267 baseEnd_6405267 := by
    simpa [prefixWord, tailWord_6405267, baseEnd_6405267] using wordTrace_append hprefix tailTrace_6405267
  have hstable : (prefixWord ++ tailWord_6405267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405267).length < 2 ^ (prefixWord ++ tailWord_6405267).sum := by decide
  have hdescent : baseEnd_6405267 < baseStart_6405267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405278 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_6405278 : Nat := 118140960795 + 6405278 * 2 ^ 59
def prefixEnd_6405278 : Nat := 4983230072969 + 3 ^ 40 * 6405278 * 2
def baseEnd_6405278 : Nat := 3288986339669495554067669

theorem tailTrace_6405278 : CollatzResearch.WordTrace tailWord_6405278 prefixEnd_6405278 3288986339669495554067669 := by
  unfold tailWord_6405278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29202460161097401904368061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155746454192519476823296325 29202460161097401904368061)
  ·
    refine ⟨10950922560411525714138023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29202460161097401904368061 10950922560411525714138023)
    ·
      refine ⟨16426383840617288571207035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10950922560411525714138023 16426383840617288571207035)
      ·
        refine ⟨24639575760925932856810553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16426383840617288571207035 24639575760925932856810553)
        ·
          refine ⟨18479681820694449642607915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24639575760925932856810553 18479681820694449642607915)
          ·
            refine ⟨27719522731041674463911873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18479681820694449642607915 27719522731041674463911873)
            ·
              refine ⟨20789642048281255847933905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27719522731041674463911873 20789642048281255847933905)
              ·
                refine ⟨15592231536210941885950429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20789642048281255847933905 15592231536210941885950429)
                ·
                  refine ⟨5847086826079103207231411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15592231536210941885950429 5847086826079103207231411)
                  ·
                    refine ⟨8770630239118654810847117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5847086826079103207231411 8770630239118654810847117)
                    ·
                      refine ⟨3288986339669495554067669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8770630239118654810847117 3288986339669495554067669)
                      ·
                        rfl

theorem cell23_6405278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_6405278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405278 prefixEnd_6405278 := by exact prefixLift 6405278
  have htrace : WordTrace (prefixWord ++ tailWord_6405278) baseStart_6405278 baseEnd_6405278 := by
    simpa [prefixWord, tailWord_6405278, baseEnd_6405278] using wordTrace_append hprefix tailTrace_6405278
  have hstable : (prefixWord ++ tailWord_6405278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405278).length < 2 ^ (prefixWord ++ tailWord_6405278).sum := by decide
  have hdescent : baseEnd_6405278 < baseStart_6405278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405367 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 4, 6]
def baseStart_6405367 : Nat := 118140960795 + 6405367 * 2 ^ 59
def prefixEnd_6405367 : Nat := 4983230072969 + 3 ^ 40 * 6405367 * 2
def baseEnd_6405367 : Nat := 1096344013149248568618253

theorem tailTrace_6405367 : CollatzResearch.WordTrace tailWord_6405367 prefixEnd_6405367 1096344013149248568618253 := by
  unfold tailWord_6405367
  simp only [CollatzResearch.WordTrace]
  refine ⟨233622927385456783434934355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155748618256971188956622903 233622927385456783434934355)
  ·
    refine ⟨350434391078185175152401533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233622927385456783434934355 350434391078185175152401533)
    ·
      refine ⟨131412896654319440682150575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350434391078185175152401533 131412896654319440682150575)
      ·
        refine ⟨197119344981479161023225863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131412896654319440682150575 197119344981479161023225863)
        ·
          refine ⟨295679017472218741534838795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197119344981479161023225863 295679017472218741534838795)
          ·
            refine ⟨443518526208328112302258193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295679017472218741534838795 443518526208328112302258193)
            ·
              refine ⟨332638894656246084226693645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443518526208328112302258193 332638894656246084226693645)
              ·
                refine ⟨124739585496092281585010117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332638894656246084226693645 124739585496092281585010117)
                ·
                  refine ⟨23388672280517302797189397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124739585496092281585010117 23388672280517302797189397)
                  ·
                    refine ⟨1096344013149248568618253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23388672280517302797189397 1096344013149248568618253)
                    ·
                      rfl

theorem cell23_6405367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_6405367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405367 prefixEnd_6405367 := by exact prefixLift 6405367
  have htrace : WordTrace (prefixWord ++ tailWord_6405367) baseStart_6405367 baseEnd_6405367 := by
    simpa [prefixWord, tailWord_6405367, baseEnd_6405367] using wordTrace_append hprefix tailTrace_6405367
  have hstable : (prefixWord ++ tailWord_6405367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405367).length < 2 ^ (prefixWord ++ tailWord_6405367).sum := by decide
  have hdescent : baseEnd_6405367 < baseStart_6405367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405391 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 8, 2, 2]
def baseStart_6405391 : Nat := 118140960795 + 6405391 * 2 ^ 59
def prefixEnd_6405391 : Nat := 4983230072969 + 3 ^ 40 * 6405391 * 2
def baseEnd_6405391 : Nat := 3289044362983453611954649

theorem tailTrace_6405391 : CollatzResearch.WordTrace tailWord_6405391 prefixEnd_6405391 3289044362983453611954649 := by
  unfold tailWord_6405391
  simp only [CollatzResearch.WordTrace]
  refine ⟨233623802737369835533808027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155749201824913223689205351 233623802737369835533808027)
  ·
    refine ⟨350435704106054753300712041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233623802737369835533808027 350435704106054753300712041)
    ·
      refine ⟨262826778079541064975534031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350435704106054753300712041 262826778079541064975534031)
      ·
        refine ⟨394240167119311597463301047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262826778079541064975534031 394240167119311597463301047)
        ·
          refine ⟨591360250678967396194951571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394240167119311597463301047 591360250678967396194951571)
          ·
            refine ⟨887040376018451094292427357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591360250678967396194951571 887040376018451094292427357)
            ·
              refine ⟨332640141006919160359660259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887040376018451094292427357 332640141006919160359660259)
              ·
                refine ⟨498960211510378740539490389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332640141006919160359660259 498960211510378740539490389)
                ·
                  refine ⟨5847189978637250865697153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 498960211510378740539490389 5847189978637250865697153)
                  ·
                    refine ⟨4385392483977938149272865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847189978637250865697153 4385392483977938149272865)
                    ·
                      refine ⟨3289044362983453611954649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385392483977938149272865 3289044362983453611954649)
                      ·
                        rfl

theorem cell23_6405391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 2, 2].length) (baseStart_6405391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405391 prefixEnd_6405391 := by exact prefixLift 6405391
  have htrace : WordTrace (prefixWord ++ tailWord_6405391) baseStart_6405391 baseEnd_6405391 := by
    simpa [prefixWord, tailWord_6405391, baseEnd_6405391] using wordTrace_append hprefix tailTrace_6405391
  have hstable : (prefixWord ++ tailWord_6405391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405391).length < 2 ^ (prefixWord ++ tailWord_6405391).sum := by decide
  have hdescent : baseEnd_6405391 < baseStart_6405391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405417 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_6405417 : Nat := 118140960795 + 6405417 * 2 ^ 59
def prefixEnd_6405417 : Nat := 4983230072969 + 3 ^ 40 * 6405417 * 2
def baseEnd_6405417 : Nat := 3289057713480470510229529

theorem tailTrace_6405417 : CollatzResearch.WordTrace tailWord_6405417 prefixEnd_6405417 3289057713480470510229529 := by
  unfold tailWord_6405417
  simp only [CollatzResearch.WordTrace]
  refine ⟨233624751035275641974254505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155749834023517094649503003 233624751035275641974254505)
  ·
    refine ⟨175218563276456731480690879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233624751035275641974254505 175218563276456731480690879)
    ·
      refine ⟨262827844914685097221036319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175218563276456731480690879 262827844914685097221036319)
      ·
        refine ⟨394241767372027645831554479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262827844914685097221036319 394241767372027645831554479)
        ·
          refine ⟨591362651058041468747331719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394241767372027645831554479 591362651058041468747331719)
          ·
            refine ⟨887043976587062203120997579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591362651058041468747331719 887043976587062203120997579)
            ·
              refine ⟨1330565964880593304681496369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887043976587062203120997579 1330565964880593304681496369)
              ·
                refine ⟨997924473660444978511122277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330565964880593304681496369 997924473660444978511122277)
                ·
                  refine ⟨187110838811333433470835427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997924473660444978511122277 187110838811333433470835427)
                  ·
                    refine ⟨280666258217000150206253141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187110838811333433470835427 280666258217000150206253141)
                    ·
                      refine ⟨3289057713480470510229529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 280666258217000150206253141 3289057713480470510229529)
                      ·
                        rfl

theorem cell23_6405417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_6405417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405417 prefixEnd_6405417 := by exact prefixLift 6405417
  have htrace : WordTrace (prefixWord ++ tailWord_6405417) baseStart_6405417 baseEnd_6405417 := by
    simpa [prefixWord, tailWord_6405417, baseEnd_6405417] using wordTrace_append hprefix tailTrace_6405417
  have hstable : (prefixWord ++ tailWord_6405417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405417).length < 2 ^ (prefixWord ++ tailWord_6405417).sum := by decide
  have hdescent : baseEnd_6405417 < baseStart_6405417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405424 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_6405424 : Nat := 118140960795 + 6405424 * 2 ^ 59
def prefixEnd_6405424 : Nat := 4983230072969 + 3 ^ 40 * 6405424 * 2
def baseEnd_6405424 : Nat := 3289061307845051982841997

theorem tailTrace_6405424 : CollatzResearch.WordTrace tailWord_6405424 prefixEnd_6405424 3289061307845051982841997 := by
  unfold tailWord_6405424
  simp only [CollatzResearch.WordTrace]
  refine ⟨116812503173125141084879663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155750004230833521446506217 116812503173125141084879663)
  ·
    refine ⟨175218754759687711627319495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116812503173125141084879663 175218754759687711627319495)
    ·
      refine ⟨262828132139531567440979243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175218754759687711627319495 262828132139531567440979243)
      ·
        refine ⟨394242198209297351161468865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262828132139531567440979243 394242198209297351161468865)
        ·
          refine ⟨295681648656973013371101649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394242198209297351161468865 295681648656973013371101649)
          ·
            refine ⟨221761236492729760028326237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295681648656973013371101649 221761236492729760028326237)
            ·
              refine ⟨83160463684773660010622339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221761236492729760028326237 83160463684773660010622339)
              ·
                refine ⟨124740695527160490015933509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83160463684773660010622339 124740695527160490015933509)
                ·
                  refine ⟨23388880411342591877987533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124740695527160490015933509 23388880411342591877987533)
                  ·
                    refine ⟨8770830154253471954245325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23388880411342591877987533 8770830154253471954245325)
                    ·
                      refine ⟨3289061307845051982841997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8770830154253471954245325 3289061307845051982841997)
                      ·
                        rfl

theorem cell23_6405424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_6405424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405424 prefixEnd_6405424 := by exact prefixLift 6405424
  have htrace : WordTrace (prefixWord ++ tailWord_6405424) baseStart_6405424 baseEnd_6405424 := by
    simpa [prefixWord, tailWord_6405424, baseEnd_6405424] using wordTrace_append hprefix tailTrace_6405424
  have hstable : (prefixWord ++ tailWord_6405424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405424).length < 2 ^ (prefixWord ++ tailWord_6405424).sum := by decide
  have hdescent : baseEnd_6405424 < baseStart_6405424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405425 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 2, 2, 2]
def baseStart_6405425 : Nat := 118140960795 + 6405425 * 2 ^ 59
def prefixEnd_6405425 : Nat := 4983230072969 + 3 ^ 40 * 6405425 * 2
def baseEnd_6405425 : Nat := 3289061821325706478929493

theorem tailTrace_6405425 : CollatzResearch.WordTrace tailWord_6405425 prefixEnd_6405425 3289061821325706478929493 := by
  unfold tailWord_6405425
  simp only [CollatzResearch.WordTrace]
  refine ⟨233625042819246659340545729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155750028546164439560363819 233625042819246659340545729)
  ·
    refine ⟨175218782114434994505409297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233625042819246659340545729 175218782114434994505409297)
    ·
      refine ⟨131414086585826245879056973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175218782114434994505409297 131414086585826245879056973)
      ·
        refine ⟨49280282469684842204646365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131414086585826245879056973 49280282469684842204646365)
        ·
          refine ⟨18480105926131815826742387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49280282469684842204646365 18480105926131815826742387)
          ·
            refine ⟨27720158889197723740113581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18480105926131815826742387 27720158889197723740113581)
            ·
              refine ⟨10395059583449146402542593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27720158889197723740113581 10395059583449146402542593)
              ·
                refine ⟨7796294687586859801906945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10395059583449146402542593 7796294687586859801906945)
                ·
                  refine ⟨5847221015690144851430209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7796294687586859801906945 5847221015690144851430209)
                  ·
                    refine ⟨4385415761767608638572657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847221015690144851430209 4385415761767608638572657)
                    ·
                      refine ⟨3289061821325706478929493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385415761767608638572657 3289061821325706478929493)
                      ·
                        rfl

theorem cell23_6405425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_6405425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405425 prefixEnd_6405425 := by exact prefixLift 6405425
  have htrace : WordTrace (prefixWord ++ tailWord_6405425) baseStart_6405425 baseEnd_6405425 := by
    simpa [prefixWord, tailWord_6405425, baseEnd_6405425] using wordTrace_append hprefix tailTrace_6405425
  have hstable : (prefixWord ++ tailWord_6405425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405425).length < 2 ^ (prefixWord ++ tailWord_6405425).sum := by decide
  have hdescent : baseEnd_6405425 < baseStart_6405425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405462 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6405462 : Nat := 118140960795 + 6405462 * 2 ^ 59
def prefixEnd_6405462 : Nat := 4983230072969 + 3 ^ 40 * 6405462 * 2
def baseEnd_6405462 : Nat := 3289080820109922834166823

theorem tailTrace_6405462 : CollatzResearch.WordTrace tailWord_6405462 prefixEnd_6405462 3289080820109922834166823 := by
  unfold tailWord_6405462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601649520007038416227665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155750928213408409773095093 14601649520007038416227665)
  ·
    refine ⟨10951237140005278812170749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14601649520007038416227665 10951237140005278812170749)
    ·
      refine ⟨4106713927501979554564031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10951237140005278812170749 4106713927501979554564031)
      ·
        refine ⟨6160070891252969331846047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106713927501979554564031 6160070891252969331846047)
        ·
          refine ⟨9240106336879453997769071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160070891252969331846047 9240106336879453997769071)
          ·
            refine ⟨13860159505319180996653607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9240106336879453997769071 13860159505319180996653607)
            ·
              refine ⟨20790239257978771494980411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13860159505319180996653607 20790239257978771494980411)
              ·
                refine ⟨31185358886968157242470617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20790239257978771494980411 31185358886968157242470617)
                ·
                  refine ⟨23389019165226117931852963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31185358886968157242470617 23389019165226117931852963)
                  ·
                    refine ⟨35083528747839176897779445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23389019165226117931852963 35083528747839176897779445)
                    ·
                      refine ⟨3289080820109922834166823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35083528747839176897779445 3289080820109922834166823)
                      ·
                        rfl

theorem cell23_6405462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6405462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405462 prefixEnd_6405462 := by exact prefixLift 6405462
  have htrace : WordTrace (prefixWord ++ tailWord_6405462) baseStart_6405462 baseEnd_6405462 := by
    simpa [prefixWord, tailWord_6405462, baseEnd_6405462] using wordTrace_append hprefix tailTrace_6405462
  have hstable : (prefixWord ++ tailWord_6405462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405462).length < 2 ^ (prefixWord ++ tailWord_6405462).sum := by decide
  have hdescent : baseEnd_6405462 < baseStart_6405462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405464 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6405464 : Nat := 118140960795 + 6405464 * 2 ^ 59
def prefixEnd_6405464 : Nat := 4983230072969 + 3 ^ 40 * 6405464 * 2
def baseEnd_6405464 : Nat := 3289081847071231826341813

theorem tailTrace_6405464 : CollatzResearch.WordTrace tailWord_6405464 prefixEnd_6405464 3289081847071231826341813 := by
  unfold tailWord_6405464
  simp only [CollatzResearch.WordTrace]
  refine ⟨116813232633052684500607723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155750976844070246000810297 116813232633052684500607723)
  ·
    refine ⟨175219848949579026750911585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116813232633052684500607723 175219848949579026750911585)
    ·
      refine ⟨131414886712184270063183689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175219848949579026750911585 131414886712184270063183689)
      ·
        refine ⟨98561165034138202547387767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131414886712184270063183689 98561165034138202547387767)
        ·
          refine ⟨147841747551207303821081651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98561165034138202547387767 147841747551207303821081651)
          ·
            refine ⟨221762621326810955731622477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147841747551207303821081651 221762621326810955731622477)
            ·
              refine ⟨83160982997554108399358429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221762621326810955731622477 83160982997554108399358429)
              ·
                refine ⟨31185368624082790649759411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83160982997554108399358429 31185368624082790649759411)
                ·
                  refine ⟨46778052936124185974639117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31185368624082790649759411 46778052936124185974639117)
                  ·
                    refine ⟨17541769851046569740489669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46778052936124185974639117 17541769851046569740489669)
                    ·
                      refine ⟨3289081847071231826341813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17541769851046569740489669 3289081847071231826341813)
                      ·
                        rfl

theorem cell23_6405464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6405464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405464 prefixEnd_6405464 := by exact prefixLift 6405464
  have htrace : WordTrace (prefixWord ++ tailWord_6405464) baseStart_6405464 baseEnd_6405464 := by
    simpa [prefixWord, tailWord_6405464, baseEnd_6405464] using wordTrace_append hprefix tailTrace_6405464
  have hstable : (prefixWord ++ tailWord_6405464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405464).length < 2 ^ (prefixWord ++ tailWord_6405464).sum := by decide
  have hdescent : baseEnd_6405464 < baseStart_6405464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405481 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 2, 4, 2]
def baseStart_6405481 : Nat := 118140960795 + 6405481 * 2 ^ 59
def prefixEnd_6405481 : Nat := 4983230072969 + 3 ^ 40 * 6405481 * 2
def baseEnd_6405481 : Nat := 3289090576242358259829235

theorem tailTrace_6405481 : CollatzResearch.WordTrace tailWord_6405481 prefixEnd_6405481 3289090576242358259829235 := by
  unfold tailWord_6405481
  simp only [CollatzResearch.WordTrace]
  refine ⟨233627085307043780904584297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155751390204695853936389531 233627085307043780904584297)
  ·
    refine ⟨175220313980282835678438223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233627085307043780904584297 175220313980282835678438223)
    ·
      refine ⟨262830470970424253517657335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175220313980282835678438223 262830470970424253517657335)
      ·
        refine ⟨394245706455636380276486003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262830470970424253517657335 394245706455636380276486003)
        ·
          refine ⟨591368559683454570414729005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394245706455636380276486003 591368559683454570414729005)
          ·
            refine ⟨221763209881295463905523377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591368559683454570414729005 221763209881295463905523377)
            ·
              refine ⟨166322407410971597929142533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221763209881295463905523377 166322407410971597929142533)
              ·
                refine ⟨31185451389557174611714225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166322407410971597929142533 31185451389557174611714225)
                ·
                  refine ⟨23389088542167880958785669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31185451389557174611714225 23389088542167880958785669)
                  ·
                    refine ⟨4385454101656477679772313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23389088542167880958785669 4385454101656477679772313)
                    ·
                      refine ⟨3289090576242358259829235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385454101656477679772313 3289090576242358259829235)
                      ·
                        rfl

theorem cell23_6405481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 4, 2].length) (baseStart_6405481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405481 prefixEnd_6405481 := by exact prefixLift 6405481
  have htrace : WordTrace (prefixWord ++ tailWord_6405481) baseStart_6405481 baseEnd_6405481 := by
    simpa [prefixWord, tailWord_6405481, baseEnd_6405481] using wordTrace_append hprefix tailTrace_6405481
  have hstable : (prefixWord ++ tailWord_6405481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405481).length < 2 ^ (prefixWord ++ tailWord_6405481).sum := by decide
  have hdescent : baseEnd_6405481 < baseStart_6405481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405501 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_6405501 : Nat := 118140960795 + 6405501 * 2 ^ 59
def prefixEnd_6405501 : Nat := 4983230072969 + 3 ^ 40 * 6405501 * 2
def baseEnd_6405501 : Nat := 3289100845855448181579143

theorem tailTrace_6405501 : CollatzResearch.WordTrace tailWord_6405501 prefixEnd_6405501 3289100845855448181579143 := by
  unfold tailWord_6405501
  simp only [CollatzResearch.WordTrace]
  refine ⟨233627814766971324320312357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155751876511314216213541571 233627814766971324320312357)
  ·
    refine ⟨43805215268807123310058567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233627814766971324320312357 43805215268807123310058567)
    ·
      refine ⟨65707822903210684965087851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43805215268807123310058567 65707822903210684965087851)
      ·
        refine ⟨98561734354816027447631777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65707822903210684965087851 98561734354816027447631777)
        ·
          refine ⟨73921300766112020585723833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98561734354816027447631777 73921300766112020585723833)
          ·
            refine ⟨55440975574584015439292875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73921300766112020585723833 55440975574584015439292875)
            ·
              refine ⟨83161463361876023158939313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55440975574584015439292875 83161463361876023158939313)
              ·
                refine ⟨62371097521407017369204485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83161463361876023158939313 62371097521407017369204485)
                ·
                  refine ⟨11694580785263815756725841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62371097521407017369204485 11694580785263815756725841)
                  ·
                    refine ⟨8770935588947861817544381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11694580785263815756725841 8770935588947861817544381)
                    ·
                      refine ⟨3289100845855448181579143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8770935588947861817544381 3289100845855448181579143)
                      ·
                        rfl

theorem cell23_6405501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_6405501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405501 prefixEnd_6405501 := by exact prefixLift 6405501
  have htrace : WordTrace (prefixWord ++ tailWord_6405501) baseStart_6405501 baseEnd_6405501 := by
    simpa [prefixWord, tailWord_6405501, baseEnd_6405501] using wordTrace_append hprefix tailTrace_6405501
  have hstable : (prefixWord ++ tailWord_6405501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405501).length < 2 ^ (prefixWord ++ tailWord_6405501).sum := by decide
  have hdescent : baseEnd_6405501 < baseStart_6405501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405538 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_6405538 : Nat := 118140960795 + 6405538 * 2 ^ 59
def prefixEnd_6405538 : Nat := 4983230072969 + 3 ^ 40 * 6405538 * 2
def baseEnd_6405538 : Nat := 365457760515518281868497

theorem tailTrace_6405538 : CollatzResearch.WordTrace tailWord_6405538 prefixEnd_6405538 365457760515518281868497 := by
  unfold tailWord_6405538
  simp only [CollatzResearch.WordTrace]
  refine ⟨58407291066959319909852317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155752776178558186426272845 58407291066959319909852317)
  ·
    refine ⟨21902734150109744966194619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58407291066959319909852317 21902734150109744966194619)
    ·
      refine ⟨32854101225164617449291929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21902734150109744966194619 32854101225164617449291929)
      ·
        refine ⟨24640575918873463086968947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32854101225164617449291929 24640575918873463086968947)
        ·
          refine ⟨36960863878310194630453421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24640575918873463086968947 36960863878310194630453421)
          ·
            refine ⟨13860323954366322986420033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36960863878310194630453421 13860323954366322986420033)
            ·
              refine ⟨10395242965774742239815025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13860323954366322986420033 10395242965774742239815025)
              ·
                refine ⟨7796432224331056679861269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10395242965774742239815025 7796432224331056679861269)
                ·
                  refine ⟨365457760515518281868497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7796432224331056679861269 365457760515518281868497)
                  ·
                    rfl

theorem cell23_6405538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_6405538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405538 prefixEnd_6405538 := by exact prefixLift 6405538
  have htrace : WordTrace (prefixWord ++ tailWord_6405538) baseStart_6405538 baseEnd_6405538 := by
    simpa [prefixWord, tailWord_6405538, baseEnd_6405538] using wordTrace_append hprefix tailTrace_6405538
  have hstable : (prefixWord ++ tailWord_6405538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405538).length < 2 ^ (prefixWord ++ tailWord_6405538).sum := by decide
  have hdescent : baseEnd_6405538 < baseStart_6405538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405571 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 4]
def baseStart_6405571 : Nat := 118140960795 + 6405571 * 2 ^ 59
def prefixEnd_6405571 : Nat := 4983230072969 + 3 ^ 40 * 6405571 * 2
def baseEnd_6405571 : Nat := 3289136789501262907703821

theorem tailTrace_6405571 : CollatzResearch.WordTrace tailWord_6405571 prefixEnd_6405571 3289136789501262907703821 := by
  unfold tailWord_6405571
  simp only [CollatzResearch.WordTrace]
  refine ⟨233630367876717726275360567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155753578584478484183573711 233630367876717726275360567)
  ·
    refine ⟨350445551815076589413040851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233630367876717726275360567 350445551815076589413040851)
    ·
      refine ⟨525668327722614884119561277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350445551815076589413040851 525668327722614884119561277)
      ·
        refine ⟨197125622895980581544835479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525668327722614884119561277 197125622895980581544835479)
        ·
          refine ⟨295688434343970872317253219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197125622895980581544835479 295688434343970872317253219)
          ·
            refine ⟨443532651515956308475879829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295688434343970872317253219 443532651515956308475879829)
            ·
              refine ⟨20790593039810451959806867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 443532651515956308475879829 20790593039810451959806867)
              ·
                refine ⟨31185889559715677939710301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20790593039810451959806867 31185889559715677939710301)
                ·
                  refine ⟨11694708584893379227391363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31185889559715677939710301 11694708584893379227391363)
                  ·
                    refine ⟨17542062877340068841087045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11694708584893379227391363 17542062877340068841087045)
                    ·
                      refine ⟨3289136789501262907703821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17542062877340068841087045 3289136789501262907703821)
                      ·
                        rfl

theorem cell23_6405571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_6405571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405571 prefixEnd_6405571 := by exact prefixLift 6405571
  have htrace : WordTrace (prefixWord ++ tailWord_6405571) baseStart_6405571 baseEnd_6405571 := by
    simpa [prefixWord, tailWord_6405571, baseEnd_6405571] using wordTrace_append hprefix tailTrace_6405571
  have hstable : (prefixWord ++ tailWord_6405571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405571).length < 2 ^ (prefixWord ++ tailWord_6405571).sum := by decide
  have hdescent : baseEnd_6405571 < baseStart_6405571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405618 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6405618 : Nat := 118140960795 + 6405618 * 2 ^ 59
def prefixEnd_6405618 : Nat := 4983230072969 + 3 ^ 40 * 6405618 * 2
def baseEnd_6405618 : Nat := 3289160923092024223816105

theorem tailTrace_6405618 : CollatzResearch.WordTrace tailWord_6405618 prefixEnd_6405618 3289160923092024223816105 := by
  unfold tailWord_6405618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58408020526886863325580377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155754721405031635534881005 58408020526886863325580377)
  ·
    refine ⟨43806015395165147494185283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58408020526886863325580377 43806015395165147494185283)
    ·
      refine ⟨65709023092747721241277925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43806015395165147494185283 65709023092747721241277925)
      ·
        refine ⟨12320441829890197732739611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65709023092747721241277925 12320441829890197732739611)
        ·
          refine ⟨18480662744835296599109417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12320441829890197732739611 18480662744835296599109417)
          ·
            refine ⟨13860497058626472449332063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18480662744835296599109417 13860497058626472449332063)
            ·
              refine ⟨20790745587939708673998095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13860497058626472449332063 20790745587939708673998095)
              ·
                refine ⟨31186118381909563010997143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20790745587939708673998095 31186118381909563010997143)
                ·
                  refine ⟨46779177572864344516495715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31186118381909563010997143 46779177572864344516495715)
                  ·
                    refine ⟨70168766359296516774743573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46779177572864344516495715 70168766359296516774743573)
                    ·
                      refine ⟨3289160923092024223816105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70168766359296516774743573 3289160923092024223816105)
                      ·
                        rfl

theorem cell23_6405618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6405618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405618 prefixEnd_6405618 := by exact prefixLift 6405618
  have htrace : WordTrace (prefixWord ++ tailWord_6405618) baseStart_6405618 baseEnd_6405618 := by
    simpa [prefixWord, tailWord_6405618, baseEnd_6405618] using wordTrace_append hprefix tailTrace_6405618
  have hstable : (prefixWord ++ tailWord_6405618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405618).length < 2 ^ (prefixWord ++ tailWord_6405618).sum := by decide
  have hdescent : baseEnd_6405618 < baseStart_6405618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405622 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6405622 : Nat := 118140960795 + 6405622 * 2 ^ 59
def prefixEnd_6405622 : Nat := 4983230072969 + 3 ^ 40 * 6405622 * 2
def baseEnd_6405622 : Nat := 3289162977014642208166087

theorem tailTrace_6405622 : CollatzResearch.WordTrace tailWord_6405622 prefixEnd_6405622 3289162977014642208166087 := by
  unfold tailWord_6405622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14602014249970810124091695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155754818666355307990311413 14602014249970810124091695)
  ·
    refine ⟨21903021374956215186137543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14602014249970810124091695 21903021374956215186137543)
    ·
      refine ⟨32854532062434322779206315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21903021374956215186137543 32854532062434322779206315)
      ·
        refine ⟨49281798093651484168809473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32854532062434322779206315 49281798093651484168809473)
        ·
          refine ⟨36961348570238613126607105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49281798093651484168809473 36961348570238613126607105)
          ·
            refine ⟨27721011427678959844955329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36961348570238613126607105 27721011427678959844955329)
            ·
              refine ⟨20790758570759219883716497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27721011427678959844955329 20790758570759219883716497)
              ·
                refine ⟨15593068928069414912787373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20790758570759219883716497 15593068928069414912787373)
                ·
                  refine ⟨5847400848026030592295265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15593068928069414912787373 5847400848026030592295265)
                  ·
                    refine ⟨4385550636019522944221449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847400848026030592295265 4385550636019522944221449)
                    ·
                      refine ⟨3289162977014642208166087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385550636019522944221449 3289162977014642208166087)
                      ·
                        rfl

theorem cell23_6405622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6405622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405622 prefixEnd_6405622 := by exact prefixLift 6405622
  have htrace : WordTrace (prefixWord ++ tailWord_6405622) baseStart_6405622 baseEnd_6405622 := by
    simpa [prefixWord, tailWord_6405622, baseEnd_6405622] using wordTrace_append hprefix tailTrace_6405622
  have hstable : (prefixWord ++ tailWord_6405622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405622).length < 2 ^ (prefixWord ++ tailWord_6405622).sum := by decide
  have hdescent : baseEnd_6405622 < baseStart_6405622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405639 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_6405639 : Nat := 118140960795 + 6405639 * 2 ^ 59
def prefixEnd_6405639 : Nat := 4983230072969 + 3 ^ 40 * 6405639 * 2
def baseEnd_6405639 : Nat := 3289171706185768641653509

theorem tailTrace_6405639 : CollatzResearch.WordTrace tailWord_6405639 prefixEnd_6405639 3289171706185768641653509 := by
  unfold tailWord_6405639
  simp only [CollatzResearch.WordTrace]
  refine ⟨233632848040471373888835971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155755232026980915925890647 233632848040471373888835971)
  ·
    refine ⟨350449272060707060833253957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233632848040471373888835971 350449272060707060833253957)
    ·
      refine ⟨65709238511382573906235117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350449272060707060833253957 65709238511382573906235117)
      ·
        refine ⟨24640964441768465214838169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65709238511382573906235117 24640964441768465214838169)
        ·
          refine ⟨18480723331326348911128627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24640964441768465214838169 18480723331326348911128627)
          ·
            refine ⟨27721084996989523366692941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18480723331326348911128627 27721084996989523366692941)
            ·
              refine ⟨10395406873871071262509853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27721084996989523366692941 10395406873871071262509853)
              ·
                refine ⟨3898277577701651723441195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10395406873871071262509853 3898277577701651723441195)
                ·
                  refine ⟨5847416366552477585161793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898277577701651723441195 5847416366552477585161793)
                  ·
                    refine ⟨4385562274914358188871345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847416366552477585161793 4385562274914358188871345)
                    ·
                      refine ⟨3289171706185768641653509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385562274914358188871345 3289171706185768641653509)
                      ·
                        rfl

theorem cell23_6405639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_6405639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405639 prefixEnd_6405639 := by exact prefixLift 6405639
  have htrace : WordTrace (prefixWord ++ tailWord_6405639) baseStart_6405639 baseEnd_6405639 := by
    simpa [prefixWord, tailWord_6405639, baseEnd_6405639] using wordTrace_append hprefix tailTrace_6405639
  have hstable : (prefixWord ++ tailWord_6405639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405639).length < 2 ^ (prefixWord ++ tailWord_6405639).sum := by decide
  have hdescent : baseEnd_6405639 < baseStart_6405639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405656 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 1, 2, 2]
def baseStart_6405656 : Nat := 118140960795 + 6405656 * 2 ^ 59
def prefixEnd_6405656 : Nat := 4983230072969 + 3 ^ 40 * 6405656 * 2
def baseEnd_6405656 : Nat := 3289180435356895075140931

theorem tailTrace_6405656 : CollatzResearch.WordTrace tailWord_6405656 prefixEnd_6405656 3289180435356895075140931 := by
  unfold tailWord_6405656
  simp only [CollatzResearch.WordTrace]
  refine ⟨116816734040704892896102411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155755645387606523861469881 116816734040704892896102411)
  ·
    refine ⟨175225101061057339344153617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116816734040704892896102411 175225101061057339344153617)
    ·
      refine ⟨131418825795793004508115213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175225101061057339344153617 131418825795793004508115213)
      ·
        refine ⟨49282059673422376690543205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131418825795793004508115213 49282059673422376690543205)
        ·
          refine ⟨9240386188766695629476851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49282059673422376690543205 9240386188766695629476851)
          ·
            refine ⟨13860579283150043444215277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9240386188766695629476851 13860579283150043444215277)
            ·
              refine ⟨5197717231181266291580729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13860579283150043444215277 5197717231181266291580729)
              ·
                refine ⟨3898287923385949718685547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5197717231181266291580729 3898287923385949718685547)
                ·
                  refine ⟨5847431885078924578028321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898287923385949718685547 5847431885078924578028321)
                  ·
                    refine ⟨4385573913809193433521241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847431885078924578028321 4385573913809193433521241)
                    ·
                      refine ⟨3289180435356895075140931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385573913809193433521241 3289180435356895075140931)
                      ·
                        rfl

theorem cell23_6405656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_6405656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405656 prefixEnd_6405656 := by exact prefixLift 6405656
  have htrace : WordTrace (prefixWord ++ tailWord_6405656) baseStart_6405656 baseEnd_6405656 := by
    simpa [prefixWord, tailWord_6405656, baseEnd_6405656] using wordTrace_append hprefix tailTrace_6405656
  have hstable : (prefixWord ++ tailWord_6405656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405656).length < 2 ^ (prefixWord ++ tailWord_6405656).sum := by decide
  have hdescent : baseEnd_6405656 < baseStart_6405656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405695 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 1, 4, 2]
def baseStart_6405695 : Nat := 118140960795 + 6405695 * 2 ^ 59
def prefixEnd_6405695 : Nat := 4983230072969 + 3 ^ 40 * 6405695 * 2
def baseEnd_6405695 : Nat := 3289200461102420422553251

theorem tailTrace_6405695 : CollatzResearch.WordTrace tailWord_6405695 prefixEnd_6405695 3289200461102420422553251 := by
  unfold tailWord_6405695
  simp only [CollatzResearch.WordTrace]
  refine ⟨233634890528268495452874539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155756593685512330301916359 233634890528268495452874539)
  ·
    refine ⟨350452335792402743179311809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233634890528268495452874539 350452335792402743179311809)
    ·
      refine ⟨262839251844302057384483857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350452335792402743179311809 262839251844302057384483857)
      ·
        refine ⟨197129438883226543038362893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262839251844302057384483857 197129438883226543038362893)
        ·
          refine ⟨73923539581209953639386085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197129438883226543038362893 73923539581209953639386085)
          ·
            refine ⟨13860663671476866307384891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73923539581209953639386085 13860663671476866307384891)
            ·
              refine ⟨20790995507215299461077337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13860663671476866307384891 20790995507215299461077337)
              ·
                refine ⟨15593246630411474595808003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20790995507215299461077337 15593246630411474595808003)
                ·
                  refine ⟨23389869945617211893712005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15593246630411474595808003 23389869945617211893712005)
                  ·
                    refine ⟨4385600614803227230071001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23389869945617211893712005 4385600614803227230071001)
                    ·
                      refine ⟨3289200461102420422553251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385600614803227230071001 3289200461102420422553251)
                      ·
                        rfl

theorem cell23_6405695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_6405695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405695 prefixEnd_6405695 := by exact prefixLift 6405695
  have htrace : WordTrace (prefixWord ++ tailWord_6405695) baseStart_6405695 baseEnd_6405695 := by
    simpa [prefixWord, tailWord_6405695, baseEnd_6405695] using wordTrace_append hprefix tailTrace_6405695
  have hstable : (prefixWord ++ tailWord_6405695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405695).length < 2 ^ (prefixWord ++ tailWord_6405695).sum := by decide
  have hdescent : baseEnd_6405695 < baseStart_6405695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405712 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 2, 2, 2]
def baseStart_6405712 : Nat := 118140960795 + 6405712 * 2 ^ 59
def prefixEnd_6405712 : Nat := 4983230072969 + 3 ^ 40 * 6405712 * 2
def baseEnd_6405712 : Nat := 3289209190273546856040673

theorem tailTrace_6405712 : CollatzResearch.WordTrace tailWord_6405712 prefixEnd_6405712 3289209190273546856040673 := by
  unfold tailWord_6405712
  simp only [CollatzResearch.WordTrace]
  refine ⟨116817755284603453678121695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155757007046137938237495593 116817755284603453678121695)
  ·
    refine ⟨175226632926905180517182543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116817755284603453678121695 175226632926905180517182543)
    ·
      refine ⟨262839949390357770775773815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175226632926905180517182543 262839949390357770775773815)
      ·
        refine ⟨394259924085536656163660723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262839949390357770775773815 394259924085536656163660723)
        ·
          refine ⟨591389886128304984245491085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394259924085536656163660723 591389886128304984245491085)
          ·
            refine ⟨221771207298114369092059157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591389886128304984245491085 221771207298114369092059157)
            ·
              refine ⟨10395525342099111051190273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221771207298114369092059157 10395525342099111051190273)
              ·
                refine ⟨7796644006574333288392705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10395525342099111051190273 7796644006574333288392705)
                ·
                  refine ⟨5847483004930749966294529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7796644006574333288392705 5847483004930749966294529)
                  ·
                    refine ⟨4385612253698062474720897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847483004930749966294529 4385612253698062474720897)
                    ·
                      refine ⟨3289209190273546856040673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385612253698062474720897 3289209190273546856040673)
                      ·
                        rfl

theorem cell23_6405712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 2, 2].length) (baseStart_6405712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405712 prefixEnd_6405712 := by exact prefixLift 6405712
  have htrace : WordTrace (prefixWord ++ tailWord_6405712) baseStart_6405712 baseEnd_6405712 := by
    simpa [prefixWord, tailWord_6405712, baseEnd_6405712] using wordTrace_append hprefix tailTrace_6405712
  have hstable : (prefixWord ++ tailWord_6405712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405712).length < 2 ^ (prefixWord ++ tailWord_6405712).sum := by decide
  have hdescent : baseEnd_6405712 < baseStart_6405712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405805 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_6405805 : Nat := 118140960795 + 6405805 * 2 ^ 59
def prefixEnd_6405805 : Nat := 4983230072969 + 3 ^ 40 * 6405805 * 2
def baseEnd_6405805 : Nat := 3289256943974414992177745

theorem tailTrace_6405805 : CollatzResearch.WordTrace tailWord_6405805 prefixEnd_6405805 3289256943974414992177745 := by
  unfold tailWord_6405805
  simp only [CollatzResearch.WordTrace]
  refine ⟨233638902557869984239378869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155759268371913322826252579 233638902557869984239378869)
  ·
    refine ⟨21903647114800311022441769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233638902557869984239378869 21903647114800311022441769)
    ·
      refine ⟨16427735336100233266831327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21903647114800311022441769 16427735336100233266831327)
      ·
        refine ⟨24641603004150349900246991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16427735336100233266831327 24641603004150349900246991)
        ·
          refine ⟨36962404506225524850370487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24641603004150349900246991 36962404506225524850370487)
          ·
            refine ⟨55443606759338287275555731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36962404506225524850370487 55443606759338287275555731)
            ·
              refine ⟨83165410139007430913333597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55443606759338287275555731 83165410139007430913333597)
              ·
                refine ⟨31187028802127786592500099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83165410139007430913333597 31187028802127786592500099)
                ·
                  refine ⟨46780543203191679888750149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31187028802127786592500099 46780543203191679888750149)
                  ·
                    refine ⟨8771351850598439979140653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46780543203191679888750149 8771351850598439979140653)
                    ·
                      refine ⟨3289256943974414992177745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8771351850598439979140653 3289256943974414992177745)
                      ·
                        rfl

theorem cell23_6405805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_6405805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405805 prefixEnd_6405805 := by exact prefixLift 6405805
  have htrace : WordTrace (prefixWord ++ tailWord_6405805) baseStart_6405805 baseEnd_6405805 := by
    simpa [prefixWord, tailWord_6405805, baseEnd_6405805] using wordTrace_append hprefix tailTrace_6405805
  have hstable : (prefixWord ++ tailWord_6405805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405805).length < 2 ^ (prefixWord ++ tailWord_6405805).sum := by decide
  have hdescent : baseEnd_6405805 < baseStart_6405805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405822 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_6405822 : Nat := 118140960795 + 6405822 * 2 ^ 59
def prefixEnd_6405822 : Nat := 4983230072969 + 3 ^ 40 * 6405822 * 2
def baseEnd_6405822 : Nat := 3289265673145541425665167

theorem tailTrace_6405822 : CollatzResearch.WordTrace tailWord_6405822 prefixEnd_6405822 3289265673145541425665167 := by
  unfold tailWord_6405822
  simp only [CollatzResearch.WordTrace]
  refine ⟨29204940324851049517843465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155759681732538930761831813 29204940324851049517843465)
  ·
    refine ⟨21903705243638287138382599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29204940324851049517843465 21903705243638287138382599)
    ·
      refine ⟨32855557865457430707573899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21903705243638287138382599 32855557865457430707573899)
      ·
        refine ⟨49283336798186146061360849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32855557865457430707573899 49283336798186146061360849)
        ·
          refine ⟨36962502598639609546020637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49283336798186146061360849 36962502598639609546020637)
          ·
            refine ⟨13860938474489853579757739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36962502598639609546020637 13860938474489853579757739)
            ·
              refine ⟨20791407711734780369636609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13860938474489853579757739 20791407711734780369636609)
              ·
                refine ⟨15593555783801085277227457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20791407711734780369636609 15593555783801085277227457)
                ·
                  refine ⟨11695166837850813957920593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15593555783801085277227457 11695166837850813957920593)
                  ·
                    refine ⟨8771375128388110468440445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11695166837850813957920593 8771375128388110468440445)
                    ·
                      refine ⟨3289265673145541425665167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8771375128388110468440445 3289265673145541425665167)
                      ·
                        rfl

theorem cell23_6405822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_6405822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405822 prefixEnd_6405822 := by exact prefixLift 6405822
  have htrace : WordTrace (prefixWord ++ tailWord_6405822) baseStart_6405822 baseEnd_6405822 := by
    simpa [prefixWord, tailWord_6405822, baseEnd_6405822] using wordTrace_append hprefix tailTrace_6405822
  have hstable : (prefixWord ++ tailWord_6405822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405822).length < 2 ^ (prefixWord ++ tailWord_6405822).sum := by decide
  have hdescent : baseEnd_6405822 < baseStart_6405822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405842 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_6405842 : Nat := 118140960795 + 6405842 * 2 ^ 59
def prefixEnd_6405842 : Nat := 4983230072969 + 3 ^ 40 * 6405842 * 2
def baseEnd_6405842 : Nat := 365475104750959038601675

theorem tailTrace_6405842 : CollatzResearch.WordTrace tailWord_6405842 prefixEnd_6405842 365475104750959038601675 := by
  unfold tailWord_6405842
  simp only [CollatzResearch.WordTrace]
  refine ⟨58410063014683984889618945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155760168039157293038983853 58410063014683984889618945)
  ·
    refine ⟨43807547261012988667214209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58410063014683984889618945 43807547261012988667214209)
    ·
      refine ⟨32855660445759741500410657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43807547261012988667214209 32855660445759741500410657)
      ·
        refine ⟨24641745334319806125307993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32855660445759741500410657 24641745334319806125307993)
        ·
          refine ⟨18481309000739854593980995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24641745334319806125307993 18481309000739854593980995)
          ·
            refine ⟨27721963501109781890971493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18481309000739854593980995 27721963501109781890971493)
            ·
              refine ⟨5197868156458084104557155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27721963501109781890971493 5197868156458084104557155)
              ·
                refine ⟨7796802234687126156835733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5197868156458084104557155 7796802234687126156835733)
                ·
                  refine ⟨365475104750959038601675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7796802234687126156835733 365475104750959038601675)
                  ·
                    rfl

theorem cell23_6405842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_6405842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405842 prefixEnd_6405842 := by exact prefixLift 6405842
  have htrace : WordTrace (prefixWord ++ tailWord_6405842) baseStart_6405842 baseEnd_6405842 := by
    simpa [prefixWord, tailWord_6405842, baseEnd_6405842] using wordTrace_append hprefix tailTrace_6405842
  have hstable : (prefixWord ++ tailWord_6405842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405842).length < 2 ^ (prefixWord ++ tailWord_6405842).sum := by decide
  have hdescent : baseEnd_6405842 < baseStart_6405842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405868 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_6405868 : Nat := 118140960795 + 6405868 * 2 ^ 59
def prefixEnd_6405868 : Nat := 4983230072969 + 3 ^ 40 * 6405868 * 2
def baseEnd_6405868 : Nat := 1096429764418549415229985

theorem tailTrace_6405868 : CollatzResearch.WordTrace tailWord_6405868 prefixEnd_6405868 1096429764418549415229985 := by
  unfold tailWord_6405868
  simp only [CollatzResearch.WordTrace]
  refine ⟨116820600178320872999461129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155760800237761163999281505 116820600178320872999461129)
  ·
    refine ⟨87615450133740654749595847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116820600178320872999461129 87615450133740654749595847)
    ·
      refine ⟨131423175200610982124393771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87615450133740654749595847 131423175200610982124393771)
      ·
        refine ⟨197134762800916473186590657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131423175200610982124393771 197134762800916473186590657)
        ·
          refine ⟨147851072100687354889942993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197134762800916473186590657 147851072100687354889942993)
          ·
            refine ⟨110888304075515516167457245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147851072100687354889942993 110888304075515516167457245)
            ·
              refine ⟨41583114028318318562796467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110888304075515516167457245 41583114028318318562796467)
              ·
                refine ⟨62374671042477477844194701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41583114028318318562796467 62374671042477477844194701)
                ·
                  refine ⟨23390501640929054191573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62374671042477477844194701 23390501640929054191573013)
                  ·
                    refine ⟨1096429764418549415229985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23390501640929054191573013 1096429764418549415229985)
                    ·
                      rfl

theorem cell23_6405868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_6405868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405868 prefixEnd_6405868 := by exact prefixLift 6405868
  have htrace : WordTrace (prefixWord ++ tailWord_6405868) baseStart_6405868 baseEnd_6405868 := by
    simpa [prefixWord, tailWord_6405868, baseEnd_6405868] using wordTrace_append hprefix tailTrace_6405868
  have hstable : (prefixWord ++ tailWord_6405868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405868).length < 2 ^ (prefixWord ++ tailWord_6405868).sum := by decide
  have hdescent : baseEnd_6405868 < baseStart_6405868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405875 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 4]
def baseStart_6405875 : Nat := 118140960795 + 6405875 * 2 ^ 59
def prefixEnd_6405875 : Nat := 4983230072969 + 3 ^ 40 * 6405875 * 2
def baseEnd_6405875 : Nat := 3289292887620229718302423

theorem tailTrace_6405875 : CollatzResearch.WordTrace tailWord_6405875 prefixEnd_6405875 3289292887620229718302423 := by
  unfold tailWord_6405875
  simp only [CollatzResearch.WordTrace]
  refine ⟨233641455667616386194427079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155760970445077590796284719 233641455667616386194427079)
  ·
    refine ⟨350462183501424579291640619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233641455667616386194427079 350462183501424579291640619)
    ·
      refine ⟨525693275252136868937460929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350462183501424579291640619 525693275252136868937460929)
      ·
        refine ⟨394269956439102651703095697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525693275252136868937460929 394269956439102651703095697)
        ·
          refine ⟨295702467329326988777321773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394269956439102651703095697 295702467329326988777321773)
          ·
            refine ⟨110888425248497620791495665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295702467329326988777321773 110888425248497620791495665)
            ·
              refine ⟨83166318936373215593621749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110888425248497620791495665 83166318936373215593621749)
              ·
                refine ⟨7796842400284988961902039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83166318936373215593621749 7796842400284988961902039)
                ·
                  refine ⟨11695263600427483442853059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7796842400284988961902039 11695263600427483442853059)
                  ·
                    refine ⟨17542895400641225164279589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11695263600427483442853059 17542895400641225164279589)
                    ·
                      refine ⟨3289292887620229718302423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17542895400641225164279589 3289292887620229718302423)
                      ·
                        rfl

theorem cell23_6405875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_6405875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405875 prefixEnd_6405875 := by exact prefixLift 6405875
  have htrace : WordTrace (prefixWord ++ tailWord_6405875) baseStart_6405875 baseEnd_6405875 := by
    simpa [prefixWord, tailWord_6405875, baseEnd_6405875] using wordTrace_append hprefix tailTrace_6405875
  have hstable : (prefixWord ++ tailWord_6405875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405875).length < 2 ^ (prefixWord ++ tailWord_6405875).sum := by decide
  have hdescent : baseEnd_6405875 < baseStart_6405875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405902 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_6405902 : Nat := 118140960795 + 6405902 * 2 ^ 59
def prefixEnd_6405902 : Nat := 4983230072969 + 3 ^ 40 * 6405902 * 2
def baseEnd_6405902 : Nat := 1096435583865967037554933

theorem tailTrace_6405902 : CollatzResearch.WordTrace tailWord_6405902 prefixEnd_6405902 1096435583865967037554933 := by
  unfold tailWord_6405902
  simp only [CollatzResearch.WordTrace]
  refine ⟨29205305054814821225707495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155761626959012379870439973 29205305054814821225707495)
  ·
    refine ⟨43807957582222231838561243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29205305054814821225707495 43807957582222231838561243)
    ·
      refine ⟨65711936373333347757841865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43807957582222231838561243 65711936373333347757841865)
      ·
        refine ⟨49283952280000010818381399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65711936373333347757841865 49283952280000010818381399)
        ·
          refine ⟨73925928420000016227572099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49283952280000010818381399 73925928420000016227572099)
          ·
            refine ⟨110888892630000024341358149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73925928420000016227572099 110888892630000024341358149)
            ·
              refine ⟨20791667368125004564004653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110888892630000024341358149 20791667368125004564004653)
              ·
                refine ⟨7796875263046876711501745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20791667368125004564004653 7796875263046876711501745)
                ·
                  refine ⟨5847656447285157533626309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7796875263046876711501745 5847656447285157533626309)
                  ·
                    refine ⟨1096435583865967037554933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5847656447285157533626309 1096435583865967037554933)
                    ·
                      rfl

theorem cell23_6405902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_6405902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405902 prefixEnd_6405902 := by exact prefixLift 6405902
  have htrace : WordTrace (prefixWord ++ tailWord_6405902) baseStart_6405902 baseEnd_6405902 := by
    simpa [prefixWord, tailWord_6405902, baseEnd_6405902] using wordTrace_append hprefix tailTrace_6405902
  have hstable : (prefixWord ++ tailWord_6405902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405902).length < 2 ^ (prefixWord ++ tailWord_6405902).sum := by decide
  have hdescent : baseEnd_6405902 < baseStart_6405902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405909 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_6405909 : Nat := 118140960795 + 6405909 * 2 ^ 59
def prefixEnd_6405909 : Nat := 4983230072969 + 3 ^ 40 * 6405909 * 2
def baseEnd_6405909 : Nat := 3289310345962482585277267

theorem tailTrace_6405909 : CollatzResearch.WordTrace tailWord_6405909 prefixEnd_6405909 3289310345962482585277267 := by
  unfold tailWord_6405909
  simp only [CollatzResearch.WordTrace]
  refine ⟨233642695749493210001164781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155761797166328806667443187 233642695749493210001164781)
  ·
    refine ⟨87616010906059953750436793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233642695749493210001164781 87616010906059953750436793)
    ·
      refine ⟨65712008179544965312827595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87616010906059953750436793 65712008179544965312827595)
      ·
        refine ⟨98568012269317447969241393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65712008179544965312827595 98568012269317447969241393)
        ·
          refine ⟨73926009201988085976931045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98568012269317447969241393 73926009201988085976931045)
          ·
            refine ⟨13861126725372766120674571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73926009201988085976931045 13861126725372766120674571)
            ·
              refine ⟨20791690088059149181011857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13861126725372766120674571 20791690088059149181011857)
              ·
                refine ⟨15593767566044361885758893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20791690088059149181011857 15593767566044361885758893)
                ·
                  refine ⟨5847662837266635707159585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15593767566044361885758893 5847662837266635707159585)
                  ·
                    refine ⟨4385747127949976780369689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847662837266635707159585 4385747127949976780369689)
                    ·
                      refine ⟨3289310345962482585277267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385747127949976780369689 3289310345962482585277267)
                      ·
                        rfl

theorem cell23_6405909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_6405909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405909 prefixEnd_6405909 := by exact prefixLift 6405909
  have htrace : WordTrace (prefixWord ++ tailWord_6405909) baseStart_6405909 baseEnd_6405909 := by
    simpa [prefixWord, tailWord_6405909, baseEnd_6405909] using wordTrace_append hprefix tailTrace_6405909
  have hstable : (prefixWord ++ tailWord_6405909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405909).length < 2 ^ (prefixWord ++ tailWord_6405909).sum := by decide
  have hdescent : baseEnd_6405909 < baseStart_6405909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405969 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 1, 3, 2]
def baseStart_6405969 : Nat := 118140960795 + 6405969 * 2 ^ 59
def prefixEnd_6405969 : Nat := 4983230072969 + 3 ^ 40 * 6405969 * 2
def baseEnd_6405969 : Nat := 3289341154801752350526991

theorem tailTrace_6405969 : CollatzResearch.WordTrace tailWord_6405969 prefixEnd_6405969 3289341154801752350526991 := by
  unfold tailWord_6405969
  simp only [CollatzResearch.WordTrace]
  refine ⟨233644884129275840248348961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155763256086183893498899307 233644884129275840248348961)
  ·
    refine ⟨175233663096956880186261721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233644884129275840248348961 175233663096956880186261721)
    ·
      refine ⟨131425247322717660139696291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175233663096956880186261721 131425247322717660139696291)
      ·
        refine ⟨197137870984076490209544437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131425247322717660139696291 197137870984076490209544437)
        ·
          refine ⟨18481675404757170957144791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197137870984076490209544437 18481675404757170957144791)
          ·
            refine ⟨27722513107135756435717187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18481675404757170957144791 27722513107135756435717187)
            ·
              refine ⟨41583769660703634653575781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27722513107135756435717187 41583769660703634653575781)
              ·
                refine ⟨7796956811381931497545459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41583769660703634653575781 7796956811381931497545459)
                ·
                  refine ⟨11695435217072897246318189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7796956811381931497545459 11695435217072897246318189)
                  ·
                    refine ⟨4385788206402336467369321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11695435217072897246318189 4385788206402336467369321)
                    ·
                      refine ⟨3289341154801752350526991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385788206402336467369321 3289341154801752350526991)
                      ·
                        rfl

theorem cell23_6405969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_6405969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405969 prefixEnd_6405969 := by exact prefixLift 6405969
  have htrace : WordTrace (prefixWord ++ tailWord_6405969) baseStart_6405969 baseEnd_6405969 := by
    simpa [prefixWord, tailWord_6405969, baseEnd_6405969] using wordTrace_append hprefix tailTrace_6405969
  have hstable : (prefixWord ++ tailWord_6405969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405969).length < 2 ^ (prefixWord ++ tailWord_6405969).sum := by decide
  have hdescent : baseEnd_6405969 < baseStart_6405969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405985 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_6405985 : Nat := 118140960795 + 6405985 * 2 ^ 59
def prefixEnd_6405985 : Nat := 4983230072969 + 3 ^ 40 * 6405985 * 2
def baseEnd_6405985 : Nat := 3289349370492224287926917

theorem tailTrace_6405985 : CollatzResearch.WordTrace tailWord_6405985 prefixEnd_6405985 3289349370492224287926917 := by
  unfold tailWord_6405985
  simp only [CollatzResearch.WordTrace]
  refine ⟨233645467697217874980931409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155763645131478583320620939 233645467697217874980931409)
  ·
    refine ⟨175234100772913406235698557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233645467697217874980931409 175234100772913406235698557)
    ·
      refine ⟨65712787789842527338386959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175234100772913406235698557 65712787789842527338386959)
      ·
        refine ⟨98569181684763791007580439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65712787789842527338386959 98569181684763791007580439)
        ·
          refine ⟨147853772527145686511370659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98569181684763791007580439 147853772527145686511370659)
          ·
            refine ⟨221780658790718529767055989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147853772527145686511370659 221780658790718529767055989)
            ·
              refine ⟨20791936761629862165661499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221780658790718529767055989 20791936761629862165661499)
              ·
                refine ⟨31187905142444793248492249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20791936761629862165661499 31187905142444793248492249)
                ·
                  refine ⟨23390928856833594936369187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31187905142444793248492249 23390928856833594936369187)
                  ·
                    refine ⟨35086393285250392404553781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23390928856833594936369187 35086393285250392404553781)
                    ·
                      refine ⟨3289349370492224287926917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35086393285250392404553781 3289349370492224287926917)
                      ·
                        rfl

theorem cell23_6405985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_6405985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405985 prefixEnd_6405985 := by exact prefixLift 6405985
  have htrace : WordTrace (prefixWord ++ tailWord_6405985) baseStart_6405985 baseEnd_6405985 := by
    simpa [prefixWord, tailWord_6405985, baseEnd_6405985] using wordTrace_append hprefix tailTrace_6405985
  have hstable : (prefixWord ++ tailWord_6405985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405985).length < 2 ^ (prefixWord ++ tailWord_6405985).sum := by decide
  have hdescent : baseEnd_6405985 < baseStart_6405985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6405986 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_6405986 : Nat := 118140960795 + 6405986 * 2 ^ 59
def prefixEnd_6405986 : Nat := 4983230072969 + 3 ^ 40 * 6405986 * 2
def baseEnd_6405986 : Nat := 3289349883972878784014413

theorem tailTrace_6405986 : CollatzResearch.WordTrace tailWord_6405986 prefixEnd_6405986 3289349883972878784014413 := by
  unfold tailWord_6405986
  simp only [CollatzResearch.WordTrace]
  refine ⟨58411376042553563037929453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155763669446809501434478541 58411376042553563037929453)
  ·
    refine ⟨21904266015957586139223545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58411376042553563037929453 21904266015957586139223545)
    ·
      refine ⟨16428199511968189604417659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21904266015957586139223545 16428199511968189604417659)
      ·
        refine ⟨24642299267952284406626489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16428199511968189604417659 24642299267952284406626489)
        ·
          refine ⟨18481724450964213304969867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24642299267952284406626489 18481724450964213304969867)
          ·
            refine ⟨27722586676446319957454801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18481724450964213304969867 27722586676446319957454801)
            ·
              refine ⟨20791940007334739968091101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27722586676446319957454801 20791940007334739968091101)
              ·
                refine ⟨7796977502750527488034163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20791940007334739968091101 7796977502750527488034163)
                ·
                  refine ⟨11695466254125791232051245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7796977502750527488034163 11695466254125791232051245)
                  ·
                    refine ⟨4385799845297171712019217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11695466254125791232051245 4385799845297171712019217)
                    ·
                      refine ⟨3289349883972878784014413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385799845297171712019217 3289349883972878784014413)
                      ·
                        rfl

theorem cell23_6405986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_6405986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6405986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6405986 prefixEnd_6405986 := by exact prefixLift 6405986
  have htrace : WordTrace (prefixWord ++ tailWord_6405986) baseStart_6405986 baseEnd_6405986 := by
    simpa [prefixWord, tailWord_6405986, baseEnd_6405986] using wordTrace_append hprefix tailTrace_6405986
  have hstable : (prefixWord ++ tailWord_6405986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6405986).length < 2 ^ (prefixWord ++ tailWord_6405986).sum := by decide
  have hdescent : baseEnd_6405986 < baseStart_6405986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6405986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406015 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_6406015 : Nat := 118140960795 + 6406015 * 2 ^ 59
def prefixEnd_6406015 : Nat := 4983230072969 + 3 ^ 40 * 6406015 * 2
def baseEnd_6406015 : Nat := 3289364774911859170551779

theorem tailTrace_6406015 : CollatzResearch.WordTrace tailWord_6406015 prefixEnd_6406015 3289364774911859170551779 := by
  unfold tailWord_6406015
  simp only [CollatzResearch.WordTrace]
  refine ⟨233646561887109190104523499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155764374591406126736348999 233646561887109190104523499)
  ·
    refine ⟨350469842830663785156785249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233646561887109190104523499 350469842830663785156785249)
    ·
      refine ⟨262852382122997838867588937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350469842830663785156785249 262852382122997838867588937)
      ·
        refine ⟨197139286592248379150691703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262852382122997838867588937 197139286592248379150691703)
        ·
          refine ⟨295708929888372568726037555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197139286592248379150691703 295708929888372568726037555)
          ·
            refine ⟨443563394832558853089056333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295708929888372568726037555 443563394832558853089056333)
            ·
              refine ⟨166336273062209569908396125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 443563394832558853089056333 166336273062209569908396125)
              ·
                refine ⟨62376102398328588715648547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166336273062209569908396125 62376102398328588715648547)
                ·
                  refine ⟨93564153597492883073472821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62376102398328588715648547 93564153597492883073472821)
                  ·
                    refine ⟨8771639399764957788138077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93564153597492883073472821 8771639399764957788138077)
                    ·
                      refine ⟨3289364774911859170551779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8771639399764957788138077 3289364774911859170551779)
                      ·
                        rfl

theorem cell23_6406015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_6406015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406015 prefixEnd_6406015 := by exact prefixLift 6406015
  have htrace : WordTrace (prefixWord ++ tailWord_6406015) baseStart_6406015 baseEnd_6406015 := by
    simpa [prefixWord, tailWord_6406015, baseEnd_6406015] using wordTrace_append hprefix tailTrace_6406015
  have hstable : (prefixWord ++ tailWord_6406015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406015).length < 2 ^ (prefixWord ++ tailWord_6406015).sum := by decide
  have hdescent : baseEnd_6406015 < baseStart_6406015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406052 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_6406052 : Nat := 118140960795 + 6406052 * 2 ^ 59
def prefixEnd_6406052 : Nat := 4983230072969 + 3 ^ 40 * 6406052 * 2
def baseEnd_6406052 : Nat := 1096461257898691841929703

theorem tailTrace_6406052 : CollatzResearch.WordTrace tailWord_6406052 prefixEnd_6406052 1096461257898691841929703 := by
  unfold tailWord_6406052
  simp only [CollatzResearch.WordTrace]
  refine ⟨116823955693987572711810205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155765274258650096949080273 116823955693987572711810205)
  ·
    refine ⟨43808983385245339766928827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116823955693987572711810205 43808983385245339766928827)
    ·
      refine ⟨65713475077868009650393241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43808983385245339766928827 65713475077868009650393241)
      ·
        refine ⟨49285106308401007237794931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65713475077868009650393241 49285106308401007237794931)
        ·
          refine ⟨73927659462601510856692397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49285106308401007237794931 73927659462601510856692397)
          ·
            refine ⟨27722872298475566571259649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73927659462601510856692397 27722872298475566571259649)
            ·
              refine ⟨20792154223856674928444737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27722872298475566571259649 20792154223856674928444737)
              ·
                refine ⟨15594115667892506196333553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20792154223856674928444737 15594115667892506196333553)
                ·
                  refine ⟨11695586750919379647250165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15594115667892506196333553 11695586750919379647250165)
                  ·
                    refine ⟨1096461257898691841929703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11695586750919379647250165 1096461257898691841929703)
                    ·
                      rfl

theorem cell23_6406052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_6406052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406052 prefixEnd_6406052 := by exact prefixLift 6406052
  have htrace : WordTrace (prefixWord ++ tailWord_6406052) baseStart_6406052 baseEnd_6406052 := by
    simpa [prefixWord, tailWord_6406052, baseEnd_6406052] using wordTrace_append hprefix tailTrace_6406052
  have hstable : (prefixWord ++ tailWord_6406052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406052).length < 2 ^ (prefixWord ++ tailWord_6406052).sum := by decide
  have hdescent : baseEnd_6406052 < baseStart_6406052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406085 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_6406085 : Nat := 118140960795 + 6406085 * 2 ^ 59
def prefixEnd_6406085 : Nat := 4983230072969 + 3 ^ 40 * 6406085 * 2
def baseEnd_6406085 : Nat := 3289400718557673896676457

theorem tailTrace_6406085 : CollatzResearch.WordTrace tailWord_6406085 prefixEnd_6406085 3289400718557673896676457 := by
  unfold tailWord_6406085
  simp only [CollatzResearch.WordTrace]
  refine ⟨233649114996855592059571709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155766076664570394706381139 233649114996855592059571709)
  ·
    refine ⟨87618418123820847022339391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233649114996855592059571709 87618418123820847022339391)
    ·
      refine ⟨131427627185731270533509087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87618418123820847022339391 131427627185731270533509087)
      ·
        refine ⟨197141440778596905800263631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131427627185731270533509087 197141440778596905800263631)
        ·
          refine ⟨295712161167895358700395447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197141440778596905800263631 295712161167895358700395447)
          ·
            refine ⟨443568241751843038050593171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295712161167895358700395447 443568241751843038050593171)
            ·
              refine ⟨665352362627764557075889757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443568241751843038050593171 665352362627764557075889757)
              ·
                refine ⟨249507135985411708903458659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 665352362627764557075889757 249507135985411708903458659)
                ·
                  refine ⟨374260703978117563355187989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249507135985411708903458659 374260703978117563355187989)
                  ·
                    refine ⟨17543470498974260782274437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 374260703978117563355187989 17543470498974260782274437)
                    ·
                      refine ⟨3289400718557673896676457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17543470498974260782274437 3289400718557673896676457)
                      ·
                        rfl

theorem cell23_6406085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_6406085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406085 prefixEnd_6406085 := by exact prefixLift 6406085
  have htrace : WordTrace (prefixWord ++ tailWord_6406085) baseStart_6406085 baseEnd_6406085 := by
    simpa [prefixWord, tailWord_6406085, baseEnd_6406085] using wordTrace_append hprefix tailTrace_6406085
  have hstable : (prefixWord ++ tailWord_6406085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406085).length < 2 ^ (prefixWord ++ tailWord_6406085).sum := by decide
  have hdescent : baseEnd_6406085 < baseStart_6406085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406095 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 8]
def baseStart_6406095 : Nat := 118140960795 + 6406095 * 2 ^ 59
def prefixEnd_6406095 : Nat := 4983230072969 + 3 ^ 40 * 6406095 * 2
def baseEnd_6406095 : Nat := 365489539262690984172379

theorem tailTrace_6406095 : CollatzResearch.WordTrace tailWord_6406095 prefixEnd_6406095 365489539262690984172379 := by
  unfold tailWord_6406095
  simp only [CollatzResearch.WordTrace]
  refine ⟨233649479726819363767435739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155766319817879575844957159 233649479726819363767435739)
  ·
    refine ⟨350474219590229045651153609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233649479726819363767435739 350474219590229045651153609)
    ·
      refine ⟨262855664692671784238365207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350474219590229045651153609 262855664692671784238365207)
      ·
        refine ⟨394283497039007676357547811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262855664692671784238365207 394283497039007676357547811)
        ·
          refine ⟨591425245558511514536321717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394283497039007676357547811 591425245558511514536321717)
          ·
            refine ⟨55446116771110454487780161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 591425245558511514536321717 55446116771110454487780161)
            ·
              refine ⟨41584587578332840865835121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55446116771110454487780161 41584587578332840865835121)
              ·
                refine ⟨31188440683749630649376341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41584587578332840865835121 31188440683749630649376341)
                ·
                  refine ⟨365489539262690984172379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31188440683749630649376341 365489539262690984172379)
                  ·
                    rfl

theorem cell23_6406095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 8].length) (baseStart_6406095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406095 prefixEnd_6406095 := by exact prefixLift 6406095
  have htrace : WordTrace (prefixWord ++ tailWord_6406095) baseStart_6406095 baseEnd_6406095 := by
    simpa [prefixWord, tailWord_6406095, baseEnd_6406095] using wordTrace_append hprefix tailTrace_6406095
  have hstable : (prefixWord ++ tailWord_6406095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406095).length < 2 ^ (prefixWord ++ tailWord_6406095).sum := by decide
  have hdescent : baseEnd_6406095 < baseStart_6406095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406139 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 3]
def baseStart_6406139 : Nat := 118140960795 + 6406139 * 2 ^ 59
def prefixEnd_6406139 : Nat := 4983230072969 + 3 ^ 40 * 6406139 * 2
def baseEnd_6406139 : Nat := 3289428446513016685401209

theorem tailTrace_6406139 : CollatzResearch.WordTrace tailWord_6406139 prefixEnd_6406139 3289428446513016685401209 := by
  unfold tailWord_6406139
  simp only [CollatzResearch.WordTrace]
  refine ⟨233651084538659959282037471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155767389692439972854691647 233651084538659959282037471)
  ·
    refine ⟨350476626807989938923056207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233651084538659959282037471 350476626807989938923056207)
    ·
      refine ⟨525714940211984908384584311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350476626807989938923056207 525714940211984908384584311)
      ·
        refine ⟨788572410317977362576876467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525714940211984908384584311 788572410317977362576876467)
        ·
          refine ⟨1182858615476966043865314701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788572410317977362576876467 1182858615476966043865314701)
          ·
            refine ⟨443571980803862266449493013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1182858615476966043865314701 443571980803862266449493013)
            ·
              refine ⟨20792436600181043739819985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 443571980803862266449493013 20792436600181043739819985)
              ·
                refine ⟨15594327450135782804864989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20792436600181043739819985 15594327450135782804864989)
                ·
                  refine ⟨5847872793800918551824371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15594327450135782804864989 5847872793800918551824371)
                  ·
                    refine ⟨8771809190701377827736557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5847872793800918551824371 8771809190701377827736557)
                    ·
                      refine ⟨3289428446513016685401209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8771809190701377827736557 3289428446513016685401209)
                      ·
                        rfl

theorem cell23_6406139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 3].length) (baseStart_6406139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406139 prefixEnd_6406139 := by exact prefixLift 6406139
  have htrace : WordTrace (prefixWord ++ tailWord_6406139) baseStart_6406139 baseEnd_6406139 := by
    simpa [prefixWord, tailWord_6406139, baseEnd_6406139] using wordTrace_append hprefix tailTrace_6406139
  have hstable : (prefixWord ++ tailWord_6406139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406139).length < 2 ^ (prefixWord ++ tailWord_6406139).sum := by decide
  have hdescent : baseEnd_6406139 < baseStart_6406139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
