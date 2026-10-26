import V185TrunkScan22Chunk354

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3167572 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3167572 : Nat := 118140960795 + 3167572 * 2 ^ 59
def prefixEnd_3167572 : Nat := 4983230072969 + 3 ^ 40 * 3167572 * 2
def baseEnd_3167572 : Nat := 361441543049685798596135

theorem tailTrace_3167572 : CollatzResearch.WordTrace tailWord_3167572 prefixEnd_3167572 361441543049685798596135 := by
  unfold tailWord_3167572
  simp only [CollatzResearch.WordTrace]
  refine ⟨57765421040217548536616485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77020561386956731382155313 57765421040217548536616485)
  ·
    refine ⟨10831016445040790350615591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57765421040217548536616485 10831016445040790350615591)
    ·
      refine ⟨16246524667561185525923387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10831016445040790350615591 16246524667561185525923387)
      ·
        refine ⟨24369787001341778288885081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16246524667561185525923387 24369787001341778288885081)
        ·
          refine ⟨18277340251006333716663811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24369787001341778288885081 18277340251006333716663811)
          ·
            refine ⟨27416010376509500574995717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18277340251006333716663811 27416010376509500574995717)
            ·
              refine ⟨5140501945595531357811697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27416010376509500574995717 5140501945595531357811697)
              ·
                refine ⟨3855376459196648518358773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5140501945595531357811697 3855376459196648518358773)
                ·
                  refine ⟨361441543049685798596135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3855376459196648518358773 361441543049685798596135)
                  ·
                    rfl

theorem cell22_3167572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3167572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167572 prefixEnd_3167572 := by exact prefixLift 3167572
  have htrace : WordTrace (prefixWord ++ tailWord_3167572) baseStart_3167572 baseEnd_3167572 := by
    simpa [prefixWord, tailWord_3167572, baseEnd_3167572] using wordTrace_append hprefix tailTrace_3167572
  have hstable : (prefixWord ++ tailWord_3167572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167572).length < 2 ^ (prefixWord ++ tailWord_3167572).sum := by decide
  have hdescent : baseEnd_3167572 < baseStart_3167572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167600 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_3167600 : Nat := 118140960795 + 3167600 * 2 ^ 59
def prefixEnd_3167600 : Nat := 4983230072969 + 3 ^ 40 * 3167600 * 2
def baseEnd_3167600 : Nat := 361444738040424885362773

theorem tailTrace_3167600 : CollatzResearch.WordTrace tailWord_3167600 prefixEnd_3167600 361444738040424885362773 := by
  unfold tailWord_3167600
  simp only [CollatzResearch.WordTrace]
  refine ⟨57765931662166828927626127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77021242216222438570168169 57765931662166828927626127)
  ·
    refine ⟨86648897493250243391439191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57765931662166828927626127 86648897493250243391439191)
    ·
      refine ⟨129973346239875365087158787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86648897493250243391439191 129973346239875365087158787)
      ·
        refine ⟨194960019359813047630738181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129973346239875365087158787 194960019359813047630738181)
        ·
          refine ⟨36555003629964946430763409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194960019359813047630738181 36555003629964946430763409)
          ·
            refine ⟨27416252722473709823072557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36555003629964946430763409 27416252722473709823072557)
            ·
              refine ⟨10281094770927641183652209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27416252722473709823072557 10281094770927641183652209)
              ·
                refine ⟨7710821078195730887739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10281094770927641183652209 7710821078195730887739157)
                ·
                  refine ⟨361444738040424885362773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7710821078195730887739157 361444738040424885362773)
                  ·
                    rfl

theorem cell22_3167600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_3167600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167600 prefixEnd_3167600 := by exact prefixLift 3167600
  have htrace : WordTrace (prefixWord ++ tailWord_3167600) baseStart_3167600 baseEnd_3167600 := by
    simpa [prefixWord, tailWord_3167600, baseEnd_3167600] using wordTrace_append hprefix tailTrace_3167600
  have hstable : (prefixWord ++ tailWord_3167600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167600).length < 2 ^ (prefixWord ++ tailWord_3167600).sum := by decide
  have hdescent : baseEnd_3167600 < baseStart_3167600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167602 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_3167602 : Nat := 118140960795 + 3167602 * 2 ^ 59
def prefixEnd_3167602 : Nat := 4983230072969 + 3 ^ 40 * 3167602 * 2
def baseEnd_3167602 : Nat := 1084334898762147317538313

theorem tailTrace_3167602 : CollatzResearch.WordTrace tailWord_3167602 prefixEnd_3167602 1084334898762147317538313 := by
  unfold tailWord_3167602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882984067581603049206265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77021290846884274797883373 28882984067581603049206265)
  ·
    refine ⟨21662238050686202286904699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28882984067581603049206265 21662238050686202286904699)
    ·
      refine ⟨32493357076029303430357049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21662238050686202286904699 32493357076029303430357049)
      ·
        refine ⟨24370017807021977572767787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32493357076029303430357049 24370017807021977572767787)
        ·
          refine ⟨36555026710532966359151681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24370017807021977572767787 36555026710532966359151681)
          ·
            refine ⟨27416270032899724769363761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36555026710532966359151681 27416270032899724769363761)
            ·
              refine ⟨20562202524674793577022821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27416270032899724769363761 20562202524674793577022821)
              ·
                refine ⟨3855412973376523795691779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20562202524674793577022821 3855412973376523795691779)
                ·
                  refine ⟨5783119460064785693537669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855412973376523795691779 5783119460064785693537669)
                  ·
                    refine ⟨1084334898762147317538313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783119460064785693537669 1084334898762147317538313)
                    ·
                      rfl

theorem cell22_3167602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_3167602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167602 prefixEnd_3167602 := by exact prefixLift 3167602
  have htrace : WordTrace (prefixWord ++ tailWord_3167602) baseStart_3167602 baseEnd_3167602 := by
    simpa [prefixWord, tailWord_3167602, baseEnd_3167602] using wordTrace_append hprefix tailTrace_3167602
  have hstable : (prefixWord ++ tailWord_3167602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167602).length < 2 ^ (prefixWord ++ tailWord_3167602).sum := by decide
  have hdescent : baseEnd_3167602 < baseStart_3167602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167619 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 1, 4]
def baseStart_3167619 : Nat := 118140960795 + 3167619 * 2 ^ 59
def prefixEnd_3167619 : Nat := 4983230072969 + 3 ^ 40 * 3167619 * 2
def baseEnd_3167619 : Nat := 1084340718209564939863261

theorem tailTrace_3167619 : CollatzResearch.WordTrace tailWord_3167619 prefixEnd_3167619 1084340718209564939863261 := by
  unfold tailWord_3167619
  simp only [CollatzResearch.WordTrace]
  refine ⟨115532556311264824100193911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77021704207509882733462607 115532556311264824100193911)
  ·
    refine ⟨173298834466897236150290867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115532556311264824100193911 173298834466897236150290867)
    ·
      refine ⟨259948251700345854225436301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173298834466897236150290867 259948251700345854225436301)
      ·
        refine ⟨97480594387629695334538613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259948251700345854225436301 97480594387629695334538613)
        ·
          refine ⟨9138805723840283937612995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97480594387629695334538613 9138805723840283937612995)
          ·
            refine ⟨13708208585760425906419493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9138805723840283937612995 13708208585760425906419493)
            ·
              refine ⟨2570289109830079857453655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13708208585760425906419493 2570289109830079857453655)
              ·
                refine ⟨3855433664745119786180483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570289109830079857453655 3855433664745119786180483)
                ·
                  refine ⟨5783150497117679679270725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855433664745119786180483 5783150497117679679270725)
                  ·
                    refine ⟨1084340718209564939863261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783150497117679679270725 1084340718209564939863261)
                    ·
                      rfl

theorem cell22_3167619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 4].length) (baseStart_3167619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167619 prefixEnd_3167619 := by exact prefixLift 3167619
  have htrace : WordTrace (prefixWord ++ tailWord_3167619) baseStart_3167619 baseEnd_3167619 := by
    simpa [prefixWord, tailWord_3167619, baseEnd_3167619] using wordTrace_append hprefix tailTrace_3167619
  have hstable : (prefixWord ++ tailWord_3167619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167619).length < 2 ^ (prefixWord ++ tailWord_3167619).sum := by decide
  have hdescent : baseEnd_3167619 < baseStart_3167619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167694 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_3167694 : Nat := 118140960795 + 3167694 * 2 ^ 59
def prefixEnd_3167694 : Nat := 4983230072969 + 3 ^ 40 * 3167694 * 2
def baseEnd_3167694 : Nat := 1084366392242289744238031

theorem tailTrace_3167694 : CollatzResearch.WordTrace tailWord_3167694 prefixEnd_3167694 1084366392242289744238031 := by
  unfold tailWord_3167694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441911473249138988646767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77023527857328741272782757 14441911473249138988646767)
  ·
    refine ⟨21662867209873708482970151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14441911473249138988646767 21662867209873708482970151)
    ·
      refine ⟨32494300814810562724455227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21662867209873708482970151 32494300814810562724455227)
      ·
        refine ⟨48741451222215844086682841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32494300814810562724455227 48741451222215844086682841)
        ·
          refine ⟨36556088416661883065012131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48741451222215844086682841 36556088416661883065012131)
          ·
            refine ⟨54834132624992824597518197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36556088416661883065012131 54834132624992824597518197)
            ·
              refine ⟨5140699933593077306017331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54834132624992824597518197 5140699933593077306017331)
              ·
                refine ⟨7711049900389615959025997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140699933593077306017331 7711049900389615959025997)
                ·
                  refine ⟨2891643712646105984634749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7711049900389615959025997 2891643712646105984634749)
                  ·
                    refine ⟨1084366392242289744238031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891643712646105984634749 1084366392242289744238031)
                    ·
                      rfl

theorem cell22_3167694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_3167694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167694 prefixEnd_3167694 := by exact prefixLift 3167694
  have htrace : WordTrace (prefixWord ++ tailWord_3167694) baseStart_3167694 baseEnd_3167694 := by
    simpa [prefixWord, tailWord_3167694, baseEnd_3167694] using wordTrace_append hprefix tailTrace_3167694
  have hstable : (prefixWord ++ tailWord_3167694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167694).length < 2 ^ (prefixWord ++ tailWord_3167694).sum := by decide
  have hdescent : baseEnd_3167694 < baseStart_3167694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167700 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3167700 : Nat := 118140960795 + 3167700 * 2 ^ 59
def prefixEnd_3167700 : Nat := 4983230072969 + 3 ^ 40 * 3167700 * 2
def baseEnd_3167700 : Nat := 1084368446164907728588013

theorem tailTrace_3167700 : CollatzResearch.WordTrace tailWord_3167700 prefixEnd_3167700 1084368446164907728588013 := by
  unfold tailWord_3167700
  simp only [CollatzResearch.WordTrace]
  refine ⟨57767755311985687466946277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77023673749314249955928369 57767755311985687466946277)
  ·
    refine ⟨10831454120997316400052427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57767755311985687466946277 10831454120997316400052427)
    ·
      refine ⟨16247181181495974600078641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10831454120997316400052427 16247181181495974600078641)
      ·
        refine ⟨12185385886121980950058981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16247181181495974600078641 12185385886121980950058981)
        ·
          refine ⟨2284759853647871428136059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12185385886121980950058981 2284759853647871428136059)
          ·
            refine ⟨3427139780471807142204089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284759853647871428136059 3427139780471807142204089)
            ·
              refine ⟨2570354835353855356653067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427139780471807142204089 2570354835353855356653067)
              ·
                refine ⟨3855532253030783034979601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570354835353855356653067 3855532253030783034979601)
                ·
                  refine ⟨2891649189773087276234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3855532253030783034979601 2891649189773087276234701)
                  ·
                    refine ⟨1084368446164907728588013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891649189773087276234701 1084368446164907728588013)
                    ·
                      rfl

theorem cell22_3167700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3167700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167700 prefixEnd_3167700 := by exact prefixLift 3167700
  have htrace : WordTrace (prefixWord ++ tailWord_3167700) baseStart_3167700 baseEnd_3167700 := by
    simpa [prefixWord, tailWord_3167700, baseEnd_3167700] using wordTrace_append hprefix tailTrace_3167700
  have hstable : (prefixWord ++ tailWord_3167700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167700).length < 2 ^ (prefixWord ++ tailWord_3167700).sum := by decide
  have hdescent : baseEnd_3167700 < baseStart_3167700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167735 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 10]
def baseStart_3167735 : Nat := 118140960795 + 3167735 * 2 ^ 59
def prefixEnd_3167735 : Nat := 4983230072969 + 3 ^ 40 * 3167735 * 2
def baseEnd_3167735 : Nat := 361460142460059767987635

theorem tailTrace_3167735 : CollatzResearch.WordTrace tailWord_3167735 prefixEnd_3167735 361460142460059767987635 := by
  unfold tailWord_3167735
  simp only [CollatzResearch.WordTrace]
  refine ⟨115536787178844575911416659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77024524785896383940944439 115536787178844575911416659)
  ·
    refine ⟨173305180768266863867124989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115536787178844575911416659 173305180768266863867124989)
    ·
      refine ⟨64989442788100073950171871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173305180768266863867124989 64989442788100073950171871)
      ·
        refine ⟨97484164182150110925257807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64989442788100073950171871 97484164182150110925257807)
        ·
          refine ⟨146226246273225166387886711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97484164182150110925257807 146226246273225166387886711)
          ·
            refine ⟨219339369409837749581830067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146226246273225166387886711 219339369409837749581830067)
            ·
              refine ⟨329009054114756624372745101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219339369409837749581830067 329009054114756624372745101)
              ·
                refine ⟨123378395293033734139779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329009054114756624372745101 123378395293033734139779413)
                ·
                  refine ⟨361460142460059767987635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123378395293033734139779413 361460142460059767987635)
                  ·
                    rfl

theorem cell22_3167735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_3167735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167735 prefixEnd_3167735 := by exact prefixLift 3167735
  have htrace : WordTrace (prefixWord ++ tailWord_3167735) baseStart_3167735 baseEnd_3167735 := by
    simpa [prefixWord, tailWord_3167735, baseEnd_3167735] using wordTrace_append hprefix tailTrace_3167735
  have hstable : (prefixWord ++ tailWord_3167735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167735).length < 2 ^ (prefixWord ++ tailWord_3167735).sum := by decide
  have hdescent : baseEnd_3167735 < baseStart_3167735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167745 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3167745 : Nat := 118140960795 + 3167745 * 2 ^ 59
def prefixEnd_3167745 : Nat := 4983230072969 + 3 ^ 40 * 3167745 * 2
def baseEnd_3167745 : Nat := 1084383850584542611212875

theorem tailTrace_3167745 : CollatzResearch.WordTrace tailWord_3167745 prefixEnd_3167745 1084383850584542611212875 := by
  unfold tailWord_3167745
  simp only [CollatzResearch.WordTrace]
  refine ⟨115537151908808347619280689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77024767939205565079520459 115537151908808347619280689)
  ·
    refine ⟨86652863931606260714460517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115537151908808347619280689 86652863931606260714460517)
    ·
      refine ⟨16247411987176173883961347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86652863931606260714460517 16247411987176173883961347)
      ·
        refine ⟨24371117980764260825942021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16247411987176173883961347 24371117980764260825942021)
        ·
          refine ⟨4569584621393298904864129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24371117980764260825942021 4569584621393298904864129)
          ·
            refine ⟨3427188466044974178648097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4569584621393298904864129 3427188466044974178648097)
            ·
              refine ⟨2570391349533730633986073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427188466044974178648097 2570391349533730633986073)
              ·
                refine ⟨1927793512150297975489555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570391349533730633986073 1927793512150297975489555)
                ·
                  refine ⟨2891690268225446963234333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927793512150297975489555 2891690268225446963234333)
                  ·
                    refine ⟨1084383850584542611212875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891690268225446963234333 1084383850584542611212875)
                    ·
                      rfl

theorem cell22_3167745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3167745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167745 prefixEnd_3167745 := by exact prefixLift 3167745
  have htrace : WordTrace (prefixWord ++ tailWord_3167745) baseStart_3167745 baseEnd_3167745 := by
    simpa [prefixWord, tailWord_3167745, baseEnd_3167745] using wordTrace_append hprefix tailTrace_3167745
  have hstable : (prefixWord ++ tailWord_3167745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167745).length < 2 ^ (prefixWord ++ tailWord_3167745).sum := by decide
  have hdescent : baseEnd_3167745 < baseStart_3167745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167786 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_3167786 : Nat := 118140960795 + 3167786 * 2 ^ 59
def prefixEnd_3167786 : Nat := 4983230072969 + 3 ^ 40 * 3167786 * 2
def baseEnd_3167786 : Nat := 361465961907477390312583

theorem tailTrace_3167786 : CollatzResearch.WordTrace tailWord_3167786 prefixEnd_3167786 361465961907477390312583 := by
  unfold tailWord_3167786
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884661825414952905380803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77025764867773207747682141 28884661825414952905380803)
  ·
    refine ⟨43326992738122429358071205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28884661825414952905380803 43326992738122429358071205)
    ·
      refine ⟨8123811138397955504638351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43326992738122429358071205 8123811138397955504638351)
      ·
        refine ⟨12185716707596933256957527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8123811138397955504638351 12185716707596933256957527)
        ·
          refine ⟨18278575061395399885436291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12185716707596933256957527 18278575061395399885436291)
          ·
            refine ⟨27417862592093099828154437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18278575061395399885436291 27417862592093099828154437)
            ·
              refine ⟨5140849236017456217778957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27417862592093099828154437 5140849236017456217778957)
              ·
                refine ⟨1927818463506546081667109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5140849236017456217778957 1927818463506546081667109)
                ·
                  refine ⟨361465961907477390312583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927818463506546081667109 361465961907477390312583)
                  ·
                    rfl

theorem cell22_3167786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_3167786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167786 prefixEnd_3167786 := by exact prefixLift 3167786
  have htrace : WordTrace (prefixWord ++ tailWord_3167786) baseStart_3167786 baseEnd_3167786 := by
    simpa [prefixWord, tailWord_3167786, baseEnd_3167786] using wordTrace_append hprefix tailTrace_3167786
  have hstable : (prefixWord ++ tailWord_3167786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167786).length < 2 ^ (prefixWord ++ tailWord_3167786).sum := by decide
  have hdescent : baseEnd_3167786 < baseStart_3167786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167797 : List Nat := [1, 3, 3, 1, 1, 4, 9]
def baseStart_3167797 : Nat := 118140960795 + 3167797 * 2 ^ 59
def prefixEnd_3167797 : Nat := 4983230072969 + 3 ^ 40 * 3167797 * 2
def baseEnd_3167797 : Nat := 40163024120267844774545

theorem tailTrace_3167797 : CollatzResearch.WordTrace tailWord_3167797 prefixEnd_3167797 40163024120267844774545 := by
  unfold tailWord_3167797
  simp only [CollatzResearch.WordTrace]
  refine ⟨115539048504619960500173645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77026032336413307000115763 115539048504619960500173645)
  ·
    refine ⟨43327143189232485187565117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115539048504619960500173645 43327143189232485187565117)
    ·
      refine ⟨16247678695962181945336919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43327143189232485187565117 16247678695962181945336919)
      ·
        refine ⟨24371518043943272918005379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16247678695962181945336919 24371518043943272918005379)
        ·
          refine ⟨36557277065914909377008069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24371518043943272918005379 36557277065914909377008069)
          ·
            refine ⟨6854489449859045508189013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36557277065914909377008069 6854489449859045508189013)
            ·
              refine ⟨40163024120267844774545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6854489449859045508189013 40163024120267844774545)
              ·
                rfl

theorem cell22_3167797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 9].length) (baseStart_3167797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167797 prefixEnd_3167797 := by exact prefixLift 3167797
  have htrace : WordTrace (prefixWord ++ tailWord_3167797) baseStart_3167797 baseEnd_3167797 := by
    simpa [prefixWord, tailWord_3167797, baseEnd_3167797] using wordTrace_append hprefix tailTrace_3167797
  have hstable : (prefixWord ++ tailWord_3167797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167797).length < 2 ^ (prefixWord ++ tailWord_3167797).sum := by decide
  have hdescent : baseEnd_3167797 < baseStart_3167797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167801 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_3167801 : Nat := 118140960795 + 3167801 * 2 ^ 59
def prefixEnd_3167801 : Nat := 4983230072969 + 3 ^ 40 * 3167801 * 2
def baseEnd_3167801 : Nat := 1084403020528977131812703

theorem tailTrace_3167801 : CollatzResearch.WordTrace tailWord_3167801 prefixEnd_3167801 1084403020528977131812703 := by
  unfold tailWord_3167801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115539194396605469183319257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77026129597736979455546171 115539194396605469183319257)
  ·
    refine ⟨86654395797454101887489443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115539194396605469183319257 86654395797454101887489443)
    ·
      refine ⟨129981593696181152831234165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86654395797454101887489443 129981593696181152831234165)
      ·
        refine ⟨12185774409016983077928203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129981593696181152831234165 12185774409016983077928203)
        ·
          refine ⟨18278661613525474616892305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12185774409016983077928203 18278661613525474616892305)
          ·
            refine ⟨13708996210144105962669229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18278661613525474616892305 13708996210144105962669229)
            ·
              refine ⟨5140873578804039736000961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13708996210144105962669229 5140873578804039736000961)
              ·
                refine ⟨3855655184103029802000721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5140873578804039736000961 3855655184103029802000721)
                ·
                  refine ⟨2891741388077272351500541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3855655184103029802000721 2891741388077272351500541)
                  ·
                    refine ⟨1084403020528977131812703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891741388077272351500541 1084403020528977131812703)
                    ·
                      rfl

theorem cell22_3167801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_3167801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167801 prefixEnd_3167801 := by exact prefixLift 3167801
  have htrace : WordTrace (prefixWord ++ tailWord_3167801) baseStart_3167801 baseEnd_3167801 := by
    simpa [prefixWord, tailWord_3167801, baseEnd_3167801] using wordTrace_append hprefix tailTrace_3167801
  have hstable : (prefixWord ++ tailWord_3167801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167801).length < 2 ^ (prefixWord ++ tailWord_3167801).sum := by decide
  have hdescent : baseEnd_3167801 < baseStart_3167801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167837 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 4]
def baseStart_3167837 : Nat := 118140960795 + 3167837 * 2 ^ 59
def prefixEnd_3167837 : Nat := 4983230072969 + 3 ^ 40 * 3167837 * 2
def baseEnd_3167837 : Nat := 361471781354895012637531

theorem tailTrace_3167837 : CollatzResearch.WordTrace tailWord_3167837 prefixEnd_3167837 361471781354895012637531 := by
  unfold tailWord_3167837
  simp only [CollatzResearch.WordTrace]
  refine ⟨115540507424475047331629765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77027004949650031554419843 115540507424475047331629765)
  ·
    refine ⟨21663845142089071374680581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115540507424475047331629765 21663845142089071374680581)
    ·
      refine ⟨4061970964141700882752609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21663845142089071374680581 4061970964141700882752609)
      ·
        refine ⟨3046478223106275662064457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4061970964141700882752609 3046478223106275662064457)
        ·
          refine ⟨2284858667329706746548343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046478223106275662064457 2284858667329706746548343)
          ·
            refine ⟨3427288000994560119822515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284858667329706746548343 3427288000994560119822515)
            ·
              refine ⟨5140932001491840179733773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427288000994560119822515 5140932001491840179733773)
              ·
                refine ⟨1927849500559440067400165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5140932001491840179733773 1927849500559440067400165)
                ·
                  refine ⟨361471781354895012637531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927849500559440067400165 361471781354895012637531)
                  ·
                    rfl

theorem cell22_3167837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_3167837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167837 prefixEnd_3167837 := by exact prefixLift 3167837
  have htrace : WordTrace (prefixWord ++ tailWord_3167837) baseStart_3167837 baseEnd_3167837 := by
    simpa [prefixWord, tailWord_3167837, baseEnd_3167837] using wordTrace_append hprefix tailTrace_3167837
  have hstable : (prefixWord ++ tailWord_3167837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167837).length < 2 ^ (prefixWord ++ tailWord_3167837).sum := by decide
  have hdescent : baseEnd_3167837 < baseStart_3167837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167857 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3167857 : Nat := 118140960795 + 3167857 * 2 ^ 59
def prefixEnd_3167857 : Nat := 4983230072969 + 3 ^ 40 * 3167857 * 2
def baseEnd_3167857 : Nat := 1084422190473411652412531

theorem tailTrace_3167857 : CollatzResearch.WordTrace tailWord_3167857 prefixEnd_3167857 1084422190473411652412531 := by
  unfold tailWord_3167857
  simp only [CollatzResearch.WordTrace]
  refine ⟨115541236884402590747357825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77027491256268393831571883 115541236884402590747357825)
  ·
    refine ⟨86655927663301943060518369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115541236884402590747357825 86655927663301943060518369)
    ·
      refine ⟨64991945747476457295388777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86655927663301943060518369 64991945747476457295388777)
      ·
        refine ⟨48743959310607342971541583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64991945747476457295388777 48743959310607342971541583)
        ·
          refine ⟨73115938965911014457312375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48743959310607342971541583 73115938965911014457312375)
          ·
            refine ⟨109673908448866521685968563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73115938965911014457312375 109673908448866521685968563)
            ·
              refine ⟨164510862673299782528952845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109673908448866521685968563 164510862673299782528952845)
              ·
                refine ⟨61691573502487418448357317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164510862673299782528952845 61691573502487418448357317)
                ·
                  refine ⟨11567170031716390959066997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61691573502487418448357317 11567170031716390959066997)
                  ·
                    refine ⟨1084422190473411652412531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11567170031716390959066997 1084422190473411652412531)
                    ·
                      rfl

theorem cell22_3167857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3167857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167857 prefixEnd_3167857 := by exact prefixLift 3167857
  have htrace : WordTrace (prefixWord ++ tailWord_3167857) baseStart_3167857 baseEnd_3167857 := by
    simpa [prefixWord, tailWord_3167857, baseEnd_3167857] using wordTrace_append hprefix tailTrace_3167857
  have hstable : (prefixWord ++ tailWord_3167857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167857).length < 2 ^ (prefixWord ++ tailWord_3167857).sum := by decide
  have hdescent : baseEnd_3167857 < baseStart_3167857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167876 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_3167876 : Nat := 118140960795 + 3167876 * 2 ^ 59
def prefixEnd_3167876 : Nat := 4983230072969 + 3 ^ 40 * 3167876 * 2
def baseEnd_3167876 : Nat := 361476231520567312062491

theorem tailTrace_3167876 : CollatzResearch.WordTrace tailWord_3167876 prefixEnd_3167876 361476231520567312062491 := by
  unfold tailWord_3167876
  simp only [CollatzResearch.WordTrace]
  refine ⟨57770964935666878496149741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77027953247555837994866321 57770964935666878496149741)
  ·
    refine ⟨21664111850875079436056153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57770964935666878496149741 21664111850875079436056153)
    ·
      refine ⟨16248083888156309577042115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21664111850875079436056153 16248083888156309577042115)
      ·
        refine ⟨24372125832234464365563173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16248083888156309577042115 24372125832234464365563173)
        ·
          refine ⟨4569773593543962068543095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24372125832234464365563173 4569773593543962068543095)
          ·
            refine ⟨6854660390315943102814643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569773593543962068543095 6854660390315943102814643)
            ·
              refine ⟨10281990585473914654221965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854660390315943102814643 10281990585473914654221965)
              ·
                refine ⟨3855746469552717995333237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10281990585473914654221965 3855746469552717995333237)
                ·
                  refine ⟨361476231520567312062491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3855746469552717995333237 361476231520567312062491)
                  ·
                    rfl

theorem cell22_3167876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_3167876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167876 prefixEnd_3167876 := by exact prefixLift 3167876
  have htrace : WordTrace (prefixWord ++ tailWord_3167876) baseStart_3167876 baseEnd_3167876 := by
    simpa [prefixWord, tailWord_3167876, baseEnd_3167876] using wordTrace_append hprefix tailTrace_3167876
  have hstable : (prefixWord ++ tailWord_3167876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167876).length < 2 ^ (prefixWord ++ tailWord_3167876).sum := by decide
  have hdescent : baseEnd_3167876 < baseStart_3167876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167889 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3167889 : Nat := 118140960795 + 3167889 * 2 ^ 59
def prefixEnd_3167889 : Nat := 4983230072969 + 3 ^ 40 * 3167889 * 2
def baseEnd_3167889 : Nat := 1084433144727374235612433

theorem tailTrace_3167889 : CollatzResearch.WordTrace tailWord_3167889 prefixEnd_3167889 1084433144727374235612433 := by
  unfold tailWord_3167889
  simp only [CollatzResearch.WordTrace]
  refine ⟨115542404020286660212522721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77028269346857773475015147 115542404020286660212522721)
  ·
    refine ⟨86656803015214995159392041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115542404020286660212522721 86656803015214995159392041)
    ·
      refine ⟨64992602261411246369544031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86656803015214995159392041 64992602261411246369544031)
      ·
        refine ⟨97488903392116869554316047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64992602261411246369544031 97488903392116869554316047)
        ·
          refine ⟨146233355088175304331474071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97488903392116869554316047 146233355088175304331474071)
          ·
            refine ⟨219350032632262956497211107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146233355088175304331474071 219350032632262956497211107)
            ·
              refine ⟨329025048948394434745816661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219350032632262956497211107 329025048948394434745816661)
              ·
                refine ⟨3855762292363997282177539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 329025048948394434745816661 3855762292363997282177539)
                ·
                  refine ⟨5783643438545995923266309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855762292363997282177539 5783643438545995923266309)
                  ·
                    refine ⟨1084433144727374235612433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783643438545995923266309 1084433144727374235612433)
                    ·
                      rfl

theorem cell22_3167889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3167889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167889 prefixEnd_3167889 := by exact prefixLift 3167889
  have htrace : WordTrace (prefixWord ++ tailWord_3167889) baseStart_3167889 baseEnd_3167889 := by
    simpa [prefixWord, tailWord_3167889, baseEnd_3167889] using wordTrace_append hprefix tailTrace_3167889
  have hstable : (prefixWord ++ tailWord_3167889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167889).length < 2 ^ (prefixWord ++ tailWord_3167889).sum := by decide
  have hdescent : baseEnd_3167889 < baseStart_3167889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167936 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_3167936 : Nat := 118140960795 + 3167936 * 2 ^ 59
def prefixEnd_3167936 : Nat := 4983230072969 + 3 ^ 40 * 3167936 * 2
def baseEnd_3167936 : Nat := 1084449233787881779687289

theorem tailTrace_3167936 : CollatzResearch.WordTrace tailWord_3167936 prefixEnd_3167936 1084449233787881779687289 := by
  unfold tailWord_3167936
  simp only [CollatzResearch.WordTrace]
  refine ⟨57772059125558193619741831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77029412167410924826322441 57772059125558193619741831)
  ·
    refine ⟨86658088688337290429612747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57772059125558193619741831 86658088688337290429612747)
    ·
      refine ⟨129987133032505935644419121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86658088688337290429612747 129987133032505935644419121)
      ·
        refine ⟨97490349774379451733314341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129987133032505935644419121 97490349774379451733314341)
        ·
          refine ⟨18279440582696147199996439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97490349774379451733314341 18279440582696147199996439)
          ·
            refine ⟨27419160874044220799994659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279440582696147199996439 27419160874044220799994659)
            ·
              refine ⟨41128741311066331199991989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27419160874044220799994659 41128741311066331199991989)
              ·
                refine ⟨3855819497912468549999249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41128741311066331199991989 3855819497912468549999249)
                ·
                  refine ⟨2891864623434351412499437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3855819497912468549999249 2891864623434351412499437)
                  ·
                    refine ⟨1084449233787881779687289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891864623434351412499437 1084449233787881779687289)
                    ·
                      rfl

theorem cell22_3167936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_3167936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167936 prefixEnd_3167936 := by exact prefixLift 3167936
  have htrace : WordTrace (prefixWord ++ tailWord_3167936) baseStart_3167936 baseEnd_3167936 := by
    simpa [prefixWord, tailWord_3167936, baseEnd_3167936] using wordTrace_append hprefix tailTrace_3167936
  have hstable : (prefixWord ++ tailWord_3167936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167936).length < 2 ^ (prefixWord ++ tailWord_3167936).sum := by decide
  have hdescent : baseEnd_3167936 < baseStart_3167936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168058 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_3168058 : Nat := 118140960795 + 3168058 * 2 ^ 59
def prefixEnd_3168058 : Nat := 4983230072969 + 3 ^ 40 * 3168058 * 2
def baseEnd_3168058 : Nat := 1084490996881114128136915

theorem tailTrace_3168058 : CollatzResearch.WordTrace tailWord_3168058 prefixEnd_3168058 1084490996881114128136915 := by
  unfold tailWord_3168058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887141989168600518856207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77032378637782934716949885 28887141989168600518856207)
  ·
    refine ⟨43330712983752900778284311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28887141989168600518856207 43330712983752900778284311)
    ·
      refine ⟨64996069475629351167426467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43330712983752900778284311 64996069475629351167426467)
      ·
        refine ⟨97494104213444026751139701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64996069475629351167426467 97494104213444026751139701)
        ·
          refine ⟨9140072270010377507919347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97494104213444026751139701 9140072270010377507919347)
          ·
            refine ⟨13710108405015566261879021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140072270010377507919347 13710108405015566261879021)
            ·
              refine ⟨5141290651880837348204633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13710108405015566261879021 5141290651880837348204633)
              ·
                refine ⟨3855967988910628011153475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141290651880837348204633 3855967988910628011153475)
                ·
                  refine ⟨5783951983365942016730213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855967988910628011153475 5783951983365942016730213)
                  ·
                    refine ⟨1084490996881114128136915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783951983365942016730213 1084490996881114128136915)
                    ·
                      rfl

theorem cell22_3168058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_3168058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168058 prefixEnd_3168058 := by exact prefixLift 3168058
  have htrace : WordTrace (prefixWord ++ tailWord_3168058) baseStart_3168058 baseEnd_3168058 := by
    simpa [prefixWord, tailWord_3168058, baseEnd_3168058] using wordTrace_append hprefix tailTrace_3168058
  have hstable : (prefixWord ++ tailWord_3168058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168058).length < 2 ^ (prefixWord ++ tailWord_3168058).sum := by decide
  have hdescent : baseEnd_3168058 < baseStart_3168058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168071 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 6, 3]
def baseStart_3168071 : Nat := 118140960795 + 3168071 * 2 ^ 59
def prefixEnd_3168071 : Nat := 4983230072969 + 3 ^ 40 * 3168071 * 2
def baseEnd_3168071 : Nat := 1084495447046786427561875

theorem tailTrace_3168071 : CollatzResearch.WordTrace tailWord_3168071 prefixEnd_3168071 1084495447046786427561875 := by
  unfold tailWord_3168071
  simp only [CollatzResearch.WordTrace]
  refine ⟨115549042105627305295648067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77032694737084870197098711 115549042105627305295648067)
  ·
    refine ⟨173323563158440957943472101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115549042105627305295648067 173323563158440957943472101)
    ·
      refine ⟨32498168092207679614401019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173323563158440957943472101 32498168092207679614401019)
      ·
        refine ⟨48747252138311519421601529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32498168092207679614401019 48747252138311519421601529)
        ·
          refine ⟨36560439103733639566201147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48747252138311519421601529 36560439103733639566201147)
          ·
            refine ⟨54840658655600459349301721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36560439103733639566201147 54840658655600459349301721)
            ·
              refine ⟨41130493991700344511976291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54840658655600459349301721 41130493991700344511976291)
              ·
                refine ⟨61695740987550516767964437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41130493991700344511976291 61695740987550516767964437)
                ·
                  refine ⟨2891987858791430473498333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61695740987550516767964437 2891987858791430473498333)
                  ·
                    refine ⟨1084495447046786427561875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891987858791430473498333 1084495447046786427561875)
                    ·
                      rfl

theorem cell22_3168071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_3168071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168071 prefixEnd_3168071 := by exact prefixLift 3168071
  have htrace : WordTrace (prefixWord ++ tailWord_3168071) baseStart_3168071 baseEnd_3168071 := by
    simpa [prefixWord, tailWord_3168071, baseEnd_3168071] using wordTrace_append hprefix tailTrace_3168071
  have hstable : (prefixWord ++ tailWord_3168071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168071).length < 2 ^ (prefixWord ++ tailWord_3168071).sum := by decide
  have hdescent : baseEnd_3168071 < baseStart_3168071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168208 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 4]
def baseStart_3168208 : Nat := 118140960795 + 3168208 * 2 ^ 59
def prefixEnd_3168208 : Nat := 4983230072969 + 3 ^ 40 * 3168208 * 2
def baseEnd_3168208 : Nat := 361514114982187912295485

theorem tailTrace_3168208 : CollatzResearch.WordTrace tailWord_3168208 prefixEnd_3168208 361514114982187912295485 := by
  unfold tailWord_3168208
  simp only [CollatzResearch.WordTrace]
  refine ⟨57777019453065488846692639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77036025937420651795590185 57777019453065488846692639)
  ·
    refine ⟨86665529179598233270038959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57777019453065488846692639 86665529179598233270038959)
    ·
      refine ⟨129998293769397349905058439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86665529179598233270038959 129998293769397349905058439)
      ·
        refine ⟨194997440654096024857587659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129998293769397349905058439 194997440654096024857587659)
        ·
          refine ⟨292496160981144037286381489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194997440654096024857587659 292496160981144037286381489)
          ·
            refine ⟨219372120735858027964786117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292496160981144037286381489 219372120735858027964786117)
            ·
              refine ⟨41132272637973380243397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219372120735858027964786117 41132272637973380243397397)
              ·
                refine ⟨1928075279905002198909253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41132272637973380243397397 1928075279905002198909253)
                ·
                  refine ⟨361514114982187912295485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1928075279905002198909253 361514114982187912295485)
                  ·
                    rfl

theorem cell22_3168208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_3168208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168208 prefixEnd_3168208 := by exact prefixLift 3168208
  have htrace : WordTrace (prefixWord ++ tailWord_3168208) baseStart_3168208 baseEnd_3168208 := by
    simpa [prefixWord, tailWord_3168208, baseEnd_3168208] using wordTrace_append hprefix tailTrace_3168208
  have hstable : (prefixWord ++ tailWord_3168208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168208).length < 2 ^ (prefixWord ++ tailWord_3168208).sum := by decide
  have hdescent : baseEnd_3168208 < baseStart_3168208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168214 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3168214 : Nat := 118140960795 + 3168214 * 2 ^ 59
def prefixEnd_3168214 : Nat := 4983230072969 + 3 ^ 40 * 3168214 * 2
def baseEnd_3168214 : Nat := 361514799623060573745479

theorem tailTrace_3168214 : CollatzResearch.WordTrace tailWord_3168214 prefixEnd_3168214 361514799623060573745479 := by
  unfold tailWord_3168214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222141109006827544881481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77036171829406160478735797 7222141109006827544881481)
  ·
    refine ⟨5416605831755120658661111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7222141109006827544881481 5416605831755120658661111)
    ·
      refine ⟨8124908747632680987991667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5416605831755120658661111 8124908747632680987991667)
      ·
        refine ⟨12187363121449021481987501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124908747632680987991667 12187363121449021481987501)
        ·
          refine ⟨4570261170543383055745313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12187363121449021481987501 4570261170543383055745313)
          ·
            refine ⟨3427695877907537291808985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570261170543383055745313 3427695877907537291808985)
            ·
              refine ⟨2570771908430652968856739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427695877907537291808985 2570771908430652968856739)
              ·
                refine ⟨3856157862645979453285109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570771908430652968856739 3856157862645979453285109)
                ·
                  refine ⟨361514799623060573745479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3856157862645979453285109 361514799623060573745479)
                  ·
                    rfl

theorem cell22_3168214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3168214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168214 prefixEnd_3168214 := by exact prefixLift 3168214
  have htrace : WordTrace (prefixWord ++ tailWord_3168214) baseStart_3168214 baseEnd_3168214 := by
    simpa [prefixWord, tailWord_3168214, baseEnd_3168214] using wordTrace_append hprefix tailTrace_3168214
  have hstable : (prefixWord ++ tailWord_3168214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168214).length < 2 ^ (prefixWord ++ tailWord_3168214).sum := by decide
  have hdescent : baseEnd_3168214 < baseStart_3168214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168281 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 9]
def baseStart_3168281 : Nat := 118140960795 + 3168281 * 2 ^ 59
def prefixEnd_3168281 : Nat := 4983230072969 + 3 ^ 40 * 3168281 * 2
def baseEnd_3168281 : Nat := 361522444779471959937077

theorem tailTrace_3168281 : CollatzResearch.WordTrace tailWord_3168281 prefixEnd_3168281 361522444779471959937077 := by
  unfold tailWord_3168281
  simp only [CollatzResearch.WordTrace]
  refine ⟨115556701434866511160792697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77037800956577674107195131 115556701434866511160792697)
  ·
    refine ⟨86667526076149883370594523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115556701434866511160792697 86667526076149883370594523)
    ·
      refine ⟨130001289114224825055891785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86667526076149883370594523 130001289114224825055891785)
      ·
        refine ⟨97500966835668618791918839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130001289114224825055891785 97500966835668618791918839)
        ·
          refine ⟨146251450253502928187878259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97500966835668618791918839 146251450253502928187878259)
          ·
            refine ⟨219377175380254392281817389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146251450253502928187878259 219377175380254392281817389)
            ·
              refine ⟨82266440767595397105681521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219377175380254392281817389 82266440767595397105681521)
              ·
                refine ⟨61699830575696547829261141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82266440767595397105681521 61699830575696547829261141)
                ·
                  refine ⟨361522444779471959937077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61699830575696547829261141 361522444779471959937077)
                  ·
                    rfl

theorem cell22_3168281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_3168281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168281 prefixEnd_3168281 := by exact prefixLift 3168281
  have htrace : WordTrace (prefixWord ++ tailWord_3168281) baseStart_3168281 baseEnd_3168281 := by
    simpa [prefixWord, tailWord_3168281, baseEnd_3168281] using wordTrace_append hprefix tailTrace_3168281
  have hstable : (prefixWord ++ tailWord_3168281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168281).length < 2 ^ (prefixWord ++ tailWord_3168281).sum := by decide
  have hdescent : baseEnd_3168281 < baseStart_3168281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168285 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3168285 : Nat := 118140960795 + 3168285 * 2 ^ 59
def prefixEnd_3168285 : Nat := 4983230072969 + 3 ^ 40 * 3168285 * 2
def baseEnd_3168285 : Nat := 1084568703620161202711219

theorem tailTrace_3168285 : CollatzResearch.WordTrace tailWord_3168285 prefixEnd_3168285 1084568703620161202711219 := by
  unfold tailWord_3168285
  simp only [CollatzResearch.WordTrace]
  refine ⟨115556847326852019843938309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77037898217901346562625539 115556847326852019843938309)
  ·
    refine ⟨21666908873784753720738433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115556847326852019843938309 21666908873784753720738433)
    ·
      refine ⟨16250181655338565290553825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21666908873784753720738433 16250181655338565290553825)
      ·
        refine ⟨12187636241503923967915369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16250181655338565290553825 12187636241503923967915369)
        ·
          refine ⟨9140727181127942975936527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12187636241503923967915369 9140727181127942975936527)
          ·
            refine ⟨13711090771691914463904791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140727181127942975936527 13711090771691914463904791)
            ·
              refine ⟨20566636157537871695857187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711090771691914463904791 20566636157537871695857187)
              ·
                refine ⟨30849954236306807543785781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20566636157537871695857187 30849954236306807543785781)
                ·
                  refine ⟨2892183209653763207229917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30849954236306807543785781 2892183209653763207229917)
                  ·
                    refine ⟨1084568703620161202711219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892183209653763207229917 1084568703620161202711219)
                    ·
                      rfl

theorem cell22_3168285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3168285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168285 prefixEnd_3168285 := by exact prefixLift 3168285
  have htrace : WordTrace (prefixWord ++ tailWord_3168285) baseStart_3168285 baseEnd_3168285 := by
    simpa [prefixWord, tailWord_3168285, baseEnd_3168285] using wordTrace_append hprefix tailTrace_3168285
  have hstable : (prefixWord ++ tailWord_3168285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168285).length < 2 ^ (prefixWord ++ tailWord_3168285).sum := by decide
  have hdescent : baseEnd_3168285 < baseStart_3168285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168328 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3168328 : Nat := 118140960795 + 3168328 * 2 ^ 59
def prefixEnd_3168328 : Nat := 4983230072969 + 3 ^ 40 * 3168328 * 2
def baseEnd_3168328 : Nat := 1084583423398923423886087

theorem tailTrace_3168328 : CollatzResearch.WordTrace tailWord_3168328 prefixEnd_3168328 1084583423398923423886087 := by
  unfold tailWord_3168328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57779207832848119093876819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77038943777130825458502425 57779207832848119093876819)
  ·
    refine ⟨86668811749272178640815229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57779207832848119093876819 86668811749272178640815229)
    ·
      refine ⟨32500804405977066990305711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86668811749272178640815229 32500804405977066990305711)
      ·
        refine ⟨48751206608965600485458567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32500804405977066990305711 48751206608965600485458567)
        ·
          refine ⟨73126809913448400728187851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48751206608965600485458567 73126809913448400728187851)
          ·
            refine ⟨109690214870172601092281777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73126809913448400728187851 109690214870172601092281777)
            ·
              refine ⟨82267661152629450819211333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109690214870172601092281777 82267661152629450819211333)
              ·
                refine ⟨15425186466118022028602125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82267661152629450819211333 15425186466118022028602125)
                ·
                  refine ⟨5784444924794258260725797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15425186466118022028602125 5784444924794258260725797)
                  ·
                    refine ⟨1084583423398923423886087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5784444924794258260725797 1084583423398923423886087)
                    ·
                      rfl

theorem cell22_3168328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3168328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168328 prefixEnd_3168328 := by exact prefixLift 3168328
  have htrace : WordTrace (prefixWord ++ tailWord_3168328) baseStart_3168328 baseEnd_3168328 := by
    simpa [prefixWord, tailWord_3168328, baseEnd_3168328] using wordTrace_append hprefix tailTrace_3168328
  have hstable : (prefixWord ++ tailWord_3168328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168328).length < 2 ^ (prefixWord ++ tailWord_3168328).sum := by decide
  have hdescent : baseEnd_3168328 < baseStart_3168328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168343 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 6]
def baseStart_3168343 : Nat := 118140960795 + 3168343 * 2 ^ 59
def prefixEnd_3168343 : Nat := 4983230072969 + 3 ^ 40 * 3168343 * 2
def baseEnd_3168343 : Nat := 361529519401822794920347

theorem tailTrace_3168343 : CollatzResearch.WordTrace tailWord_3168343 prefixEnd_3168343 361529519401822794920347 := by
  unfold tailWord_3168343
  simp only [CollatzResearch.WordTrace]
  refine ⟨115558962760641895749549683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77039308507094597166366455 115558962760641895749549683)
  ·
    refine ⟨173338444140962843624324525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115558962760641895749549683 173338444140962843624324525)
    ·
      refine ⟨65001916552861066359121697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173338444140962843624324525 65001916552861066359121697)
      ·
        refine ⟨48751437414645799769341273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65001916552861066359121697 48751437414645799769341273)
        ·
          refine ⟨36563578060984349827005955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48751437414645799769341273 36563578060984349827005955)
          ·
            refine ⟨54845367091476524740508933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36563578060984349827005955 54845367091476524740508933)
            ·
              refine ⟨10283506329651848388845425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54845367091476524740508933 10283506329651848388845425)
              ·
                refine ⟨7712629747238886291634069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10283506329651848388845425 7712629747238886291634069)
                ·
                  refine ⟨361529519401822794920347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7712629747238886291634069 361529519401822794920347)
                  ·
                    rfl

theorem cell22_3168343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 6].length) (baseStart_3168343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168343 prefixEnd_3168343 := by exact prefixLift 3168343
  have htrace : WordTrace (prefixWord ++ tailWord_3168343) baseStart_3168343 baseEnd_3168343 := by
    simpa [prefixWord, tailWord_3168343, baseEnd_3168343] using wordTrace_append hprefix tailTrace_3168343
  have hstable : (prefixWord ++ tailWord_3168343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168343).length < 2 ^ (prefixWord ++ tailWord_3168343).sum := by decide
  have hdescent : baseEnd_3168343 < baseStart_3168343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168345 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_3168345 : Nat := 118140960795 + 3168345 * 2 ^ 59
def prefixEnd_3168345 : Nat := 4983230072969 + 3 ^ 40 * 3168345 * 2
def baseEnd_3168345 : Nat := 1084589242846341046211035

theorem tailTrace_3168345 : CollatzResearch.WordTrace tailWord_3168345 prefixEnd_3168345 1084589242846341046211035 := by
  unfold tailWord_3168345
  simp only [CollatzResearch.WordTrace]
  refine ⟨115559035706634650091122489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77039357137756433394081659 115559035706634650091122489)
  ·
    refine ⟨86669276779975987568341867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115559035706634650091122489 86669276779975987568341867)
    ·
      refine ⟨130003915169963981352512801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86669276779975987568341867 130003915169963981352512801)
      ·
        refine ⟨97502936377472986014384601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130003915169963981352512801 97502936377472986014384601)
        ·
          refine ⟨73127202283104739510788451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97502936377472986014384601 73127202283104739510788451)
          ·
            refine ⟨109690803424657109266182677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73127202283104739510788451 109690803424657109266182677)
            ·
              refine ⟨5141756410530801996852313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109690803424657109266182677 5141756410530801996852313)
              ·
                refine ⟨3856317307898101497639235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141756410530801996852313 3856317307898101497639235)
                ·
                  refine ⟨5784475961847152246458853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856317307898101497639235 5784475961847152246458853)
                  ·
                    refine ⟨1084589242846341046211035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5784475961847152246458853 1084589242846341046211035)
                    ·
                      rfl

theorem cell22_3168345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_3168345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168345 prefixEnd_3168345 := by exact prefixLift 3168345
  have htrace : WordTrace (prefixWord ++ tailWord_3168345) baseStart_3168345 baseEnd_3168345 := by
    simpa [prefixWord, tailWord_3168345, baseEnd_3168345] using wordTrace_append hprefix tailTrace_3168345
  have hstable : (prefixWord ++ tailWord_3168345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168345).length < 2 ^ (prefixWord ++ tailWord_3168345).sum := by decide
  have hdescent : baseEnd_3168345 < baseStart_3168345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168375 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 4, 3]
def baseStart_3168375 : Nat := 118140960795 + 3168375 * 2 ^ 59
def prefixEnd_3168375 : Nat := 4983230072969 + 3 ^ 40 * 3168375 * 2
def baseEnd_3168375 : Nat := 1084599512459430967960943

theorem tailTrace_3168375 : CollatzResearch.WordTrace tailWord_3168375 prefixEnd_3168375 1084599512459430967960943 := by
  unfold tailWord_3168375
  simp only [CollatzResearch.WordTrace]
  refine ⟨115560129896525965214714579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77040086597683976809809719 115560129896525965214714579)
  ·
    refine ⟨173340194844788947822071869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115560129896525965214714579 173340194844788947822071869)
    ·
      refine ⟨65002573066795855433276951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173340194844788947822071869 65002573066795855433276951)
      ·
        refine ⟨97503859600193783149915427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65002573066795855433276951 97503859600193783149915427)
        ·
          refine ⟨146255789400290674724873141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97503859600193783149915427 146255789400290674724873141)
          ·
            refine ⟨13711480256277250755456857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146255789400290674724873141 13711480256277250755456857)
            ·
              refine ⟨10283610192207938066592643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13711480256277250755456857 10283610192207938066592643)
              ·
                refine ⟨15425415288311907099888965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10283610192207938066592643 15425415288311907099888965)
                ·
                  refine ⟨2892265366558482581229181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15425415288311907099888965 2892265366558482581229181)
                  ·
                    refine ⟨1084599512459430967960943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892265366558482581229181 1084599512459430967960943)
                    ·
                      rfl

theorem cell22_3168375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_3168375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168375 prefixEnd_3168375 := by exact prefixLift 3168375
  have htrace : WordTrace (prefixWord ++ tailWord_3168375) baseStart_3168375 baseEnd_3168375 := by
    simpa [prefixWord, tailWord_3168375, baseEnd_3168375] using wordTrace_append hprefix tailTrace_3168375
  have hstable : (prefixWord ++ tailWord_3168375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168375).length < 2 ^ (prefixWord ++ tailWord_3168375).sum := by decide
  have hdescent : baseEnd_3168375 < baseStart_3168375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168407 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 2, 4]
def baseStart_3168407 : Nat := 118140960795 + 3168407 * 2 ^ 59
def prefixEnd_3168407 : Nat := 4983230072969 + 3 ^ 40 * 3168407 * 2
def baseEnd_3168407 : Nat := 1084610466713393551160845

theorem tailTrace_3168407 : CollatzResearch.WordTrace tailWord_3168407 prefixEnd_3168407 1084610466713393551160845 := by
  unfold tailWord_3168407
  simp only [CollatzResearch.WordTrace]
  refine ⟨115561297032410034679879475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77040864688273356453252983 115561297032410034679879475)
  ·
    refine ⟨173341945548615052019819213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115561297032410034679879475 173341945548615052019819213)
    ·
      refine ⟨65003229580730644507432205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173341945548615052019819213 65003229580730644507432205)
      ·
        refine ⟨24376211092773991690287077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65003229580730644507432205 24376211092773991690287077)
        ·
          refine ⟨4570539579895123441928827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24376211092773991690287077 4570539579895123441928827)
          ·
            refine ⟨6855809369842685162893241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570539579895123441928827 6855809369842685162893241)
            ·
              refine ⟨5141857027382013872169931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855809369842685162893241 5141857027382013872169931)
              ·
                refine ⟨7712785541073020808254897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141857027382013872169931 7712785541073020808254897)
                ·
                  refine ⟨5784589155804765606191173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712785541073020808254897 5784589155804765606191173)
                  ·
                    refine ⟨1084610466713393551160845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5784589155804765606191173 1084610466713393551160845)
                    ·
                      rfl

theorem cell22_3168407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_3168407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168407 prefixEnd_3168407 := by exact prefixLift 3168407
  have htrace : WordTrace (prefixWord ++ tailWord_3168407) baseStart_3168407 baseEnd_3168407 := by
    simpa [prefixWord, tailWord_3168407, baseEnd_3168407] using wordTrace_append hprefix tailTrace_3168407
  have hstable : (prefixWord ++ tailWord_3168407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168407).length < 2 ^ (prefixWord ++ tailWord_3168407).sum := by decide
  have hdescent : baseEnd_3168407 < baseStart_3168407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168426 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3168426 : Nat := 118140960795 + 3168426 * 2 ^ 59
def prefixEnd_3168426 : Nat := 4983230072969 + 3 ^ 40 * 3168426 * 2
def baseEnd_3168426 : Nat := 1084616970801683834935787

theorem tailTrace_3168426 : CollatzResearch.WordTrace tailWord_3168426 prefixEnd_3168426 1084616970801683834935787 := by
  unfold tailWord_3168426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28890497504835300231205283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77041326679560800616547421 28890497504835300231205283)
  ·
    refine ⟨43335746257252950346807925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28890497504835300231205283 43335746257252950346807925)
    ·
      refine ⟨4062726211617464095013243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43335746257252950346807925 4062726211617464095013243)
      ·
        refine ⟨6094089317426196142519865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062726211617464095013243 6094089317426196142519865)
        ·
          refine ⟨4570566988069647106889899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6094089317426196142519865 4570566988069647106889899)
          ·
            refine ⟨6855850482104470660334849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570566988069647106889899 6855850482104470660334849)
            ·
              refine ⟨5141887861578352995251137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855850482104470660334849 5141887861578352995251137)
              ·
                refine ⟨3856415896183764746438353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141887861578352995251137 3856415896183764746438353)
                ·
                  refine ⟨2892311922137823559828765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856415896183764746438353 2892311922137823559828765)
                  ·
                    refine ⟨1084616970801683834935787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892311922137823559828765 1084616970801683834935787)
                    ·
                      rfl

theorem cell22_3168426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3168426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168426 prefixEnd_3168426 := by exact prefixLift 3168426
  have htrace : WordTrace (prefixWord ++ tailWord_3168426) baseStart_3168426 baseEnd_3168426 := by
    simpa [prefixWord, tailWord_3168426, baseEnd_3168426] using wordTrace_append hprefix tailTrace_3168426
  have hstable : (prefixWord ++ tailWord_3168426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168426).length < 2 ^ (prefixWord ++ tailWord_3168426).sum := by decide
  have hdescent : baseEnd_3168426 < baseStart_3168426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168495 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 6]
def baseStart_3168495 : Nat := 118140960795 + 3168495 * 2 ^ 59
def prefixEnd_3168495 : Nat := 4983230072969 + 3 ^ 40 * 3168495 * 2
def baseEnd_3168495 : Nat := 361546863637263551653525

theorem tailTrace_3168495 : CollatzResearch.WordTrace tailWord_3168495 prefixEnd_3168495 361546863637263551653525 := by
  unfold tailWord_3168495
  simp only [CollatzResearch.WordTrace]
  refine ⟨115564506656091225709082939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77043004437394150472721959 115564506656091225709082939)
  ·
    refine ⟨173346759984136838563624409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115564506656091225709082939 173346759984136838563624409)
    ·
      refine ⟨130010069988102628922718307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173346759984136838563624409 130010069988102628922718307)
      ·
        refine ⟨195015104982153943384077461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130010069988102628922718307 195015104982153943384077461)
        ·
          refine ⟨9141333046038466096128631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195015104982153943384077461 9141333046038466096128631)
          ·
            refine ⟨13711999569057699144192947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141333046038466096128631 13711999569057699144192947)
            ·
              refine ⟨20567999353586548716289421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711999569057699144192947 20567999353586548716289421)
              ·
                refine ⟨7712999757594955768608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20567999353586548716289421 7712999757594955768608533)
                ·
                  refine ⟨361546863637263551653525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7712999757594955768608533 361546863637263551653525)
                  ·
                    rfl

theorem cell22_3168495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 6].length) (baseStart_3168495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168495 prefixEnd_3168495 := by exact prefixLift 3168495
  have htrace : WordTrace (prefixWord ++ tailWord_3168495) baseStart_3168495 baseEnd_3168495 := by
    simpa [prefixWord, tailWord_3168495, baseEnd_3168495] using wordTrace_append hprefix tailTrace_3168495
  have hstable : (prefixWord ++ tailWord_3168495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168495).length < 2 ^ (prefixWord ++ tailWord_3168495).sum := by decide
  have hdescent : baseEnd_3168495 < baseStart_3168495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168514 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3168514 : Nat := 118140960795 + 3168514 * 2 ^ 59
def prefixEnd_3168514 : Nat := 4983230072969 + 3 ^ 40 * 3168514 * 2
def baseEnd_3168514 : Nat := 1084647095000080938735517

theorem tailTrace_3168514 : CollatzResearch.WordTrace tailWord_3168514 prefixEnd_3168514 1084647095000080938735517 := by
  unfold tailWord_3168514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28891299910755597988506149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77043466428681594636016397 28891299910755597988506149)
  ·
    refine ⟨5417118733266674622844903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28891299910755597988506149 5417118733266674622844903)
    ·
      refine ⟨8125678099900011934267355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5417118733266674622844903 8125678099900011934267355)
      ·
        refine ⟨12188517149850017901401033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8125678099900011934267355 12188517149850017901401033)
        ·
          refine ⟨9141387862387513426050775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12188517149850017901401033 9141387862387513426050775)
          ·
            refine ⟨13712081793581270139076163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141387862387513426050775 13712081793581270139076163)
            ·
              refine ⟨20568122690371905208614245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13712081793581270139076163 20568122690371905208614245)
              ·
                refine ⟨3856523004444732226615171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20568122690371905208614245 3856523004444732226615171)
                ·
                  refine ⟨5784784506667098339922757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856523004444732226615171 5784784506667098339922757)
                  ·
                    refine ⟨1084647095000080938735517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5784784506667098339922757 1084647095000080938735517)
                    ·
                      rfl

theorem cell22_3168514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3168514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168514 prefixEnd_3168514 := by exact prefixLift 3168514
  have htrace : WordTrace (prefixWord ++ tailWord_3168514) baseStart_3168514 baseEnd_3168514 := by
    simpa [prefixWord, tailWord_3168514, baseEnd_3168514] using wordTrace_append hprefix tailTrace_3168514
  have hstable : (prefixWord ++ tailWord_3168514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168514).length < 2 ^ (prefixWord ++ tailWord_3168514).sum := by decide
  have hdescent : baseEnd_3168514 < baseStart_3168514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168529 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 4]
def baseStart_3168529 : Nat := 118140960795 + 3168529 * 2 ^ 59
def prefixEnd_3168529 : Nat := 4983230072969 + 3 ^ 40 * 3168529 * 2
def baseEnd_3168529 : Nat := 361550743268875299870157

theorem tailTrace_3168529 : CollatzResearch.WordTrace tailWord_3168529 prefixEnd_3168529 361550743268875299870157 := by
  unfold tailWord_3168529
  simp only [CollatzResearch.WordTrace]
  refine ⟨115565746737968049515820641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77043831158645366343880427 115565746737968049515820641)
  ·
    refine ⟨86674310053476037136865481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115565746737968049515820641 86674310053476037136865481)
    ·
      refine ⟨65005732540107027852649111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86674310053476037136865481 65005732540107027852649111)
      ·
        refine ⟨97508598810160541778973667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65005732540107027852649111 97508598810160541778973667)
        ·
          refine ⟨146262898215240812668460501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97508598810160541778973667 146262898215240812668460501)
          ·
            refine ⟨3428036676919706546917043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 146262898215240812668460501 3428036676919706546917043)
            ·
              refine ⟨5142055015379559820375565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428036676919706546917043 5142055015379559820375565)
              ·
                refine ⟨1928270630767334932640837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5142055015379559820375565 1928270630767334932640837)
                ·
                  refine ⟨361550743268875299870157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1928270630767334932640837 361550743268875299870157)
                  ·
                    rfl

theorem cell22_3168529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_3168529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168529 prefixEnd_3168529 := by exact prefixLift 3168529
  have htrace : WordTrace (prefixWord ++ tailWord_3168529) baseStart_3168529 baseEnd_3168529 := by
    simpa [prefixWord, tailWord_3168529, baseEnd_3168529] using wordTrace_append hprefix tailTrace_3168529
  have hstable : (prefixWord ++ tailWord_3168529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168529).length < 2 ^ (prefixWord ++ tailWord_3168529).sum := by decide
  have hdescent : baseEnd_3168529 < baseStart_3168529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168546 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3168546 : Nat := 118140960795 + 3168546 * 2 ^ 59
def prefixEnd_3168546 : Nat := 4983230072969 + 3 ^ 40 * 3168546 * 2
def baseEnd_3168546 : Nat := 361552683084681173978473

theorem tailTrace_3168546 : CollatzResearch.WordTrace tailWord_3168546 prefixEnd_3168546 361552683084681173978473 := by
  unfold tailWord_3168546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28891591694726615354797373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77044244519270974279459661 28891591694726615354797373)
  ·
    refine ⟨10834346885522480758049015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28891591694726615354797373 10834346885522480758049015)
    ·
      refine ⟨16251520328283721137073523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10834346885522480758049015 16251520328283721137073523)
      ·
        refine ⟨24377280492425581705610285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16251520328283721137073523 24377280492425581705610285)
        ·
          refine ⟨9141480184659593139603857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24377280492425581705610285 9141480184659593139603857)
          ·
            refine ⟨6856110138494694854702893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9141480184659593139603857 6856110138494694854702893)
            ·
              refine ⟨2571041301935510570513585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6856110138494694854702893 2571041301935510570513585)
              ·
                refine ⟨1928280976451632927885189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571041301935510570513585 1928280976451632927885189)
                ·
                  refine ⟨361552683084681173978473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1928280976451632927885189 361552683084681173978473)
                  ·
                    rfl

theorem cell22_3168546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3168546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168546 prefixEnd_3168546 := by exact prefixLift 3168546
  have htrace : WordTrace (prefixWord ++ tailWord_3168546) baseStart_3168546 baseEnd_3168546 := by
    simpa [prefixWord, tailWord_3168546, baseEnd_3168546] using wordTrace_append hprefix tailTrace_3168546
  have hstable : (prefixWord ++ tailWord_3168546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168546).length < 2 ^ (prefixWord ++ tailWord_3168546).sum := by decide
  have hdescent : baseEnd_3168546 < baseStart_3168546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168572 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_3168572 : Nat := 118140960795 + 3168572 * 2 ^ 59
def prefixEnd_3168572 : Nat := 4983230072969 + 3 ^ 40 * 3168572 * 2
def baseEnd_3168572 : Nat := 1084666949585388120785339

theorem tailTrace_3168572 : CollatzResearch.WordTrace tailWord_3168572 prefixEnd_3168572 1084666949585388120785339 := by
  unfold tailWord_3168572
  simp only [CollatzResearch.WordTrace]
  refine ⟨57783657538406133929817985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77044876717874845239757313 57783657538406133929817985)
  ·
    refine ⟨43337743153804600447363489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57783657538406133929817985 43337743153804600447363489)
    ·
      refine ⟨32503307365353450335522617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43337743153804600447363489 32503307365353450335522617)
      ·
        refine ⟨24377480524015087751641963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32503307365353450335522617 24377480524015087751641963)
        ·
          refine ⟨36566220786022631627462945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24377480524015087751641963 36566220786022631627462945)
          ·
            refine ⟨27424665589516973720597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36566220786022631627462945 27424665589516973720597209)
            ·
              refine ⟨20568499192137730290447907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27424665589516973720597209 20568499192137730290447907)
              ·
                refine ⟨30852748788206595435671861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20568499192137730290447907 30852748788206595435671861)
                ·
                  refine ⟨2892445198894368322094237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30852748788206595435671861 2892445198894368322094237)
                  ·
                    refine ⟨1084666949585388120785339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892445198894368322094237 1084666949585388120785339)
                    ·
                      rfl

theorem cell22_3168572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_3168572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168572 prefixEnd_3168572 := by exact prefixLift 3168572
  have htrace : WordTrace (prefixWord ++ tailWord_3168572) baseStart_3168572 baseEnd_3168572 := by
    simpa [prefixWord, tailWord_3168572, baseEnd_3168572] using wordTrace_append hprefix tailTrace_3168572
  have hstable : (prefixWord ++ tailWord_3168572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168572).length < 2 ^ (prefixWord ++ tailWord_3168572).sum := by decide
  have hdescent : baseEnd_3168572 < baseStart_3168572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168649 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_3168649 : Nat := 118140960795 + 3168649 * 2 ^ 59
def prefixEnd_3168649 : Nat := 4983230072969 + 3 ^ 40 * 3168649 * 2
def baseEnd_3168649 : Nat := 1084693308258985586610103

theorem tailTrace_3168649 : CollatzResearch.WordTrace tailWord_3168649 prefixEnd_3168649 1084693308258985586610103 := by
  unfold tailWord_3168649
  simp only [CollatzResearch.WordTrace]
  refine ⟨115570123497533310010189001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77046748998355540006792667 115570123497533310010189001)
  ·
    refine ⟨86677592623149982507641751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115570123497533310010189001 86677592623149982507641751)
    ·
      refine ⟨130016388934724973761462627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86677592623149982507641751 130016388934724973761462627)
      ·
        refine ⟨195024583402087460642193941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130016388934724973761462627 195024583402087460642193941)
        ·
          refine ⟨9141777346972849717602841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195024583402087460642193941 9141777346972849717602841)
          ·
            refine ⟨6856333010229637288202131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9141777346972849717602841 6856333010229637288202131)
            ·
              refine ⟨10284499515344455932303197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6856333010229637288202131 10284499515344455932303197)
              ·
                refine ⟨3856687318254170974613699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10284499515344455932303197 3856687318254170974613699)
                ·
                  refine ⟨5785030977381256461920549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856687318254170974613699 5785030977381256461920549)
                  ·
                    refine ⟨1084693308258985586610103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5785030977381256461920549 1084693308258985586610103)
                    ·
                      rfl

theorem cell22_3168649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_3168649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168649 prefixEnd_3168649 := by exact prefixLift 3168649
  have htrace : WordTrace (prefixWord ++ tailWord_3168649) baseStart_3168649 baseEnd_3168649 := by
    simpa [prefixWord, tailWord_3168649, baseEnd_3168649] using wordTrace_append hprefix tailTrace_3168649
  have hstable : (prefixWord ++ tailWord_3168649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168649).length < 2 ^ (prefixWord ++ tailWord_3168649).sum := by decide
  have hdescent : baseEnd_3168649 < baseStart_3168649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168664 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_3168664 : Nat := 118140960795 + 3168664 * 2 ^ 59
def prefixEnd_3168664 : Nat := 4983230072969 + 3 ^ 40 * 3168664 * 2
def baseEnd_3168664 : Nat := 361566147688510182495019

theorem tailTrace_3168664 : CollatzResearch.WordTrace tailWord_3168664 prefixEnd_3168664 361566147688510182495019 := by
  unfold tailWord_3168664
  simp only [CollatzResearch.WordTrace]
  refine ⟨57785335296239483785992523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77047113728319311714656697 57785335296239483785992523)
  ·
    refine ⟨86678002944359225678988785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57785335296239483785992523 86678002944359225678988785)
    ·
      refine ⟨65008502208269419259241589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86678002944359225678988785 65008502208269419259241589)
      ·
        refine ⟨6094547082025258055553899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65008502208269419259241589 6094547082025258055553899)
        ·
          refine ⟨9141820623037887083330849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094547082025258055553899 9141820623037887083330849)
          ·
            refine ⟨6856365467278415312498137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9141820623037887083330849 6856365467278415312498137)
            ·
              refine ⟨5142274100458811484373603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6856365467278415312498137 5142274100458811484373603)
              ·
                refine ⟨7713411150688217226560405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142274100458811484373603 7713411150688217226560405)
                ·
                  refine ⟨361566147688510182495019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7713411150688217226560405 361566147688510182495019)
                  ·
                    rfl

theorem cell22_3168664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_3168664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168664 prefixEnd_3168664 := by exact prefixLift 3168664
  have htrace : WordTrace (prefixWord ++ tailWord_3168664) baseStart_3168664 baseEnd_3168664 := by
    simpa [prefixWord, tailWord_3168664, baseEnd_3168664] using wordTrace_append hprefix tailTrace_3168664
  have hstable : (prefixWord ++ tailWord_3168664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168664).length < 2 ^ (prefixWord ++ tailWord_3168664).sum := by decide
  have hdescent : baseEnd_3168664 < baseStart_3168664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168679 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3168679 : Nat := 118140960795 + 3168679 * 2 ^ 59
def prefixEnd_3168679 : Nat := 4983230072969 + 3 ^ 40 * 3168679 * 2
def baseEnd_3168679 : Nat := 1084703577872075508360011

theorem tailTrace_3168679 : CollatzResearch.WordTrace tailWord_3168679 prefixEnd_3168679 1084703577872075508360011 := by
  unfold tailWord_3168679
  simp only [CollatzResearch.WordTrace]
  refine ⟨115571217687424625133781091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77047478458283083422520727 115571217687424625133781091)
  ·
    refine ⟨173356826531136937700671637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115571217687424625133781091 173356826531136937700671637)
    ·
      refine ⟨8126101243647043954718983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173356826531136937700671637 8126101243647043954718983)
      ·
        refine ⟨12189151865470565932078475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126101243647043954718983 12189151865470565932078475)
        ·
          refine ⟨18283727798205848898117713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189151865470565932078475 18283727798205848898117713)
          ·
            refine ⟨13712795848654386673588285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18283727798205848898117713 13712795848654386673588285)
            ·
              refine ⟨5142298443245395002595607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13712795848654386673588285 5142298443245395002595607)
              ·
                refine ⟨7713447664868092503893411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142298443245395002595607 7713447664868092503893411)
                ·
                  refine ⟨11570171497302138755840117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7713447664868092503893411 11570171497302138755840117)
                  ·
                    refine ⟨1084703577872075508360011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11570171497302138755840117 1084703577872075508360011)
                    ·
                      rfl

theorem cell22_3168679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3168679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168679 prefixEnd_3168679 := by exact prefixLift 3168679
  have htrace : WordTrace (prefixWord ++ tailWord_3168679) baseStart_3168679 baseEnd_3168679 := by
    simpa [prefixWord, tailWord_3168679, baseEnd_3168679] using wordTrace_append hprefix tailTrace_3168679
  have hstable : (prefixWord ++ tailWord_3168679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168679).length < 2 ^ (prefixWord ++ tailWord_3168679).sum := by decide
  have hdescent : baseEnd_3168679 < baseStart_3168679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168758 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3168758 : Nat := 118140960795 + 3168758 * 2 ^ 59
def prefixEnd_3168758 : Nat := 4983230072969 + 3 ^ 40 * 3168758 * 2
def baseEnd_3168758 : Nat := 1084730621186545635634769

theorem tailTrace_3168758 : CollatzResearch.WordTrace tailWord_3168758 prefixEnd_3168758 1084730621186545635634769 := by
  unfold tailWord_3168758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7223381190883651351619183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77049399369425614417271285 7223381190883651351619183)
  ·
    refine ⟨10835071786325477027428775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7223381190883651351619183 10835071786325477027428775)
    ·
      refine ⟨16252607679488215541143163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10835071786325477027428775 16252607679488215541143163)
      ·
        refine ⟨24378911519232323311714745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16252607679488215541143163 24378911519232323311714745)
        ·
          refine ⟨18284183639424242483786059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24378911519232323311714745 18284183639424242483786059)
          ·
            refine ⟨27426275459136363725679089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18284183639424242483786059 27426275459136363725679089)
            ·
              refine ⟨20569706594352272794259317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27426275459136363725679089 20569706594352272794259317)
              ·
                refine ⟨1928409993220525574461811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20569706594352272794259317 1928409993220525574461811)
                ·
                  refine ⟨2892614989830788361692717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928409993220525574461811 2892614989830788361692717)
                  ·
                    refine ⟨1084730621186545635634769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892614989830788361692717 1084730621186545635634769)
                    ·
                      rfl

theorem cell22_3168758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3168758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168758 prefixEnd_3168758 := by exact prefixLift 3168758
  have htrace : WordTrace (prefixWord ++ tailWord_3168758) baseStart_3168758 baseEnd_3168758 := by
    simpa [prefixWord, tailWord_3168758, baseEnd_3168758] using wordTrace_append hprefix tailTrace_3168758
  have hstable : (prefixWord ++ tailWord_3168758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168758).length < 2 ^ (prefixWord ++ tailWord_3168758).sum := by decide
  have hdescent : baseEnd_3168758 < baseStart_3168758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168889 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 7]
def baseStart_3168889 : Nat := 118140960795 + 3168889 * 2 ^ 59
def prefixEnd_3168889 : Nat := 4983230072969 + 3 ^ 40 * 3168889 * 2
def baseEnd_3168889 : Nat := 361591821721234986869789

theorem tailTrace_3168889 : CollatzResearch.WordTrace tailWord_3168889 prefixEnd_3168889 361591821721234986869789 := by
  unfold tailWord_3168889
  simp only [CollatzResearch.WordTrace]
  refine ⟨115578877016663830998925721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77052584677775887332617147 115578877016663830998925721)
  ·
    refine ⟨86684157762497873249194291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115578877016663830998925721 86684157762497873249194291)
    ·
      refine ⟨130026236643746809873791437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86684157762497873249194291 130026236643746809873791437)
      ·
        refine ⟨48759838741405053702671789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130026236643746809873791437 48759838741405053702671789)
        ·
          refine ⟨18284939528026895138501921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48759838741405053702671789 18284939528026895138501921)
          ·
            refine ⟨13713704646020171353876441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18284939528026895138501921 13713704646020171353876441)
            ·
              refine ⟨10285278484515128515407331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13713704646020171353876441 10285278484515128515407331)
              ·
                refine ⟨15427917726772692773110997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10285278484515128515407331 15427917726772692773110997)
                ·
                  refine ⟨361591821721234986869789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15427917726772692773110997 361591821721234986869789)
                  ·
                    rfl

theorem cell22_3168889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_3168889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3168889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3168889 prefixEnd_3168889 := by exact prefixLift 3168889
  have htrace : WordTrace (prefixWord ++ tailWord_3168889) baseStart_3168889 baseEnd_3168889 := by
    simpa [prefixWord, tailWord_3168889, baseEnd_3168889] using wordTrace_append hprefix tailTrace_3168889
  have hstable : (prefixWord ++ tailWord_3168889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168889).length < 2 ^ (prefixWord ++ tailWord_3168889).sum := by decide
  have hdescent : baseEnd_3168889 < baseStart_3168889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169024 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_3169024 : Nat := 118140960795 + 3169024 * 2 ^ 59
def prefixEnd_3169024 : Nat := 4983230072969 + 3 ^ 40 * 3169024 * 2
def baseEnd_3169024 : Nat := 361607226140869869494651

theorem tailTrace_3169024 : CollatzResearch.WordTrace tailWord_3169024 prefixEnd_3169024 361607226140869869494651 := by
  unfold tailWord_3169024
  simp only [CollatzResearch.WordTrace]
  refine ⟨57791900435587374527545063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77055867247449832703393417 57791900435587374527545063)
  ·
    refine ⟨86687850653381061791317595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57791900435587374527545063 86687850653381061791317595)
    ·
      refine ⟨130031775980071592686976393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86687850653381061791317595 130031775980071592686976393)
      ·
        refine ⟨97523831985053694515232295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130031775980071592686976393 97523831985053694515232295)
        ·
          refine ⟨146285747977580541772848443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97523831985053694515232295 146285747977580541772848443)
          ·
            refine ⟨219428621966370812659272665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146285747977580541772848443 219428621966370812659272665)
            ·
              refine ⟨164571466474778109494454499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219428621966370812659272665 164571466474778109494454499)
              ·
                refine ⟨246857199712167164241681749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164571466474778109494454499 246857199712167164241681749)
                ·
                  refine ⟨361607226140869869494651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 246857199712167164241681749 361607226140869869494651)
                  ·
                    rfl

theorem cell22_3169024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_3169024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169024 prefixEnd_3169024 := by exact prefixLift 3169024
  have htrace : WordTrace (prefixWord ++ tailWord_3169024) baseStart_3169024 baseEnd_3169024 := by
    simpa [prefixWord, tailWord_3169024, baseEnd_3169024] using wordTrace_append hprefix tailTrace_3169024
  have hstable : (prefixWord ++ tailWord_3169024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169024).length < 2 ^ (prefixWord ++ tailWord_3169024).sum := by decide
  have hdescent : baseEnd_3169024 < baseStart_3169024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169028 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_3169028 : Nat := 118140960795 + 3169028 * 2 ^ 59
def prefixEnd_3169028 : Nat := 4983230072969 + 3 ^ 40 * 3169028 * 2
def baseEnd_3169028 : Nat := 1084823047704354931383941

theorem tailTrace_3169028 : CollatzResearch.WordTrace tailWord_3169028 prefixEnd_3169028 1084823047704354931383941 := by
  unfold tailWord_3169028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57791973381580128869117869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77055964508773505158823825 57791973381580128869117869)
  ·
    refine ⟨21671990018092548325919201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57791973381580128869117869 21671990018092548325919201)
    ·
      refine ⟨16253992513569411244439401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21671990018092548325919201 16253992513569411244439401)
      ·
        refine ⟨12190494385177058433329551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16253992513569411244439401 12190494385177058433329551)
        ·
          refine ⟨18285741577765587649994327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12190494385177058433329551 18285741577765587649994327)
          ·
            refine ⟨27428612366648381474991491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18285741577765587649994327 27428612366648381474991491)
            ·
              refine ⟨41142918549972572212487237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27428612366648381474991491 41142918549972572212487237)
              ·
                refine ⟨7714297228119857289841357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41142918549972572212487237 7714297228119857289841357)
                ·
                  refine ⟨2892861460544946483690509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7714297228119857289841357 2892861460544946483690509)
                  ·
                    refine ⟨1084823047704354931383941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892861460544946483690509 1084823047704354931383941)
                    ·
                      rfl

theorem cell22_3169028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_3169028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169028 prefixEnd_3169028 := by exact prefixLift 3169028
  have htrace : WordTrace (prefixWord ++ tailWord_3169028) baseStart_3169028 baseEnd_3169028 := by
    simpa [prefixWord, tailWord_3169028, baseEnd_3169028] using wordTrace_append hprefix tailTrace_3169028
  have hstable : (prefixWord ++ tailWord_3169028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169028).length < 2 ^ (prefixWord ++ tailWord_3169028).sum := by decide
  have hdescent : baseEnd_3169028 < baseStart_3169028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169075 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 5]
def baseStart_3169075 : Nat := 118140960795 + 3169075 * 2 ^ 59
def prefixEnd_3169075 : Nat := 4983230072969 + 3 ^ 40 * 3169075 * 2
def baseEnd_3169075 : Nat := 361613045588287491819599

theorem tailTrace_3169075 : CollatzResearch.WordTrace tailWord_3169075 prefixEnd_3169075 361613045588287491819599 := by
  unfold tailWord_3169075
  simp only [CollatzResearch.WordTrace]
  refine ⟨115585660993989984765196679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77057107329326656510131119 115585660993989984765196679)
  ·
    refine ⟨173378491490984977147795019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115585660993989984765196679 173378491490984977147795019)
    ·
      refine ⟨260067737236477465721692529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173378491490984977147795019 260067737236477465721692529)
      ·
        refine ⟨195050802927358099291269397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260067737236477465721692529 195050802927358099291269397)
        ·
          refine ⟨9143006387219910904278253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195050802927358099291269397 9143006387219910904278253)
          ·
            refine ⟨3428627395207466589104345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9143006387219910904278253 3428627395207466589104345)
            ·
              refine ⟨2571470546405599941828259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428627395207466589104345 2571470546405599941828259)
              ·
                refine ⟨3857205819608399912742389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571470546405599941828259 3857205819608399912742389)
                ·
                  refine ⟨361613045588287491819599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3857205819608399912742389 361613045588287491819599)
                  ·
                    rfl

theorem cell22_3169075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 5].length) (baseStart_3169075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169075 prefixEnd_3169075 := by exact prefixLift 3169075
  have htrace : WordTrace (prefixWord ++ tailWord_3169075) baseStart_3169075 baseEnd_3169075 := by
    simpa [prefixWord, tailWord_3169075, baseEnd_3169075] using wordTrace_append hprefix tailTrace_3169075
  have hstable : (prefixWord ++ tailWord_3169075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169075).length < 2 ^ (prefixWord ++ tailWord_3169075).sum := by decide
  have hdescent : baseEnd_3169075 < baseStart_3169075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169131 : List Nat := [1, 1, 1, 1, 2, 2, 7, 7]
def baseStart_3169131 : Nat := 118140960795 + 3169131 * 2 ^ 59
def prefixEnd_3169131 : Nat := 4983230072969 + 3 ^ 40 * 3169131 * 2
def baseEnd_3169131 : Nat := 120539811856588555117625

theorem tailTrace_3169131 : CollatzResearch.WordTrace tailWord_3169131 prefixEnd_3169131 120539811856588555117625 := by
  unfold tailWord_3169131
  simp only [CollatzResearch.WordTrace]
  refine ⟨115587703481787106329235247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77058468987858070886156831 115587703481787106329235247)
  ·
    refine ⟨173381555222680659493852871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115587703481787106329235247 173381555222680659493852871)
    ·
      refine ⟨260072332834020989240779307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173381555222680659493852871 260072332834020989240779307)
      ·
        refine ⟨390108499251031483861168961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260072332834020989240779307 390108499251031483861168961)
        ·
          refine ⟨292581374438273612895876721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390108499251031483861168961 292581374438273612895876721)
          ·
            refine ⟨219436030828705209671907541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292581374438273612895876721 219436030828705209671907541)
            ·
              refine ⟨5143031972547778351685333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 219436030828705209671907541 5143031972547778351685333)
              ·
                refine ⟨120539811856588555117625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5143031972547778351685333 120539811856588555117625)
                ·
                  rfl

theorem cell22_3169131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 7].length) (baseStart_3169131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169131 prefixEnd_3169131 := by exact prefixLift 3169131
  have htrace : WordTrace (prefixWord ++ tailWord_3169131) baseStart_3169131 baseEnd_3169131 := by
    simpa [prefixWord, tailWord_3169131, baseEnd_3169131] using wordTrace_append hprefix tailTrace_3169131
  have hstable : (prefixWord ++ tailWord_3169131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169131).length < 2 ^ (prefixWord ++ tailWord_3169131).sum := by decide
  have hdescent : baseEnd_3169131 < baseStart_3169131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169270 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3169270 : Nat := 118140960795 + 3169270 * 2 ^ 59
def prefixEnd_3169270 : Nat := 4983230072969 + 3 ^ 40 * 3169270 * 2
def baseEnd_3169270 : Nat := 1084905889249946966833199

theorem tailTrace_3169270 : CollatzResearch.WordTrace tailWord_3169270 prefixEnd_3169270 1084905889249946966833199 := by
  unfold tailWord_3169270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224548326767720816784079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77061848818855688712363509 7224548326767720816784079)
  ·
    refine ⟨10836822490151581225176119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7224548326767720816784079 10836822490151581225176119)
    ·
      refine ⟨16255233735227371837764179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10836822490151581225176119 16255233735227371837764179)
      ·
        refine ⟨24382850602841057756646269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16255233735227371837764179 24382850602841057756646269)
        ·
          refine ⟨9143568976065396658742351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24382850602841057756646269 9143568976065396658742351)
          ·
            refine ⟨13715353464098094988113527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9143568976065396658742351 13715353464098094988113527)
            ·
              refine ⟨20573030196147142482170291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13715353464098094988113527 20573030196147142482170291)
              ·
                refine ⟨30859545294220713723255437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20573030196147142482170291 30859545294220713723255437)
                ·
                  refine ⟨11572329485332767646220789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30859545294220713723255437 11572329485332767646220789)
                  ·
                    refine ⟨1084905889249946966833199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11572329485332767646220789 1084905889249946966833199)
                    ·
                      rfl

theorem cell22_3169270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3169270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169270 prefixEnd_3169270 := by exact prefixLift 3169270
  have htrace : WordTrace (prefixWord ++ tailWord_3169270) baseStart_3169270 baseEnd_3169270 := by
    simpa [prefixWord, tailWord_3169270, baseEnd_3169270] using wordTrace_append hprefix tailTrace_3169270
  have hstable : (prefixWord ++ tailWord_3169270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169270).length < 2 ^ (prefixWord ++ tailWord_3169270).sum := by decide
  have hdescent : baseEnd_3169270 < baseStart_3169270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169287 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 2, 3]
def baseStart_3169287 : Nat := 118140960795 + 3169287 * 2 ^ 59
def prefixEnd_3169287 : Nat := 4983230072969 + 3 ^ 40 * 3169287 * 2
def baseEnd_3169287 : Nat := 1084911708697364589158147

theorem tailTrace_3169287 : CollatzResearch.WordTrace tailWord_3169287 prefixEnd_3169287 1084911708697364589158147 := by
  unfold tailWord_3169287
  simp only [CollatzResearch.WordTrace]
  refine ⟨115593393269221944971914115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77062262179481296647942743 115593393269221944971914115)
  ·
    refine ⟨173390089903832917457871173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115593393269221944971914115 173390089903832917457871173)
    ·
      refine ⟨32510641856968672023350845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173390089903832917457871173 32510641856968672023350845)
      ·
        refine ⟨12191490696363252008756567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32510641856968672023350845 12191490696363252008756567)
        ·
          refine ⟨18287236044544878013134851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12191490696363252008756567 18287236044544878013134851)
          ·
            refine ⟨27430854066817317019702277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18287236044544878013134851 27430854066817317019702277)
            ·
              refine ⟨5143285137528246941194177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27430854066817317019702277 5143285137528246941194177)
              ·
                refine ⟨3857463853146185205895633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143285137528246941194177 3857463853146185205895633)
                ·
                  refine ⟨2893097889859638904421725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3857463853146185205895633 2893097889859638904421725)
                  ·
                    refine ⟨1084911708697364589158147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893097889859638904421725 1084911708697364589158147)
                    ·
                      rfl

theorem cell22_3169287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_3169287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169287 prefixEnd_3169287 := by exact prefixLift 3169287
  have htrace : WordTrace (prefixWord ++ tailWord_3169287) baseStart_3169287 baseEnd_3169287 := by
    simpa [prefixWord, tailWord_3169287, baseEnd_3169287] using wordTrace_append hprefix tailTrace_3169287
  have hstable : (prefixWord ++ tailWord_3169287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169287).length < 2 ^ (prefixWord ++ tailWord_3169287).sum := by decide
  have hdescent : baseEnd_3169287 < baseStart_3169287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169315 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 5, 3]
def baseStart_3169315 : Nat := 118140960795 + 3169315 * 2 ^ 59
def prefixEnd_3169315 : Nat := 4983230072969 + 3 ^ 40 * 3169315 * 2
def baseEnd_3169315 : Nat := 1084921293669581849458061

theorem tailTrace_3169315 : CollatzResearch.WordTrace tailWord_3169315 prefixEnd_3169315 1084921293669581849458061 := by
  unfold tailWord_3169315
  simp only [CollatzResearch.WordTrace]
  refine ⟨115594414513120505753933399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77062943008747003835955599 115594414513120505753933399)
  ·
    refine ⟨173391621769680758630900099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115594414513120505753933399 173391621769680758630900099)
    ·
      refine ⟨260087432654521137946350149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173391621769680758630900099 260087432654521137946350149)
      ·
        refine ⟨48766393622722713364940653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260087432654521137946350149 48766393622722713364940653)
        ·
          refine ⟨18287397608521017511852745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48766393622722713364940653 18287397608521017511852745)
          ·
            refine ⟨13715548206390763133889559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18287397608521017511852745 13715548206390763133889559)
            ·
              refine ⟨20573322309586144700834339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13715548206390763133889559 20573322309586144700834339)
              ·
                refine ⟨30859983464379217051251509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20573322309586144700834339 30859983464379217051251509)
                ·
                  refine ⟨2893123449785551598554829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30859983464379217051251509 2893123449785551598554829)
                  ·
                    refine ⟨1084921293669581849458061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893123449785551598554829 1084921293669581849458061)
                    ·
                      rfl

theorem cell22_3169315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 3].length) (baseStart_3169315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169315 prefixEnd_3169315 := by exact prefixLift 3169315
  have htrace : WordTrace (prefixWord ++ tailWord_3169315) baseStart_3169315 baseEnd_3169315 := by
    simpa [prefixWord, tailWord_3169315, baseEnd_3169315] using wordTrace_append hprefix tailTrace_3169315
  have hstable : (prefixWord ++ tailWord_3169315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169315).length < 2 ^ (prefixWord ++ tailWord_3169315).sum := by decide
  have hdescent : baseEnd_3169315 < baseStart_3169315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169319 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3169319 : Nat := 118140960795 + 3169319 * 2 ^ 59
def prefixEnd_3169319 : Nat := 4983230072969 + 3 ^ 40 * 3169319 * 2
def baseEnd_3169319 : Nat := 1084922662951327172358049

theorem tailTrace_3169319 : CollatzResearch.WordTrace tailWord_3169319 prefixEnd_3169319 1084922662951327172358049 := by
  unfold tailWord_3169319
  simp only [CollatzResearch.WordTrace]
  refine ⟨115594560405106014437079011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77063040270070676291386007 115594560405106014437079011)
  ·
    refine ⟨173391840607659021655618517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115594560405106014437079011 173391840607659021655618517)
    ·
      refine ⟨4063871264242008320053559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 173391840607659021655618517 4063871264242008320053559)
      ·
        refine ⟨6095806896363012480080339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063871264242008320053559 6095806896363012480080339)
        ·
          refine ⟨9143710344544518720120509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6095806896363012480080339 9143710344544518720120509)
          ·
            refine ⟨3428891379204194520045191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9143710344544518720120509 3428891379204194520045191)
            ·
              refine ⟨5143337068806291780067787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428891379204194520045191 5143337068806291780067787)
              ·
                refine ⟨7715005603209437670101681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143337068806291780067787 7715005603209437670101681)
                ·
                  refine ⟨5786254202407078252576261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7715005603209437670101681 5786254202407078252576261)
                  ·
                    refine ⟨1084922662951327172358049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5786254202407078252576261 1084922662951327172358049)
                    ·
                      rfl

theorem cell22_3169319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3169319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169319 prefixEnd_3169319 := by exact prefixLift 3169319
  have htrace : WordTrace (prefixWord ++ tailWord_3169319) baseStart_3169319 baseEnd_3169319 := by
    simpa [prefixWord, tailWord_3169319, baseEnd_3169319] using wordTrace_append hprefix tailTrace_3169319
  have hstable : (prefixWord ++ tailWord_3169319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169319).length < 2 ^ (prefixWord ++ tailWord_3169319).sum := by decide
  have hdescent : baseEnd_3169319 < baseStart_3169319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169328 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_3169328 : Nat := 118140960795 + 3169328 * 2 ^ 59
def prefixEnd_3169328 : Nat := 4983230072969 + 3 ^ 40 * 3169328 * 2
def baseEnd_3169328 : Nat := 361641914611751382961007

theorem tailTrace_3169328 : CollatzResearch.WordTrace tailWord_3169328 prefixEnd_3169328 361641914611751382961007 := by
  unfold tailWord_3169328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57797444331036704487078319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77063259108048939316104425 57797444331036704487078319)
  ·
    refine ⟨86696166496555056730617479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57797444331036704487078319 86696166496555056730617479)
    ·
      refine ⟨130044249744832585095926219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86696166496555056730617479 130044249744832585095926219)
      ·
        refine ⟨195066374617248877643889329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130044249744832585095926219 195066374617248877643889329)
        ·
          refine ⟨146299780962936658232916997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195066374617248877643889329 146299780962936658232916997)
          ·
            refine ⟨27431208930550623418671937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146299780962936658232916997 27431208930550623418671937)
            ·
              refine ⟨20573406697912967564003953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27431208930550623418671937 20573406697912967564003953)
              ·
                refine ⟨15430055023434725673002965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20573406697912967564003953 15430055023434725673002965)
                ·
                  refine ⟨361641914611751382961007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15430055023434725673002965 361641914611751382961007)
                  ·
                    rfl

theorem cell22_3169328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_3169328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169328 prefixEnd_3169328 := by exact prefixLift 3169328
  have htrace : WordTrace (prefixWord ++ tailWord_3169328) baseStart_3169328 baseEnd_3169328 := by
    simpa [prefixWord, tailWord_3169328, baseEnd_3169328] using wordTrace_append hprefix tailTrace_3169328
  have hstable : (prefixWord ++ tailWord_3169328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169328).length < 2 ^ (prefixWord ++ tailWord_3169328).sum := by decide
  have hdescent : baseEnd_3169328 < baseStart_3169328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169437 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3169437 : Nat := 118140960795 + 3169437 * 2 ^ 59
def prefixEnd_3169437 : Nat := 4983230072969 + 3 ^ 40 * 3169437 * 2
def baseEnd_3169437 : Nat := 1084963056762814197907687

theorem tailTrace_3169437 : CollatzResearch.WordTrace tailWord_3169437 prefixEnd_3169437 1084963056762814197907687 := by
  unfold tailWord_3169437
  simp only [CollatzResearch.WordTrace]
  refine ⟨115598864218678520589874565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77065909479119013726583043 115598864218678520589874565)
  ·
    refine ⟨21674787041002222610601481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115598864218678520589874565 21674787041002222610601481)
    ·
      refine ⟨16256090280751666957951111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21674787041002222610601481 16256090280751666957951111)
      ·
        refine ⟨24384135421127500436926667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16256090280751666957951111 24384135421127500436926667)
        ·
          refine ⟨36576203131691250655390001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24384135421127500436926667 36576203131691250655390001)
          ·
            refine ⟨27432152348768437991542501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36576203131691250655390001 27432152348768437991542501)
            ·
              refine ⟨5143528565394082123414219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27432152348768437991542501 5143528565394082123414219)
              ·
                refine ⟨7715292848091123185121329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143528565394082123414219 7715292848091123185121329)
                ·
                  refine ⟨5786469636068342388840997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7715292848091123185121329 5786469636068342388840997)
                  ·
                    refine ⟨1084963056762814197907687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5786469636068342388840997 1084963056762814197907687)
                    ·
                      rfl

theorem cell22_3169437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3169437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169437 prefixEnd_3169437 := by exact prefixLift 3169437
  have htrace : WordTrace (prefixWord ++ tailWord_3169437) baseStart_3169437 baseEnd_3169437 := by
    simpa [prefixWord, tailWord_3169437, baseEnd_3169437] using wordTrace_append hprefix tailTrace_3169437
  have hstable : (prefixWord ++ tailWord_3169437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169437).length < 2 ^ (prefixWord ++ tailWord_3169437).sum := by decide
  have hdescent : baseEnd_3169437 < baseStart_3169437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169465 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_3169465 : Nat := 118140960795 + 3169465 * 2 ^ 59
def prefixEnd_3169465 : Nat := 4983230072969 + 3 ^ 40 * 3169465 * 2
def baseEnd_3169465 : Nat := 1084972641735031458207601

theorem tailTrace_3169465 : CollatzResearch.WordTrace tailWord_3169465 prefixEnd_3169465 1084972641735031458207601 := by
  unfold tailWord_3169465
  simp only [CollatzResearch.WordTrace]
  refine ⟨115599885462577081371893849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77066590308384720914595899 115599885462577081371893849)
  ·
    refine ⟨86699914096932811028920387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115599885462577081371893849 86699914096932811028920387)
    ·
      refine ⟨130049871145399216543380581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86699914096932811028920387 130049871145399216543380581)
      ·
        refine ⟨24384350839762353101883859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130049871145399216543380581 24384350839762353101883859)
        ·
          refine ⟨36576526259643529652825789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24384350839762353101883859 36576526259643529652825789)
          ·
            refine ⟨13716197347366323619809671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36576526259643529652825789 13716197347366323619809671)
            ·
              refine ⟨20574296021049485429714507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13716197347366323619809671 20574296021049485429714507)
              ·
                refine ⟨30861444031574228144571761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20574296021049485429714507 30861444031574228144571761)
                ·
                  refine ⟨23146083023680671108428821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30861444031574228144571761 23146083023680671108428821)
                  ·
                    refine ⟨1084972641735031458207601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23146083023680671108428821 1084972641735031458207601)
                    ·
                      rfl

theorem cell22_3169465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_3169465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169465 prefixEnd_3169465 := by exact prefixLift 3169465
  have htrace : WordTrace (prefixWord ++ tailWord_3169465) baseStart_3169465 baseEnd_3169465 := by
    simpa [prefixWord, tailWord_3169465, baseEnd_3169465] using wordTrace_append hprefix tailTrace_3169465
  have hstable : (prefixWord ++ tailWord_3169465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169465).length < 2 ^ (prefixWord ++ tailWord_3169465).sum := by decide
  have hdescent : baseEnd_3169465 < baseStart_3169465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169514 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_3169514 : Nat := 118140960795 + 3169514 * 2 ^ 59
def prefixEnd_3169514 : Nat := 4983230072969 + 3 ^ 40 * 3169514 * 2
def baseEnd_3169514 : Nat := 361663138478803887910817

theorem tailTrace_3169514 : CollatzResearch.WordTrace tailWord_3169514 prefixEnd_3169514 361663138478803887910817 := by
  unfold tailWord_3169514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28900418159849890685106899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77067781759599708493618397 28900418159849890685106899)
  ·
    refine ⟨43350627239774836027660349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28900418159849890685106899 43350627239774836027660349)
    ·
      refine ⟨16256485214915563510372631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43350627239774836027660349 16256485214915563510372631)
      ·
        refine ⟨24384727822373345265558947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16256485214915563510372631 24384727822373345265558947)
        ·
          refine ⟨36577091733560017898338421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24384727822373345265558947 36577091733560017898338421)
          ·
            refine ⟨3429102350021251677969227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36577091733560017898338421 3429102350021251677969227)
            ·
              refine ⟨5143653525031877516953841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429102350021251677969227 5143653525031877516953841)
              ·
                refine ⟨3857740143773908137715381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143653525031877516953841 3857740143773908137715381)
                ·
                  refine ⟨361663138478803887910817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3857740143773908137715381 361663138478803887910817)
                  ·
                    rfl

theorem cell22_3169514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_3169514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169514 prefixEnd_3169514 := by exact prefixLift 3169514
  have htrace : WordTrace (prefixWord ++ tailWord_3169514) baseStart_3169514 baseEnd_3169514 := by
    simpa [prefixWord, tailWord_3169514, baseEnd_3169514] using wordTrace_append hprefix tailTrace_3169514
  have hstable : (prefixWord ++ tailWord_3169514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169514).length < 2 ^ (prefixWord ++ tailWord_3169514).sum := by decide
  have hdescent : baseEnd_3169514 < baseStart_3169514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169587 : List Nat := [1, 1, 1, 2, 5, 3, 2, 7]
def baseStart_3169587 : Nat := 118140960795 + 3169587 * 2 ^ 59
def prefixEnd_3169587 : Nat := 4983230072969 + 3 ^ 40 * 3169587 * 2
def baseEnd_3169587 : Nat := 120557156092029311850803

theorem tailTrace_3169587 : CollatzResearch.WordTrace tailWord_3169587 prefixEnd_3169587 120557156092029311850803 := by
  unfold tailWord_3169587
  simp only [CollatzResearch.WordTrace]
  refine ⟨115604335168135096207835015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77069556778756730805223343 115604335168135096207835015)
  ·
    refine ⟨173406502752202644311752523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115604335168135096207835015 173406502752202644311752523)
    ·
      refine ⟨260109754128303966467628785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173406502752202644311752523 260109754128303966467628785)
      ·
        refine ⟨195082315596227974850721589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260109754128303966467628785 195082315596227974850721589)
        ·
          refine ⟨18288967087146372642255149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195082315596227974850721589 18288967087146372642255149)
          ·
            refine ⟨6858362657679889740845681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18288967087146372642255149 6858362657679889740845681)
            ·
              refine ⟨5143771993259917305634261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6858362657679889740845681 5143771993259917305634261)
              ·
                refine ⟨120557156092029311850803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5143771993259917305634261 120557156092029311850803)
                ·
                  rfl

theorem cell22_3169587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 7].length) (baseStart_3169587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169587 prefixEnd_3169587 := by exact prefixLift 3169587
  have htrace : WordTrace (prefixWord ++ tailWord_3169587) baseStart_3169587 baseEnd_3169587 := by
    simpa [prefixWord, tailWord_3169587, baseEnd_3169587] using wordTrace_append hprefix tailTrace_3169587
  have hstable : (prefixWord ++ tailWord_3169587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169587).length < 2 ^ (prefixWord ++ tailWord_3169587).sum := by decide
  have hdescent : baseEnd_3169587 < baseStart_3169587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169604 : List Nat := [2, 3, 4, 1, 1, 1, 2, 8]
def baseStart_3169604 : Nat := 118140960795 + 3169604 * 2 ^ 59
def prefixEnd_3169604 : Nat := 4983230072969 + 3 ^ 40 * 3169604 * 2
def baseEnd_3169604 : Nat := 120557802697297936553575

theorem tailTrace_3169604 : CollatzResearch.WordTrace tailWord_3169604 prefixEnd_3169604 120557802697297936553575 := by
  unfold tailWord_3169604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57802477604536754055601933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77069970139382338740802577 57802477604536754055601933)
  ·
    refine ⟨21675929101701282770850725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57802477604536754055601933 21675929101701282770850725)
    ·
      refine ⟨4064236706568990519534511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21675929101701282770850725 4064236706568990519534511)
      ·
        refine ⟨6096355059853485779301767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064236706568990519534511 6096355059853485779301767)
        ·
          refine ⟨9144532589780228668952651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6096355059853485779301767 9144532589780228668952651)
          ·
            refine ⟨13716798884670343003428977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9144532589780228668952651 13716798884670343003428977)
            ·
              refine ⟨10287599163502757252571733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13716798884670343003428977 10287599163502757252571733)
              ·
                refine ⟨120557802697297936553575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10287599163502757252571733 120557802697297936553575)
                ·
                  rfl

theorem cell22_3169604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_3169604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169604 prefixEnd_3169604 := by exact prefixLift 3169604
  have htrace : WordTrace (prefixWord ++ tailWord_3169604) baseStart_3169604 baseEnd_3169604 := by
    simpa [prefixWord, tailWord_3169604, baseEnd_3169604] using wordTrace_append hprefix tailTrace_3169604
  have hstable : (prefixWord ++ tailWord_3169604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169604).length < 2 ^ (prefixWord ++ tailWord_3169604).sum := by decide
  have hdescent : baseEnd_3169604 < baseStart_3169604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169647 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 2, 5]
def baseStart_3169647 : Nat := 118140960795 + 3169647 * 2 ^ 59
def prefixEnd_3169647 : Nat := 4983230072969 + 3 ^ 40 * 3169647 * 2
def baseEnd_3169647 : Nat := 1085034944054443650157043

theorem tailTrace_3169647 : CollatzResearch.WordTrace tailWord_3169647 prefixEnd_3169647 1085034944054443650157043 := by
  unfold tailWord_3169647
  simp only [CollatzResearch.WordTrace]
  refine ⟨115606523547917726455019195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77071015698611817636679463 115606523547917726455019195)
  ·
    refine ⟨173409785321876589682528793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115606523547917726455019195 173409785321876589682528793)
    ·
      refine ⟨130057338991407442261896595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173409785321876589682528793 130057338991407442261896595)
      ·
        refine ⟨195086008487111163392844893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130057338991407442261896595 195086008487111163392844893)
        ·
          refine ⟨73157253182666686272316835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195086008487111163392844893 73157253182666686272316835)
          ·
            refine ⟨109735879774000029408475253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73157253182666686272316835 109735879774000029408475253)
            ·
              refine ⟨10287738728812502757044555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109735879774000029408475253 10287738728812502757044555)
              ·
                refine ⟨15431608093218754135566833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10287738728812502757044555 15431608093218754135566833)
                ·
                  refine ⟨11573706069914065601675125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15431608093218754135566833 11573706069914065601675125)
                  ·
                    refine ⟨1085034944054443650157043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11573706069914065601675125 1085034944054443650157043)
                    ·
                      rfl

theorem cell22_3169647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_3169647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169647 prefixEnd_3169647 := by exact prefixLift 3169647
  have htrace : WordTrace (prefixWord ++ tailWord_3169647) baseStart_3169647 baseEnd_3169647 := by
    simpa [prefixWord, tailWord_3169647, baseEnd_3169647] using wordTrace_append hprefix tailTrace_3169647
  have hstable : (prefixWord ++ tailWord_3169647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169647).length < 2 ^ (prefixWord ++ tailWord_3169647).sum := by decide
  have hdescent : baseEnd_3169647 < baseStart_3169647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169816 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_3169816 : Nat := 118140960795 + 3169816 * 2 ^ 59
def prefixEnd_3169816 : Nat := 4983230072969 + 3 ^ 40 * 3169816 * 2
def baseEnd_3169816 : Nat := 1085092796208183542681525

theorem tailTrace_3169816 : CollatzResearch.WordTrace tailWord_3169816 prefixEnd_3169816 1085092796208183542681525 := by
  unfold tailWord_3169816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57806343742152734158960651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77075124989536978878614201 57806343742152734158960651)
  ·
    refine ⟨86709515613229101238440977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57806343742152734158960651 86709515613229101238440977)
    ·
      refine ⟨65032136709921825928830733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86709515613229101238440977 65032136709921825928830733)
      ·
        refine ⟨24387051266220684723311525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65032136709921825928830733 24387051266220684723311525)
        ·
          refine ⟨4572572112416378385620911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24387051266220684723311525 4572572112416378385620911)
          ·
            refine ⟨6858858168624567578431367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4572572112416378385620911 6858858168624567578431367)
            ·
              refine ⟨10288287252936851367647051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6858858168624567578431367 10288287252936851367647051)
              ·
                refine ⟨15432430879405277051470577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10288287252936851367647051 15432430879405277051470577)
                ·
                  refine ⟨11574323159553957788602933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15432430879405277051470577 11574323159553957788602933)
                  ·
                    refine ⟨1085092796208183542681525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11574323159553957788602933 1085092796208183542681525)
                    ·
                      rfl

theorem cell22_3169816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_3169816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169816 prefixEnd_3169816 := by exact prefixLift 3169816
  have htrace : WordTrace (prefixWord ++ tailWord_3169816) baseStart_3169816 baseEnd_3169816 := by
    simpa [prefixWord, tailWord_3169816, baseEnd_3169816] using wordTrace_append hprefix tailTrace_3169816
  have hstable : (prefixWord ++ tailWord_3169816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169816).length < 2 ^ (prefixWord ++ tailWord_3169816).sum := by decide
  have hdescent : baseEnd_3169816 < baseStart_3169816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169848 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 1, 4]
def baseStart_3169848 : Nat := 118140960795 + 3169848 * 2 ^ 59
def prefixEnd_3169848 : Nat := 4983230072969 + 3 ^ 40 * 3169848 * 2
def baseEnd_3169848 : Nat := 1085103750462146125881427

theorem tailTrace_3169848 : CollatzResearch.WordTrace tailWord_3169848 prefixEnd_3169848 1085103750462146125881427 := by
  unfold tailWord_3169848
  simp only [CollatzResearch.WordTrace]
  refine ⟨57806927310094768891543099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77075903080126358522057465 57806927310094768891543099)
  ·
    refine ⟨86710390965142153337314649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57806927310094768891543099 86710390965142153337314649)
    ·
      refine ⟨65032793223856615002985987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86710390965142153337314649 65032793223856615002985987)
      ·
        refine ⟨97549189835784922504478981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65032793223856615002985987 97549189835784922504478981)
        ·
          refine ⟨18290473094209672969589809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97549189835784922504478981 18290473094209672969589809)
          ·
            refine ⟨13717854820657254727192357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18290473094209672969589809 13717854820657254727192357)
            ·
              refine ⟨2572097778873235261348567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13717854820657254727192357 2572097778873235261348567)
              ·
                refine ⟨3858146668309852892022851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572097778873235261348567 3858146668309852892022851)
                ·
                  refine ⟨5787220002464779338034277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858146668309852892022851 5787220002464779338034277)
                  ·
                    refine ⟨1085103750462146125881427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787220002464779338034277 1085103750462146125881427)
                    ·
                      rfl

theorem cell22_3169848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_3169848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169848 prefixEnd_3169848 := by exact prefixLift 3169848
  have htrace : WordTrace (prefixWord ++ tailWord_3169848) baseStart_3169848 baseEnd_3169848 := by
    simpa [prefixWord, tailWord_3169848, baseEnd_3169848] using wordTrace_append hprefix tailTrace_3169848
  have hstable : (prefixWord ++ tailWord_3169848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169848).length < 2 ^ (prefixWord ++ tailWord_3169848).sum := by decide
  have hdescent : baseEnd_3169848 < baseStart_3169848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169861 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_3169861 : Nat := 118140960795 + 3169861 * 2 ^ 59
def prefixEnd_3169861 : Nat := 4983230072969 + 3 ^ 40 * 3169861 * 2
def baseEnd_3169861 : Nat := 1085108200627818425306387

theorem tailTrace_3169861 : CollatzResearch.WordTrace tailWord_3169861 prefixEnd_3169861 1085108200627818425306387 := by
  unfold tailWord_3169861
  simp only [CollatzResearch.WordTrace]
  refine ⟨115614328769142441003309437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77076219179428294002206291 115614328769142441003309437)
  ·
    refine ⟨43355373288428415376241039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115614328769142441003309437 43355373288428415376241039)
    ·
      refine ⟨65033059932642623064361559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43355373288428415376241039 65033059932642623064361559)
      ·
        refine ⟨97549589898963934596542339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65033059932642623064361559 97549589898963934596542339)
        ·
          refine ⟨146324384848445901894813509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97549589898963934596542339 146324384848445901894813509)
          ·
            refine ⟨27435822159083606605277533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146324384848445901894813509 27435822159083606605277533)
            ·
              refine ⟨10288433309656352476979075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27435822159083606605277533 10288433309656352476979075)
              ·
                refine ⟨15432649964484528715468613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10288433309656352476979075 15432649964484528715468613)
                ·
                  refine ⟨2893621868340849134150365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15432649964484528715468613 2893621868340849134150365)
                  ·
                    refine ⟨1085108200627818425306387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893621868340849134150365 1085108200627818425306387)
                    ·
                      rfl

theorem cell22_3169861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_3169861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169861 prefixEnd_3169861 := by exact prefixLift 3169861
  have htrace : WordTrace (prefixWord ++ tailWord_3169861) baseStart_3169861 baseEnd_3169861 := by
    simpa [prefixWord, tailWord_3169861, baseEnd_3169861] using wordTrace_append hprefix tailTrace_3169861
  have hstable : (prefixWord ++ tailWord_3169861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169861).length < 2 ^ (prefixWord ++ tailWord_3169861).sum := by decide
  have hdescent : baseEnd_3169861 < baseStart_3169861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169889 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3169889 : Nat := 118140960795 + 3169889 * 2 ^ 59
def prefixEnd_3169889 : Nat := 4983230072969 + 3 ^ 40 * 3169889 * 2
def baseEnd_3169889 : Nat := 1085117785600035685606301

theorem tailTrace_3169889 : CollatzResearch.WordTrace tailWord_3169889 prefixEnd_3169889 1085117785600035685606301 := by
  unfold tailWord_3169889
  simp only [CollatzResearch.WordTrace]
  refine ⟨115615350013041001785328721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77076900008694001190219147 115615350013041001785328721)
  ·
    refine ⟨86711512509780751338996541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115615350013041001785328721 86711512509780751338996541)
    ·
      refine ⟨32516817191167781752123703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86711512509780751338996541 32516817191167781752123703)
      ·
        refine ⟨48775225786751672628185555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32516817191167781752123703 48775225786751672628185555)
        ·
          refine ⟨73162838680127508942278333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48775225786751672628185555 73162838680127508942278333)
          ·
            refine ⟨27436064505047815853354375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73162838680127508942278333 27436064505047815853354375)
            ·
              refine ⟨41154096757571723780031563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27436064505047815853354375 41154096757571723780031563)
              ·
                refine ⟨61731145136357585670047345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41154096757571723780031563 61731145136357585670047345)
                ·
                  refine ⟨46298358852268189252535509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61731145136357585670047345 46298358852268189252535509)
                  ·
                    refine ⟨1085117785600035685606301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46298358852268189252535509 1085117785600035685606301)
                    ·
                      rfl

theorem cell22_3169889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3169889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169889 prefixEnd_3169889 := by exact prefixLift 3169889
  have htrace : WordTrace (prefixWord ++ tailWord_3169889) baseStart_3169889 baseEnd_3169889 := by
    simpa [prefixWord, tailWord_3169889, baseEnd_3169889] using wordTrace_append hprefix tailTrace_3169889
  have hstable : (prefixWord ++ tailWord_3169889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169889).length < 2 ^ (prefixWord ++ tailWord_3169889).sum := by decide
  have hdescent : baseEnd_3169889 < baseStart_3169889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169891 : List Nat := [1, 1, 1, 5, 1, 3, 4, 6]
def baseStart_3169891 : Nat := 118140960795 + 3169891 * 2 ^ 59
def prefixEnd_3169891 : Nat := 4983230072969 + 3 ^ 40 * 3169891 * 2
def baseEnd_3169891 : Nat := 120568718915656483006255

theorem tailTrace_3169891 : CollatzResearch.WordTrace tailWord_3169891 prefixEnd_3169891 120568718915656483006255 := by
  unfold tailWord_3169891
  simp only [CollatzResearch.WordTrace]
  refine ⟨115615422959033756126901527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77076948639355837417934351 115615422959033756126901527)
  ·
    refine ⟨173423134438550634190352291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115615422959033756126901527 173423134438550634190352291)
    ·
      refine ⟨260134701657825951285528437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173423134438550634190352291 260134701657825951285528437)
      ·
        refine ⟨24387628280421182933018291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260134701657825951285528437 24387628280421182933018291)
        ·
          refine ⟨36581442420631774399527437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24387628280421182933018291 36581442420631774399527437)
          ·
            refine ⟨13718040907736915399822789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36581442420631774399527437 13718040907736915399822789)
            ·
              refine ⟨2572132670200671637466773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13718040907736915399822789 2572132670200671637466773)
              ·
                refine ⟨120568718915656483006255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2572132670200671637466773 120568718915656483006255)
                ·
                  rfl

theorem cell22_3169891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 6].length) (baseStart_3169891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169891 prefixEnd_3169891 := by exact prefixLift 3169891
  have htrace : WordTrace (prefixWord ++ tailWord_3169891) baseStart_3169891 baseEnd_3169891 := by
    simpa [prefixWord, tailWord_3169891, baseEnd_3169891] using wordTrace_append hprefix tailTrace_3169891
  have hstable : (prefixWord ++ tailWord_3169891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169891).length < 2 ^ (prefixWord ++ tailWord_3169891).sum := by decide
  have hdescent : baseEnd_3169891 < baseStart_3169891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169974 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3169974 : Nat := 118140960795 + 3169974 * 2 ^ 59
def prefixEnd_3169974 : Nat := 4983230072969 + 3 ^ 40 * 3169974 * 2
def baseEnd_3169974 : Nat := 1085146882837123797231041

theorem tailTrace_3169974 : CollatzResearch.WordTrace tailWord_3169974 prefixEnd_3169974 1085146882837123797231041 := by
  unfold tailWord_3169974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226153138608316331385811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77078966811822040868115317 7226153138608316331385811)
  ·
    refine ⟨10839229707912474497078717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7226153138608316331385811 10839229707912474497078717)
    ·
      refine ⟨4064711140467177936404519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10839229707912474497078717 4064711140467177936404519)
      ·
        refine ⟨6097066710700766904606779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064711140467177936404519 6097066710700766904606779)
        ·
          refine ⟨9145600066051150356910169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6097066710700766904606779 9145600066051150356910169)
          ·
            refine ⟨6859200049538362767682627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9145600066051150356910169 6859200049538362767682627)
            ·
              refine ⟨10288800074307544151523941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859200049538362767682627 10288800074307544151523941)
              ·
                refine ⟨1929150013932664528410739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10288800074307544151523941 1929150013932664528410739)
                ·
                  refine ⟨2893725020898996792616109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929150013932664528410739 2893725020898996792616109)
                  ·
                    refine ⟨1085146882837123797231041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893725020898996792616109 1085146882837123797231041)
                    ·
                      rfl

theorem cell22_3169974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3169974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169974 prefixEnd_3169974 := by exact prefixLift 3169974
  have htrace : WordTrace (prefixWord ++ tailWord_3169974) baseStart_3169974 baseEnd_3169974 := by
    simpa [prefixWord, tailWord_3169974, baseEnd_3169974] using wordTrace_append hprefix tailTrace_3169974
  have hstable : (prefixWord ++ tailWord_3169974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169974).length < 2 ^ (prefixWord ++ tailWord_3169974).sum := by decide
  have hdescent : baseEnd_3169974 < baseStart_3169974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169981 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 6]
def baseStart_3169981 : Nat := 118140960795 + 3169981 * 2 ^ 59
def prefixEnd_3169981 : Nat := 4983230072969 + 3 ^ 40 * 3169981 * 2
def baseEnd_3169981 : Nat := 361716426360059370768673

theorem tailTrace_3169981 : CollatzResearch.WordTrace tailWord_3169981 prefixEnd_3169981 361716426360059370768673 := by
  unfold tailWord_3169981
  simp only [CollatzResearch.WordTrace]
  refine ⟨115618705528707701497677797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77079137019138467665118531 115618705528707701497677797)
  ·
    refine ⟨21678507286632694030814587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115618705528707701497677797 21678507286632694030814587)
    ·
      refine ⟨32517760929949041046221881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21678507286632694030814587 32517760929949041046221881)
      ·
        refine ⟨24388320697461780784666411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32517760929949041046221881 24388320697461780784666411)
        ·
          refine ⟨36582481046192671176999617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24388320697461780784666411 36582481046192671176999617)
          ·
            refine ⟨27436860784644503382749713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36582481046192671176999617 27436860784644503382749713)
            ·
              refine ⟨20577645588483377537062285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27436860784644503382749713 20577645588483377537062285)
              ·
                refine ⟨7716617095681266576398357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20577645588483377537062285 7716617095681266576398357)
                ·
                  refine ⟨361716426360059370768673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7716617095681266576398357 361716426360059370768673)
                  ·
                    rfl

theorem cell22_3169981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_3169981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3169981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3169981 prefixEnd_3169981 := by exact prefixLift 3169981
  have htrace : WordTrace (prefixWord ++ tailWord_3169981) baseStart_3169981 baseEnd_3169981 := by
    simpa [prefixWord, tailWord_3169981, baseEnd_3169981] using wordTrace_append hprefix tailTrace_3169981
  have hstable : (prefixWord ++ tailWord_3169981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169981).length < 2 ^ (prefixWord ++ tailWord_3169981).sum := by decide
  have hdescent : baseEnd_3169981 < baseStart_3169981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170017 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 1, 4]
def baseStart_3170017 : Nat := 118140960795 + 3170017 * 2 ^ 59
def prefixEnd_3170017 : Nat := 4983230072969 + 3 ^ 40 * 3170017 * 2
def baseEnd_3170017 : Nat := 1085161602615886018405909

theorem tailTrace_3170017 : CollatzResearch.WordTrace tailWord_3170017 prefixEnd_3170017 1085161602615886018405909 := by
  unfold tailWord_3170017
  simp only [CollatzResearch.WordTrace]
  refine ⟨115620018556577279645988305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77080012371051519763992203 115620018556577279645988305)
  ·
    refine ⟨86715013917432959734491229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115620018556577279645988305 86715013917432959734491229)
    ·
      refine ⟨32518130219037359900434211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86715013917432959734491229 32518130219037359900434211)
      ·
        refine ⟨48777195328556039850651317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32518130219037359900434211 48777195328556039850651317)
        ·
          refine ⟨4572862062052128735998561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48777195328556039850651317 4572862062052128735998561)
          ·
            refine ⟨3429646546539096551998921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4572862062052128735998561 3429646546539096551998921)
            ·
              refine ⟨2572234909904322413999191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429646546539096551998921 2572234909904322413999191)
              ·
                refine ⟨3858352364856483620998787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572234909904322413999191 3858352364856483620998787)
                ·
                  refine ⟨5787528547284725431498181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858352364856483620998787 5787528547284725431498181)
                  ·
                    refine ⟨1085161602615886018405909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787528547284725431498181 1085161602615886018405909)
                    ·
                      rfl

theorem cell22_3170017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_3170017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170017 prefixEnd_3170017 := by exact prefixLift 3170017
  have htrace : WordTrace (prefixWord ++ tailWord_3170017) baseStart_3170017 baseEnd_3170017 := by
    simpa [prefixWord, tailWord_3170017, baseEnd_3170017] using wordTrace_append hprefix tailTrace_3170017
  have hstable : (prefixWord ++ tailWord_3170017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170017).length < 2 ^ (prefixWord ++ tailWord_3170017).sum := by decide
  have hdescent : baseEnd_3170017 < baseStart_3170017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170088 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_3170088 : Nat := 118140960795 + 3170088 * 2 ^ 59
def prefixEnd_3170088 : Nat := 4983230072969 + 3 ^ 40 * 3170088 * 2
def baseEnd_3170088 : Nat := 361728635788955166626897

theorem tailTrace_3170088 : CollatzResearch.WordTrace tailWord_3170088 prefixEnd_3170088 361728635788955166626897 := by
  unfold tailWord_3170088
  simp only [CollatzResearch.WordTrace]
  refine ⟨57811304069660029385911459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77081738759546705847881945 57811304069660029385911459)
  ·
    refine ⟨86716956104490044078867189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57811304069660029385911459 86716956104490044078867189)
    ·
      refine ⟨8129714634795941632393799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86716956104490044078867189 8129714634795941632393799)
      ·
        refine ⟨12194571952193912448590699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129714634795941632393799 12194571952193912448590699)
        ·
          refine ⟨18291857928290868672886049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194571952193912448590699 18291857928290868672886049)
          ·
            refine ⟨13718893446218151504664537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18291857928290868672886049 13718893446218151504664537)
            ·
              refine ⟨10289170084663613628498403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13718893446218151504664537 10289170084663613628498403)
              ·
                refine ⟨15433755126995420442747605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289170084663613628498403 15433755126995420442747605)
                ·
                  refine ⟨361728635788955166626897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15433755126995420442747605 361728635788955166626897)
                  ·
                    rfl

theorem cell22_3170088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_3170088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170088 prefixEnd_3170088 := by exact prefixLift 3170088
  have htrace : WordTrace (prefixWord ++ tailWord_3170088) baseStart_3170088 baseEnd_3170088 := by
    simpa [prefixWord, tailWord_3170088, baseEnd_3170088] using wordTrace_append hprefix tailTrace_3170088
  have hstable : (prefixWord ++ tailWord_3170088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170088).length < 2 ^ (prefixWord ++ tailWord_3170088).sum := by decide
  have hdescent : baseEnd_3170088 < baseStart_3170088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170165 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3170165 : Nat := 118140960795 + 3170165 * 2 ^ 59
def prefixEnd_3170165 : Nat := 4983230072969 + 3 ^ 40 * 3170165 * 2
def baseEnd_3170165 : Nat := 1085212266040462965705455

theorem tailTrace_3170165 : CollatzResearch.WordTrace tailWord_3170165 prefixEnd_3170165 1085212266040462965705455 := by
  unfold tailWord_3170165
  simp only [CollatzResearch.WordTrace]
  refine ⟨115625416560041100922375949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77083611040027400614917299 115625416560041100922375949)
  ·
    refine ⟨43359531210015412845890981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115625416560041100922375949 43359531210015412845890981)
    ·
      refine ⟨8129912101877889908604559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43359531210015412845890981 8129912101877889908604559)
      ·
        refine ⟨12194868152816834862906839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129912101877889908604559 12194868152816834862906839)
        ·
          refine ⟨18292302229225252294360259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194868152816834862906839 18292302229225252294360259)
          ·
            refine ⟨27438453343837878441540389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18292302229225252294360259 27438453343837878441540389)
            ·
              refine ⟨5144710001969602207788823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27438453343837878441540389 5144710001969602207788823)
              ·
                refine ⟨7717065002954403311683235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144710001969602207788823 7717065002954403311683235)
                ·
                  refine ⟨11575597504431604967524853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7717065002954403311683235 11575597504431604967524853)
                  ·
                    refine ⟨1085212266040462965705455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11575597504431604967524853 1085212266040462965705455)
                    ·
                      rfl

theorem cell22_3170165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3170165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170165 prefixEnd_3170165 := by exact prefixLift 3170165
  have htrace : WordTrace (prefixWord ++ tailWord_3170165) baseStart_3170165 baseEnd_3170165 := by
    simpa [prefixWord, tailWord_3170165, baseEnd_3170165] using wordTrace_append hprefix tailTrace_3170165
  have hstable : (prefixWord ++ tailWord_3170165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170165).length < 2 ^ (prefixWord ++ tailWord_3170165).sum := by decide
  have hdescent : baseEnd_3170165 < baseStart_3170165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170180 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3170180 : Nat := 118140960795 + 3170180 * 2 ^ 59
def prefixEnd_3170180 : Nat := 4983230072969 + 3 ^ 40 * 3170180 * 2
def baseEnd_3170180 : Nat := 1085217400847007926580409

theorem tailTrace_3170180 : CollatzResearch.WordTrace tailWord_3170180 prefixEnd_3170180 1085217400847007926580409 := by
  unfold tailWord_3170180
  simp only [CollatzResearch.WordTrace]
  refine ⟨57812981827493379242085997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77083975769991172322781329 57812981827493379242085997)
  ·
    refine ⟨21679868185310017215782249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57812981827493379242085997 21679868185310017215782249)
    ·
      refine ⟨16259901138982512911836687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21679868185310017215782249 16259901138982512911836687)
      ·
        refine ⟨24389851708473769367755031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16259901138982512911836687 24389851708473769367755031)
        ·
          refine ⟨36584777562710654051632547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24389851708473769367755031 36584777562710654051632547)
          ·
            refine ⟨54877166344065981077448821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36584777562710654051632547 54877166344065981077448821)
            ·
              refine ⟨5144734344756185726010827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54877166344065981077448821 5144734344756185726010827)
              ·
                refine ⟨7717101517134278589016241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144734344756185726010827 7717101517134278589016241)
                ·
                  refine ⟨5787826137850708941762181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717101517134278589016241 5787826137850708941762181)
                  ·
                    refine ⟨1085217400847007926580409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787826137850708941762181 1085217400847007926580409)
                    ·
                      rfl

theorem cell22_3170180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3170180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170180 prefixEnd_3170180 := by exact prefixLift 3170180
  have htrace : WordTrace (prefixWord ++ tailWord_3170180) baseStart_3170180 baseEnd_3170180 := by
    simpa [prefixWord, tailWord_3170180, baseEnd_3170180] using wordTrace_append hprefix tailTrace_3170180
  have hstable : (prefixWord ++ tailWord_3170180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170180).length < 2 ^ (prefixWord ++ tailWord_3170180).sum := by decide
  have hdescent : baseEnd_3170180 < baseStart_3170180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170186 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_3170186 : Nat := 118140960795 + 3170186 * 2 ^ 59
def prefixEnd_3170186 : Nat := 4983230072969 + 3 ^ 40 * 3170186 * 2
def baseEnd_3170186 : Nat := 1085219454769625910930391

theorem tailTrace_3170186 : CollatzResearch.WordTrace tailWord_3170186 prefixEnd_3170186 1085219454769625910930391 := by
  unfold tailWord_3170186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28906545623241255377222603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77084121661976681005926941 28906545623241255377222603)
  ·
    refine ⟨43359818434861883065833905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28906545623241255377222603 43359818434861883065833905)
    ·
      refine ⟨32519863826146412299375429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43359818434861883065833905 32519863826146412299375429)
      ·
        refine ⟨6097474467402452306132893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32519863826146412299375429 6097474467402452306132893)
        ·
          refine ⟨2286552925275919614799835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6097474467402452306132893 2286552925275919614799835)
          ·
            refine ⟨3429829387913879422199753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286552925275919614799835 3429829387913879422199753)
            ·
              refine ⟨2572372040935409566649815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429829387913879422199753 2572372040935409566649815)
              ·
                refine ⟨3858558061403114349974723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572372040935409566649815 3858558061403114349974723)
                ·
                  refine ⟨5787837092104671524962085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858558061403114349974723 5787837092104671524962085)
                  ·
                    refine ⟨1085219454769625910930391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787837092104671524962085 1085219454769625910930391)
                    ·
                      rfl

theorem cell22_3170186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_3170186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170186 prefixEnd_3170186 := by exact prefixLift 3170186
  have htrace : WordTrace (prefixWord ++ tailWord_3170186) baseStart_3170186 baseEnd_3170186 := by
    simpa [prefixWord, tailWord_3170186, baseEnd_3170186] using wordTrace_append hprefix tailTrace_3170186
  have hstable : (prefixWord ++ tailWord_3170186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170186).length < 2 ^ (prefixWord ++ tailWord_3170186).sum := by decide
  have hdescent : baseEnd_3170186 < baseStart_3170186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170216 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3170216 : Nat := 118140960795 + 3170216 * 2 ^ 59
def prefixEnd_3170216 : Nat := 4983230072969 + 3 ^ 40 * 3170216 * 2
def baseEnd_3170216 : Nat := 1085229724382715832680299

theorem tailTrace_3170216 : CollatzResearch.WordTrace tailWord_3170216 prefixEnd_3170216 1085229724382715832680299 := by
  unfold tailWord_3170216
  simp only [CollatzResearch.WordTrace]
  refine ⟨57813638341428168316241251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77084851121904224421655001 57813638341428168316241251)
  ·
    refine ⟨86720457512142252474361877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57813638341428168316241251 86720457512142252474361877)
    ·
      refine ⟨4065021445881668084735713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86720457512142252474361877 4065021445881668084735713)
      ·
        refine ⟨3048766084411251063551785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065021445881668084735713 3048766084411251063551785)
        ·
          refine ⟨2286574563308438297663839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048766084411251063551785 2286574563308438297663839)
          ·
            refine ⟨3429861844962657446495759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286574563308438297663839 3429861844962657446495759)
            ·
              refine ⟨5144792767443986169743639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429861844962657446495759 5144792767443986169743639)
              ·
                refine ⟨7717189151165979254615459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144792767443986169743639 7717189151165979254615459)
                ·
                  refine ⟨11575783726748968881923189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7717189151165979254615459 11575783726748968881923189)
                  ·
                    refine ⟨1085229724382715832680299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11575783726748968881923189 1085229724382715832680299)
                    ·
                      rfl

theorem cell22_3170216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3170216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170216 prefixEnd_3170216 := by exact prefixLift 3170216
  have htrace : WordTrace (prefixWord ++ tailWord_3170216) baseStart_3170216 baseEnd_3170216 := by
    simpa [prefixWord, tailWord_3170216, baseEnd_3170216] using wordTrace_append hprefix tailTrace_3170216
  have hstable : (prefixWord ++ tailWord_3170216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170216).length < 2 ^ (prefixWord ++ tailWord_3170216).sum := by decide
  have hdescent : baseEnd_3170216 < baseStart_3170216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170261 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_3170261 : Nat := 118140960795 + 3170261 * 2 ^ 59
def prefixEnd_3170261 : Nat := 4983230072969 + 3 ^ 40 * 3170261 * 2
def baseEnd_3170261 : Nat := 1085245128802350715305161

theorem tailTrace_3170261 : CollatzResearch.WordTrace tailWord_3170261 prefixEnd_3170261 1085245128802350715305161 := by
  unfold tailWord_3170261
  simp only [CollatzResearch.WordTrace]
  refine ⟨115628917967693309317870637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77085945311795539545247091 115628917967693309317870637)
  ·
    refine ⟨43360844237884990994201489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115628917967693309317870637 43360844237884990994201489)
    ·
      refine ⟨32520633178413743245651117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43360844237884990994201489 32520633178413743245651117)
      ·
        refine ⟨12195237441905153717119169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32520633178413743245651117 12195237441905153717119169)
        ·
          refine ⟨9146428081428865287839377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12195237441905153717119169 9146428081428865287839377)
          ·
            refine ⟨6859821061071648965879533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9146428081428865287839377 6859821061071648965879533)
            ·
              refine ⟨2572432897901868362204825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6859821061071648965879533 2572432897901868362204825)
              ·
                refine ⟨1929324673426401271653619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572432897901868362204825 1929324673426401271653619)
                ·
                  refine ⟨2893987010139601907480429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929324673426401271653619 2893987010139601907480429)
                  ·
                    refine ⟨1085245128802350715305161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893987010139601907480429 1085245128802350715305161)
                    ·
                      rfl

theorem cell22_3170261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_3170261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170261 prefixEnd_3170261 := by exact prefixLift 3170261
  have htrace : WordTrace (prefixWord ++ tailWord_3170261) baseStart_3170261 baseEnd_3170261 := by
    simpa [prefixWord, tailWord_3170261, baseEnd_3170261] using wordTrace_append hprefix tailTrace_3170261
  have hstable : (prefixWord ++ tailWord_3170261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170261).length < 2 ^ (prefixWord ++ tailWord_3170261).sum := by decide
  have hdescent : baseEnd_3170261 < baseStart_3170261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170274 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3170274 : Nat := 118140960795 + 3170274 * 2 ^ 59
def prefixEnd_3170274 : Nat := 4983230072969 + 3 ^ 40 * 3170274 * 2
def baseEnd_3170274 : Nat := 361749859656007671576707

theorem tailTrace_3170274 : CollatzResearch.WordTrace tailWord_3170274 prefixEnd_3170274 361749859656007671576707 := by
  unfold tailWord_3170274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907348029161553134523469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77086261411097475025395917 28907348029161553134523469)
  ·
    refine ⟨10840255510935582425446301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28907348029161553134523469 10840255510935582425446301)
    ·
      refine ⟨4065095816600843409542363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10840255510935582425446301 4065095816600843409542363)
      ·
        refine ⟨6097643724901265114313545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065095816600843409542363 6097643724901265114313545)
        ·
          refine ⟨4573232793675948835735159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097643724901265114313545 4573232793675948835735159)
          ·
            refine ⟨6859849190513923253602739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573232793675948835735159 6859849190513923253602739)
            ·
              refine ⟨10289773785770884880404109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859849190513923253602739 10289773785770884880404109)
              ·
                refine ⟨3858665169664081830151541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10289773785770884880404109 3858665169664081830151541)
                ·
                  refine ⟨361749859656007671576707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3858665169664081830151541 361749859656007671576707)
                  ·
                    rfl

theorem cell22_3170274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3170274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170274 prefixEnd_3170274 := by exact prefixLift 3170274
  have htrace : WordTrace (prefixWord ++ tailWord_3170274) baseStart_3170274 baseEnd_3170274 := by
    simpa [prefixWord, tailWord_3170274, baseEnd_3170274] using wordTrace_append hprefix tailTrace_3170274
  have hstable : (prefixWord ++ tailWord_3170274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170274).length < 2 ^ (prefixWord ++ tailWord_3170274).sum := by decide
  have hdescent : baseEnd_3170274 < baseStart_3170274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170283 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_3170283 : Nat := 118140960795 + 3170283 * 2 ^ 59
def prefixEnd_3170283 : Nat := 4983230072969 + 3 ^ 40 * 3170283 * 2
def baseEnd_3170283 : Nat := 1085252659851949991255093

theorem tailTrace_3170283 : CollatzResearch.WordTrace tailWord_3170283 prefixEnd_3170283 1085252659851949991255093 := by
  unfold tailWord_3170283
  simp only [CollatzResearch.WordTrace]
  refine ⟨115629720373613607075171503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77086480249075738050114335 115629720373613607075171503)
  ·
    refine ⟨173444580560420410612757255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115629720373613607075171503 173444580560420410612757255)
    ·
      refine ⟨260166870840630615919135883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173444580560420410612757255 260166870840630615919135883)
      ·
        refine ⟨390250306260945923878703825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260166870840630615919135883 390250306260945923878703825)
        ·
          refine ⟨292687729695709442909027869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390250306260945923878703825 292687729695709442909027869)
          ·
            refine ⟨109757898635891041090885451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292687729695709442909027869 109757898635891041090885451)
            ·
              refine ⟨164636847953836561636328177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109757898635891041090885451 164636847953836561636328177)
              ·
                refine ⟨123477635965377421227246133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164636847953836561636328177 123477635965377421227246133)
                ·
                  refine ⟨11576028371754133240054325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123477635965377421227246133 11576028371754133240054325)
                  ·
                    refine ⟨1085252659851949991255093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11576028371754133240054325 1085252659851949991255093)
                    ·
                      rfl

theorem cell22_3170283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_3170283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170283 prefixEnd_3170283 := by exact prefixLift 3170283
  have htrace : WordTrace (prefixWord ++ tailWord_3170283) baseStart_3170283 baseEnd_3170283 := by
    simpa [prefixWord, tailWord_3170283, baseEnd_3170283] using wordTrace_append hprefix tailTrace_3170283
  have hstable : (prefixWord ++ tailWord_3170283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170283).length < 2 ^ (prefixWord ++ tailWord_3170283).sum := by decide
  have hdescent : baseEnd_3170283 < baseStart_3170283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170300 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3170300 : Nat := 118140960795 + 3170300 * 2 ^ 59
def prefixEnd_3170300 : Nat := 4983230072969 + 3 ^ 40 * 3170300 * 2
def baseEnd_3170300 : Nat := 1085258479299367613580041

theorem tailTrace_3170300 : CollatzResearch.WordTrace tailWord_3170300 prefixEnd_3170300 1085258479299367613580041 := by
  unfold tailWord_3170300
  simp only [CollatzResearch.WordTrace]
  refine ⟨57815170207276009489270177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77086893609701345985693569 57815170207276009489270177)
  ·
    refine ⟨43361377655457007116952633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57815170207276009489270177 43361377655457007116952633)
    ·
      refine ⟨32521033241592755337714475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43361377655457007116952633 32521033241592755337714475)
      ·
        refine ⟨48781549862389133006571713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32521033241592755337714475 48781549862389133006571713)
        ·
          refine ⟨36586162396791849754928785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48781549862389133006571713 36586162396791849754928785)
          ·
            refine ⟨27439621797593887316196589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36586162396791849754928785 27439621797593887316196589)
            ·
              refine ⟨10289858174097707743573721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27439621797593887316196589 10289858174097707743573721)
              ·
                refine ⟨7717393630573280807680291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10289858174097707743573721 7717393630573280807680291)
                ·
                  refine ⟨11576090445859921211520437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7717393630573280807680291 11576090445859921211520437)
                  ·
                    refine ⟨1085258479299367613580041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11576090445859921211520437 1085258479299367613580041)
                    ·
                      rfl

theorem cell22_3170300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3170300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170300 prefixEnd_3170300 := by exact prefixLift 3170300
  have htrace : WordTrace (prefixWord ++ tailWord_3170300) baseStart_3170300 baseEnd_3170300 := by
    simpa [prefixWord, tailWord_3170300, baseEnd_3170300] using wordTrace_append hprefix tailTrace_3170300
  have hstable : (prefixWord ++ tailWord_3170300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170300).length < 2 ^ (prefixWord ++ tailWord_3170300).sum := by decide
  have hdescent : baseEnd_3170300 < baseStart_3170300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170315 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 2, 4]
def baseStart_3170315 : Nat := 118140960795 + 3170315 * 2 ^ 59
def prefixEnd_3170315 : Nat := 4983230072969 + 3 ^ 40 * 3170315 * 2
def baseEnd_3170315 : Nat := 1085263614105912574454995

theorem tailTrace_3170315 : CollatzResearch.WordTrace tailWord_3170315 prefixEnd_3170315 1085263614105912574454995 := by
  unfold tailWord_3170315
  simp only [CollatzResearch.WordTrace]
  refine ⟨115630887509497676540336399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77087258339665117693557599 115630887509497676540336399)
  ·
    refine ⟨173446331264246514810504599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115630887509497676540336399 173446331264246514810504599)
    ·
      refine ⟨260169496896369772215756899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173446331264246514810504599 260169496896369772215756899)
      ·
        refine ⟨390254245344554658323635349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260169496896369772215756899 390254245344554658323635349)
        ·
          refine ⟨18293167750525999608920407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 390254245344554658323635349 18293167750525999608920407)
          ·
            refine ⟨27439751625788999413380611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18293167750525999608920407 27439751625788999413380611)
            ·
              refine ⟨41159627438683499120070917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27439751625788999413380611 41159627438683499120070917)
              ·
                refine ⟨7717430144753156085013297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41159627438683499120070917 7717430144753156085013297)
                ·
                  refine ⟨5788072608564867063759973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717430144753156085013297 5788072608564867063759973)
                  ·
                    refine ⟨1085263614105912574454995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788072608564867063759973 1085263614105912574454995)
                    ·
                      rfl

theorem cell22_3170315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_3170315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170315 prefixEnd_3170315 := by exact prefixLift 3170315
  have htrace : WordTrace (prefixWord ++ tailWord_3170315) baseStart_3170315 baseEnd_3170315 := by
    simpa [prefixWord, tailWord_3170315, baseEnd_3170315] using wordTrace_append hprefix tailTrace_3170315
  have hstable : (prefixWord ++ tailWord_3170315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170315).length < 2 ^ (prefixWord ++ tailWord_3170315).sum := by decide
  have hdescent : baseEnd_3170315 < baseStart_3170315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170330 : List Nat := [3, 1, 1, 3, 1, 3, 3, 7]
def baseStart_3170330 : Nat := 118140960795 + 3170330 * 2 ^ 59
def prefixEnd_3170330 : Nat := 4983230072969 + 3 ^ 40 * 3170330 * 2
def baseEnd_3170330 : Nat := 120585416545828615036661

theorem tailTrace_3170330 : CollatzResearch.WordTrace tailWord_3170330 prefixEnd_3170330 120585416545828615036661 := by
  unfold tailWord_3170330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907858651110833525533111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77087623069628889401421629 28907858651110833525533111)
  ·
    refine ⟨43361787976666250288299667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28907858651110833525533111 43361787976666250288299667)
    ·
      refine ⟨65042681964999375432449501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43361787976666250288299667 65042681964999375432449501)
      ·
        refine ⟨24391005736874765787168563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65042681964999375432449501 24391005736874765787168563)
        ·
          refine ⟨36586508605312148680752845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24391005736874765787168563 36586508605312148680752845)
          ·
            refine ⟨13719940726992055755282317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36586508605312148680752845 13719940726992055755282317)
            ·
              refine ⟨5144977772622020908230869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13719940726992055755282317 5144977772622020908230869)
              ·
                refine ⟨120585416545828615036661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5144977772622020908230869 120585416545828615036661)
                ·
                  rfl

theorem cell22_3170330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_3170330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170330 prefixEnd_3170330 := by exact prefixLift 3170330
  have htrace : WordTrace (prefixWord ++ tailWord_3170330) baseStart_3170330 baseEnd_3170330 := by
    simpa [prefixWord, tailWord_3170330, baseEnd_3170330] using wordTrace_append hprefix tailTrace_3170330
  have hstable : (prefixWord ++ tailWord_3170330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170330).length < 2 ^ (prefixWord ++ tailWord_3170330).sum := by decide
  have hdescent : baseEnd_3170330 < baseStart_3170330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170375 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 7]
def baseStart_3170375 : Nat := 118140960795 + 3170375 * 2 ^ 59
def prefixEnd_3170375 : Nat := 4983230072969 + 3 ^ 40 * 3170375 * 2
def baseEnd_3170375 : Nat := 361761384444030805984937

theorem tailTrace_3170375 : CollatzResearch.WordTrace tailWord_3170375 prefixEnd_3170375 361761384444030805984937 := by
  unfold tailWord_3170375
  simp only [CollatzResearch.WordTrace]
  refine ⟨115633075889280306787520579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77088717259520204525013719 115633075889280306787520579)
  ·
    refine ⟨173449613833920460181280869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115633075889280306787520579 173449613833920460181280869)
    ·
      refine ⟨32521802593860086283990163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173449613833920460181280869 32521802593860086283990163)
      ·
        refine ⟨48782703890790129425985245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32521802593860086283990163 48782703890790129425985245)
        ·
          refine ⟨18293513959046298534744467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48782703890790129425985245 18293513959046298534744467)
          ·
            refine ⟨27440270938569447802116701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18293513959046298534744467 27440270938569447802116701)
            ·
              refine ⟨10290101601963542925793763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27440270938569447802116701 10290101601963542925793763)
              ·
                refine ⟨15435152402945314388690645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10290101601963542925793763 15435152402945314388690645)
                ·
                  refine ⟨361761384444030805984937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15435152402945314388690645 361761384444030805984937)
                  ·
                    rfl

theorem cell22_3170375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 7].length) (baseStart_3170375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170375 prefixEnd_3170375 := by exact prefixLift 3170375
  have htrace : WordTrace (prefixWord ++ tailWord_3170375) baseStart_3170375 baseEnd_3170375 := by
    simpa [prefixWord, tailWord_3170375, baseEnd_3170375] using wordTrace_append hprefix tailTrace_3170375
  have hstable : (prefixWord ++ tailWord_3170375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170375).length < 2 ^ (prefixWord ++ tailWord_3170375).sum := by decide
  have hdescent : baseEnd_3170375 < baseStart_3170375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170398 : List Nat := [4, 4, 1, 1, 2, 2, 2, 6]
def baseStart_3170398 : Nat := 118140960795 + 3170398 * 2 ^ 59
def prefixEnd_3170398 : Nat := 4983230072969 + 3 ^ 40 * 3170398 * 2
def baseEnd_3170398 : Nat := 120588002966903113847749

theorem tailTrace_3170398 : CollatzResearch.WordTrace tailWord_3170398 prefixEnd_3170398 120588002966903113847749 := by
  unfold tailWord_3170398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454239346024622714450981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77089276512131321143738565 14454239346024622714450981)
  ·
    refine ⟨2710169877379616758959559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14454239346024622714450981 2710169877379616758959559)
    ·
      refine ⟨4065254816069425138439339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710169877379616758959559 4065254816069425138439339)
      ·
        refine ⟨6097882224104137707659009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065254816069425138439339 6097882224104137707659009)
        ·
          refine ⟨4573411668078103280744257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097882224104137707659009 4573411668078103280744257)
          ·
            refine ⟨3430058751058577460558193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4573411668078103280744257 3430058751058577460558193)
            ·
              refine ⟨2572544063293933095418645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430058751058577460558193 2572544063293933095418645)
              ·
                refine ⟨120588002966903113847749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2572544063293933095418645 120588002966903113847749)
                ·
                  rfl

theorem cell22_3170398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_3170398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170398 prefixEnd_3170398 := by exact prefixLift 3170398
  have htrace : WordTrace (prefixWord ++ tailWord_3170398) baseStart_3170398 baseEnd_3170398 := by
    simpa [prefixWord, tailWord_3170398, baseEnd_3170398] using wordTrace_append hprefix tailTrace_3170398
  have hstable : (prefixWord ++ tailWord_3170398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170398).length < 2 ^ (prefixWord ++ tailWord_3170398).sum := by decide
  have hdescent : baseEnd_3170398 < baseStart_3170398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170437 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 6]
def baseStart_3170437 : Nat := 118140960795 + 3170437 * 2 ^ 59
def prefixEnd_3170437 : Nat := 4983230072969 + 3 ^ 40 * 3170437 * 2
def baseEnd_3170437 : Nat := 361768459066381640968207

theorem tailTrace_3170437 : CollatzResearch.WordTrace tailWord_3170437 prefixEnd_3170437 361768459066381640968207 := by
  unfold tailWord_3170437
  simp only [CollatzResearch.WordTrace]
  refine ⟨115635337215055691376277565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77090224810037127584185043 115635337215055691376277565)
  ·
    refine ⟨43363251455645884266104087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115635337215055691376277565 43363251455645884266104087)
    ·
      refine ⟨65044877183468826399156131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43363251455645884266104087 65044877183468826399156131)
      ·
        refine ⟨97567315775203239598734197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65044877183468826399156131 97567315775203239598734197)
        ·
          refine ⟨9146935853925303712381331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97567315775203239598734197 9146935853925303712381331)
          ·
            refine ⟨13720403780887955568571997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9146935853925303712381331 13720403780887955568571997)
            ·
              refine ⟨5145151417832983338214499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13720403780887955568571997 5145151417832983338214499)
              ·
                refine ⟨7717727126749475007321749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145151417832983338214499 7717727126749475007321749)
                ·
                  refine ⟨361768459066381640968207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7717727126749475007321749 361768459066381640968207)
                  ·
                    rfl

theorem cell22_3170437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_3170437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170437 prefixEnd_3170437 := by exact prefixLift 3170437
  have htrace : WordTrace (prefixWord ++ tailWord_3170437) baseStart_3170437 baseEnd_3170437 := by
    simpa [prefixWord, tailWord_3170437, baseEnd_3170437] using wordTrace_append hprefix tailTrace_3170437
  have hstable : (prefixWord ++ tailWord_3170437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170437).length < 2 ^ (prefixWord ++ tailWord_3170437).sum := by decide
  have hdescent : baseEnd_3170437 < baseStart_3170437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170456 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_3170456 : Nat := 118140960795 + 3170456 * 2 ^ 59
def prefixEnd_3170456 : Nat := 4983230072969 + 3 ^ 40 * 3170456 * 2
def baseEnd_3170456 : Nat := 1085311881287435206679563

theorem tailTrace_3170456 : CollatzResearch.WordTrace tailWord_3170456 prefixEnd_3170456 1085311881287435206679563 := by
  unfold tailWord_3170456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57818015100993428810609611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77090686801324571747479481 57818015100993428810609611)
  ·
    refine ⟨86727022651490143215914417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57818015100993428810609611 86727022651490143215914417)
    ·
      refine ⟨65045266988617607411935813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86727022651490143215914417 65045266988617607411935813)
      ·
        refine ⟨12195987560365801389737965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65045266988617607411935813 12195987560365801389737965)
        ·
          refine ⟨4573495335137175521151737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12195987560365801389737965 4573495335137175521151737)
          ·
            refine ⟨3430121501352881640863803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4573495335137175521151737 3430121501352881640863803)
            ·
              refine ⟨5145182252029322461295705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430121501352881640863803 5145182252029322461295705)
              ·
                refine ⟨3858886689021991845971779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145182252029322461295705 3858886689021991845971779)
                ·
                  refine ⟨5788330033532987768957669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858886689021991845971779 5788330033532987768957669)
                  ·
                    refine ⟨1085311881287435206679563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788330033532987768957669 1085311881287435206679563)
                    ·
                      rfl

theorem cell22_3170456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_3170456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170456 prefixEnd_3170456 := by exact prefixLift 3170456
  have htrace : WordTrace (prefixWord ++ tailWord_3170456) baseStart_3170456 baseEnd_3170456 := by
    simpa [prefixWord, tailWord_3170456, baseEnd_3170456] using wordTrace_append hprefix tailTrace_3170456
  have hstable : (prefixWord ++ tailWord_3170456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170456).length < 2 ^ (prefixWord ++ tailWord_3170456).sum := by decide
  have hdescent : baseEnd_3170456 < baseStart_3170456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170514 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_3170514 : Nat := 118140960795 + 3170514 * 2 ^ 59
def prefixEnd_3170514 : Nat := 4983230072969 + 3 ^ 40 * 3170514 * 2
def baseEnd_3170514 : Nat := 1085331735872742388729385

theorem tailTrace_3170514 : CollatzResearch.WordTrace tailWord_3170514 prefixEnd_3170514 1085331735872742388729385 := by
  unfold tailWord_3170514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28909536408944183381707649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77092097090517822351220397 28909536408944183381707649)
  ·
    refine ⟨21682152306708137536280737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28909536408944183381707649 21682152306708137536280737)
    ·
      refine ⟨16261614230031103152210553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21682152306708137536280737 16261614230031103152210553)
      ·
        refine ⟨12196210672523327364157915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16261614230031103152210553 12196210672523327364157915)
        ·
          refine ⟨18294316008784991046236873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196210672523327364157915 18294316008784991046236873)
          ·
            refine ⟨13720737006588743284677655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18294316008784991046236873 13720737006588743284677655)
            ·
              refine ⟨20581105509883114927016483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13720737006588743284677655 20581105509883114927016483)
              ·
                refine ⟨30871658264824672390524725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20581105509883114927016483 30871658264824672390524725)
                ·
                  refine ⟨2894217962327313036611693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30871658264824672390524725 2894217962327313036611693)
                  ·
                    refine ⟨1085331735872742388729385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2894217962327313036611693 1085331735872742388729385)
                    ·
                      rfl

theorem cell22_3170514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_3170514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170514 prefixEnd_3170514 := by exact prefixLift 3170514
  have htrace : WordTrace (prefixWord ++ tailWord_3170514) baseStart_3170514 baseEnd_3170514 := by
    simpa [prefixWord, tailWord_3170514, baseEnd_3170514] using wordTrace_append hprefix tailTrace_3170514
  have hstable : (prefixWord ++ tailWord_3170514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170514).length < 2 ^ (prefixWord ++ tailWord_3170514).sum := by decide
  have hdescent : baseEnd_3170514 < baseStart_3170514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170518 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3170518 : Nat := 118140960795 + 3170518 * 2 ^ 59
def prefixEnd_3170518 : Nat := 4983230072969 + 3 ^ 40 * 3170518 * 2
def baseEnd_3170518 : Nat := 1085333105154487711629373

theorem tailTrace_3170518 : CollatzResearch.WordTrace tailWord_3170518 prefixEnd_3170518 1085333105154487711629373 := by
  unfold tailWord_3170518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227393220485140138123513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77092194351841494806650805 7227393220485140138123513)
  ·
    refine ⟨5420544915363855103592635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7227393220485140138123513 5420544915363855103592635)
    ·
      refine ⟨8130817373045782655388953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420544915363855103592635 8130817373045782655388953)
      ·
        refine ⟨6098113029784336991541715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8130817373045782655388953 6098113029784336991541715)
        ·
          refine ⟨9147169544676505487312573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098113029784336991541715 9147169544676505487312573)
          ·
            refine ⟨3430188579253689557742215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9147169544676505487312573 3430188579253689557742215)
            ·
              refine ⟨5145282868880534336613323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430188579253689557742215 5145282868880534336613323)
              ·
                refine ⟨7717924303320801504919985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145282868880534336613323 7717924303320801504919985)
                ·
                  refine ⟨5788443227490601128689989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717924303320801504919985 5788443227490601128689989)
                  ·
                    refine ⟨1085333105154487711629373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788443227490601128689989 1085333105154487711629373)
                    ·
                      rfl

theorem cell22_3170518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3170518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170518 prefixEnd_3170518 := by exact prefixLift 3170518
  have htrace : WordTrace (prefixWord ++ tailWord_3170518) baseStart_3170518 baseEnd_3170518 := by
    simpa [prefixWord, tailWord_3170518, baseEnd_3170518] using wordTrace_append hprefix tailTrace_3170518
  have hstable : (prefixWord ++ tailWord_3170518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170518).length < 2 ^ (prefixWord ++ tailWord_3170518).sum := by decide
  have hdescent : baseEnd_3170518 < baseStart_3170518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170557 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_3170557 : Nat := 118140960795 + 3170557 * 2 ^ 59
def prefixEnd_3170557 : Nat := 4983230072969 + 3 ^ 40 * 3170557 * 2
def baseEnd_3170557 : Nat := 1085346455651504609904253

theorem tailTrace_3170557 : CollatzResearch.WordTrace tailWord_3170557 prefixEnd_3170557 1085346455651504609904253 := by
  unfold tailWord_3170557
  simp only [CollatzResearch.WordTrace]
  refine ⟨115639713974620951870645925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77093142649747301247097283 115639713974620951870645925)
  ·
    refine ⟨21682446370241428475746111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115639713974620951870645925 21682446370241428475746111)
    ·
      refine ⟨32523669555362142713619167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21682446370241428475746111 32523669555362142713619167)
      ·
        refine ⟨48785504333043214070428751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32523669555362142713619167 48785504333043214070428751)
        ·
          refine ⟨73178256499564821105643127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48785504333043214070428751 73178256499564821105643127)
          ·
            refine ⟨109767384749347231658464691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73178256499564821105643127 109767384749347231658464691)
            ·
              refine ⟨164651077124020847487697037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109767384749347231658464691 164651077124020847487697037)
              ·
                refine ⟨61744153921507817807886389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164651077124020847487697037 61744153921507817807886389)
                ·
                  refine ⟨5788514430141357919489349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61744153921507817807886389 5788514430141357919489349)
                  ·
                    refine ⟨1085346455651504609904253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788514430141357919489349 1085346455651504609904253)
                    ·
                      rfl

theorem cell22_3170557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_3170557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170557 prefixEnd_3170557 := by exact prefixLift 3170557
  have htrace : WordTrace (prefixWord ++ tailWord_3170557) baseStart_3170557 baseEnd_3170557 := by
    simpa [prefixWord, tailWord_3170557, baseEnd_3170557] using wordTrace_append hprefix tailTrace_3170557
  have hstable : (prefixWord ++ tailWord_3170557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170557).length < 2 ^ (prefixWord ++ tailWord_3170557).sum := by decide
  have hdescent : baseEnd_3170557 < baseStart_3170557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170572 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_3170572 : Nat := 118140960795 + 3170572 * 2 ^ 59
def prefixEnd_3170572 : Nat := 4983230072969 + 3 ^ 40 * 3170572 * 2
def baseEnd_3170572 : Nat := 361783863486016523593069

theorem tailTrace_3170572 : CollatzResearch.WordTrace tailWord_3170572 prefixEnd_3170572 361783863486016523593069 := by
  unfold tailWord_3170572
  simp only [CollatzResearch.WordTrace]
  refine ⟨57820130534783304716220985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77093507379711072954961313 57820130534783304716220985)
  ·
    refine ⟨43365097901087478537165739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57820130534783304716220985 43365097901087478537165739)
    ·
      refine ⟨65047646851631217805748609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43365097901087478537165739 65047646851631217805748609)
      ·
        refine ⟨48785735138723413354311457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65047646851631217805748609 48785735138723413354311457)
        ·
          refine ⟨36589301354042560015733593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48785735138723413354311457 36589301354042560015733593)
          ·
            refine ⟨27441976015531920011800195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36589301354042560015733593 27441976015531920011800195)
            ·
              refine ⟨41162964023297880017700293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27441976015531920011800195 41162964023297880017700293)
              ·
                refine ⟨7718055754368352503318805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41162964023297880017700293 7718055754368352503318805)
                ·
                  refine ⟨361783863486016523593069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7718055754368352503318805 361783863486016523593069)
                  ·
                    rfl

theorem cell22_3170572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_3170572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170572 prefixEnd_3170572 := by exact prefixLift 3170572
  have htrace : WordTrace (prefixWord ++ tailWord_3170572) baseStart_3170572 baseEnd_3170572 := by
    simpa [prefixWord, tailWord_3170572, baseEnd_3170572] using wordTrace_append hprefix tailTrace_3170572
  have hstable : (prefixWord ++ tailWord_3170572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170572).length < 2 ^ (prefixWord ++ tailWord_3170572).sum := by decide
  have hdescent : baseEnd_3170572 < baseStart_3170572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170587 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 1, 5]
def baseStart_3170587 : Nat := 118140960795 + 3170587 * 2 ^ 59
def prefixEnd_3170587 : Nat := 4983230072969 + 3 ^ 40 * 3170587 * 2
def baseEnd_3170587 : Nat := 1085356725264594531654161

theorem tailTrace_3170587 : CollatzResearch.WordTrace tailWord_3170587 prefixEnd_3170587 1085356725264594531654161 := by
  unfold tailWord_3170587
  simp only [CollatzResearch.WordTrace]
  refine ⟨115640808164512266994238015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77093872109674844662825343 115640808164512266994238015)
  ·
    refine ⟨173461212246768400491357023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115640808164512266994238015 173461212246768400491357023)
    ·
      refine ⟨260191818370152600737035535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173461212246768400491357023 260191818370152600737035535)
      ·
        refine ⟨390287727555228901105553303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260191818370152600737035535 390287727555228901105553303)
        ·
          refine ⟨585431591332843351658329955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390287727555228901105553303 585431591332843351658329955)
          ·
            refine ⟨878147386999265027487494933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585431591332843351658329955 878147386999265027487494933)
            ·
              refine ⟨41163158765590548163476325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 878147386999265027487494933 41163158765590548163476325)
              ·
                refine ⟨7718092268548227780651811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41163158765590548163476325 7718092268548227780651811)
                ·
                  refine ⟨11577138402822341670977717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718092268548227780651811 11577138402822341670977717)
                  ·
                    refine ⟨1085356725264594531654161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11577138402822341670977717 1085356725264594531654161)
                    ·
                      rfl

theorem cell22_3170587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_3170587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170587 prefixEnd_3170587 := by exact prefixLift 3170587
  have htrace : WordTrace (prefixWord ++ tailWord_3170587) baseStart_3170587 baseEnd_3170587 := by
    simpa [prefixWord, tailWord_3170587, baseEnd_3170587] using wordTrace_append hprefix tailTrace_3170587
  have hstable : (prefixWord ++ tailWord_3170587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170587).length < 2 ^ (prefixWord ++ tailWord_3170587).sum := by decide
  have hdescent : baseEnd_3170587 < baseStart_3170587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170599 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3170599 : Nat := 118140960795 + 3170599 * 2 ^ 59
def prefixEnd_3170599 : Nat := 4983230072969 + 3 ^ 40 * 3170599 * 2
def baseEnd_3170599 : Nat := 1085360833109830500354125

theorem tailTrace_3170599 : CollatzResearch.WordTrace tailWord_3170599 prefixEnd_3170599 1085360833109830500354125 := by
  unfold tailWord_3170599
  simp only [CollatzResearch.WordTrace]
  refine ⟨115641245840468793043674851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77094163893645862029116567 115641245840468793043674851)
  ·
    refine ⟨173461868760703189565512277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115641245840468793043674851 173461868760703189565512277)
    ·
      refine ⟨2032756274539490502720847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 173461868760703189565512277 2032756274539490502720847)
      ·
        refine ⟨3049134411809235754081271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032756274539490502720847 3049134411809235754081271)
        ·
          refine ⟨4573701617713853631121907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049134411809235754081271 4573701617713853631121907)
          ·
            refine ⟨6860552426570780446682861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573701617713853631121907 6860552426570780446682861)
            ·
              refine ⟨2572707159964042667506073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6860552426570780446682861 2572707159964042667506073)
              ·
                refine ⟨1929530369973032000629555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572707159964042667506073 1929530369973032000629555)
                ·
                  refine ⟨2894295554959548000944333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929530369973032000629555 2894295554959548000944333)
                  ·
                    refine ⟨1085360833109830500354125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2894295554959548000944333 1085360833109830500354125)
                    ·
                      rfl

theorem cell22_3170599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3170599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170599 prefixEnd_3170599 := by exact prefixLift 3170599
  have htrace : WordTrace (prefixWord ++ tailWord_3170599) baseStart_3170599 baseEnd_3170599 := by
    simpa [prefixWord, tailWord_3170599, baseEnd_3170599] using wordTrace_append hprefix tailTrace_3170599
  have hstable : (prefixWord ++ tailWord_3170599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170599).length < 2 ^ (prefixWord ++ tailWord_3170599).sum := by decide
  have hdescent : baseEnd_3170599 < baseStart_3170599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170604 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_3170604 : Nat := 118140960795 + 3170604 * 2 ^ 59
def prefixEnd_3170604 : Nat := 4983230072969 + 3 ^ 40 * 3170604 * 2
def baseEnd_3170604 : Nat := 1085362544712012153979109

theorem tailTrace_3170604 : CollatzResearch.WordTrace tailWord_3170604 prefixEnd_3170604 1085362544712012153979109 := by
  unfold tailWord_3170604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57820714102725339448803433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77094285470300452598404577 57820714102725339448803433)
  ·
    refine ⟨43365535577044004586602575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57820714102725339448803433 43365535577044004586602575)
    ·
      refine ⟨65048303365566006879903863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43365535577044004586602575 65048303365566006879903863)
      ·
        refine ⟨97572455048349010319855795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65048303365566006879903863 97572455048349010319855795)
        ·
          refine ⟨146358682572523515479783693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97572455048349010319855795 146358682572523515479783693)
          ·
            refine ⟨54884505964696318304918885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146358682572523515479783693 54884505964696318304918885)
            ·
              refine ⟨10290844868380559682172291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54884505964696318304918885 10290844868380559682172291)
              ·
                refine ⟨15436267302570839523258437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10290844868380559682172291 15436267302570839523258437)
                ·
                  refine ⟨2894300119232032410610957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15436267302570839523258437 2894300119232032410610957)
                  ·
                    refine ⟨1085362544712012153979109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2894300119232032410610957 1085362544712012153979109)
                    ·
                      rfl

theorem cell22_3170604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_3170604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170604 prefixEnd_3170604 := by exact prefixLift 3170604
  have htrace : WordTrace (prefixWord ++ tailWord_3170604) baseStart_3170604 baseEnd_3170604 := by
    simpa [prefixWord, tailWord_3170604, baseEnd_3170604] using wordTrace_append hprefix tailTrace_3170604
  have hstable : (prefixWord ++ tailWord_3170604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170604).length < 2 ^ (prefixWord ++ tailWord_3170604).sum := by decide
  have hdescent : baseEnd_3170604 < baseStart_3170604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170625 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3170625 : Nat := 118140960795 + 3170625 * 2 ^ 59
def prefixEnd_3170625 : Nat := 4983230072969 + 3 ^ 40 * 3170625 * 2
def baseEnd_3170625 : Nat := 1085369733441175099204045

theorem tailTrace_3170625 : CollatzResearch.WordTrace tailWord_3170625 prefixEnd_3170625 1085369733441175099204045 := by
  unfold tailWord_3170625
  simp only [CollatzResearch.WordTrace]
  refine ⟨115642194138374599484121329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77094796092249732989414219 115642194138374599484121329)
  ·
    refine ⟨86731645603780949613090997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115642194138374599484121329 86731645603780949613090997)
    ·
      refine ⟨8131091775354464026227281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86731645603780949613090997 8131091775354464026227281)
      ·
        refine ⟨6098318831515848019670461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8131091775354464026227281 6098318831515848019670461)
        ·
          refine ⟨2286869561818443007376423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6098318831515848019670461 2286869561818443007376423)
          ·
            refine ⟨3430304342727664511064635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286869561818443007376423 3430304342727664511064635)
            ·
              refine ⟨5145456514091496766596953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430304342727664511064635 5145456514091496766596953)
              ·
                refine ⟨3859092385568622574947715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145456514091496766596953 3859092385568622574947715)
                ·
                  refine ⟨5788638578352933862421573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859092385568622574947715 5788638578352933862421573)
                  ·
                    refine ⟨1085369733441175099204045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788638578352933862421573 1085369733441175099204045)
                    ·
                      rfl

theorem cell22_3170625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3170625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170625 prefixEnd_3170625 := by exact prefixLift 3170625
  have htrace : WordTrace (prefixWord ++ tailWord_3170625) baseStart_3170625 baseEnd_3170625 := by
    simpa [prefixWord, tailWord_3170625, baseEnd_3170625] using wordTrace_append hprefix tailTrace_3170625
  have hstable : (prefixWord ++ tailWord_3170625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170625).length < 2 ^ (prefixWord ++ tailWord_3170625).sum := by decide
  have hdescent : baseEnd_3170625 < baseStart_3170625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170632 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3170632 : Nat := 118140960795 + 3170632 * 2 ^ 59
def prefixEnd_3170632 : Nat := 4983230072969 + 3 ^ 40 * 3170632 * 2
def baseEnd_3170632 : Nat := 1085372129684229414279023

theorem tailTrace_3170632 : CollatzResearch.WordTrace tailWord_3170632 prefixEnd_3170632 1085372129684229414279023 := by
  unfold tailWord_3170632
  simp only [CollatzResearch.WordTrace]
  refine ⟨57821224724674619839813075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77094966299566159786417433 57821224724674619839813075)
  ·
    refine ⟨86731837087011929759719613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57821224724674619839813075 86731837087011929759719613)
    ·
      refine ⟨32524438907629473659894855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86731837087011929759719613 32524438907629473659894855)
      ·
        refine ⟨48786658361444210489842283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32524438907629473659894855 48786658361444210489842283)
        ·
          refine ⟨73179987542166315734763425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48786658361444210489842283 73179987542166315734763425)
          ·
            refine ⟨54884990656624736801072569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73179987542166315734763425 54884990656624736801072569)
            ·
              refine ⟨41163742992468552600804427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54884990656624736801072569 41163742992468552600804427)
              ·
                refine ⟨61745614488702828901206641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41163742992468552600804427 61745614488702828901206641)
                ·
                  refine ⟨46309210866527121675904981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61745614488702828901206641 46309210866527121675904981)
                  ·
                    refine ⟨1085372129684229414279023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46309210866527121675904981 1085372129684229414279023)
                    ·
                      rfl

theorem cell22_3170632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3170632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170632 prefixEnd_3170632 := by exact prefixLift 3170632
  have htrace : WordTrace (prefixWord ++ tailWord_3170632) baseStart_3170632 baseEnd_3170632 := by
    simpa [prefixWord, tailWord_3170632, baseEnd_3170632] using wordTrace_append hprefix tailTrace_3170632
  have hstable : (prefixWord ++ tailWord_3170632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170632).length < 2 ^ (prefixWord ++ tailWord_3170632).sum := by decide
  have hdescent : baseEnd_3170632 < baseStart_3170632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170664 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3170664 : Nat := 118140960795 + 3170664 * 2 ^ 59
def prefixEnd_3170664 : Nat := 4983230072969 + 3 ^ 40 * 3170664 * 2
def baseEnd_3170664 : Nat := 1085383083938191997478925

theorem tailTrace_3170664 : CollatzResearch.WordTrace tailWord_3170664 prefixEnd_3170664 1085383083938191997478925 := by
  unfold tailWord_3170664
  simp only [CollatzResearch.WordTrace]
  refine ⟨57821808292616654572395523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77095744390155539429860697 57821808292616654572395523)
  ·
    refine ⟨86732712438924981858593285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57821808292616654572395523 86732712438924981858593285)
    ·
      refine ⟨16262383582298434098486241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86732712438924981858593285 16262383582298434098486241)
      ·
        refine ⟨12196787686723825573864681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16262383582298434098486241 12196787686723825573864681)
        ·
          refine ⟨9147590765042869180398511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12196787686723825573864681 9147590765042869180398511)
          ·
            refine ⟨13721386147564303770597767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9147590765042869180398511 13721386147564303770597767)
            ·
              refine ⟨20582079221346455655896651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13721386147564303770597767 20582079221346455655896651)
              ·
                refine ⟨30873118832019683483844977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20582079221346455655896651 30873118832019683483844977)
                ·
                  refine ⟨23154839124014762612883733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30873118832019683483844977 23154839124014762612883733)
                  ·
                    refine ⟨1085383083938191997478925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23154839124014762612883733 1085383083938191997478925)
                    ·
                      rfl

theorem cell22_3170664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3170664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170664 prefixEnd_3170664 := by exact prefixLift 3170664
  have htrace : WordTrace (prefixWord ++ tailWord_3170664) baseStart_3170664 baseEnd_3170664 := by
    simpa [prefixWord, tailWord_3170664, baseEnd_3170664] using wordTrace_append hprefix tailTrace_3170664
  have hstable : (prefixWord ++ tailWord_3170664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170664).length < 2 ^ (prefixWord ++ tailWord_3170664).sum := by decide
  have hdescent : baseEnd_3170664 < baseStart_3170664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170724 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_3170724 : Nat := 118140960795 + 3170724 * 2 ^ 59
def prefixEnd_3170724 : Nat := 4983230072969 + 3 ^ 40 * 3170724 * 2
def baseEnd_3170724 : Nat := 361801207721457280326247

theorem tailTrace_3170724 : CollatzResearch.WordTrace tailWord_3170724 prefixEnd_3170724 361801207721457280326247 := by
  unfold tailWord_3170724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57822902482507969695987613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77097203310010626261316817 57822902482507969695987613)
  ·
    refine ⟨21683588430940488635995355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57822902482507969695987613 21683588430940488635995355)
    ·
      refine ⟨32525382646410732953993033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21683588430940488635995355 32525382646410732953993033)
      ·
        refine ⟨24394036984808049715494775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32525382646410732953993033 24394036984808049715494775)
        ·
          refine ⟨36591055477212074573242163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24394036984808049715494775 36591055477212074573242163)
          ·
            refine ⟨54886583215818111859863245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36591055477212074573242163 54886583215818111859863245)
            ·
              refine ⟨20582468705931791947448717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54886583215818111859863245 20582468705931791947448717)
              ·
                refine ⟨7718425764724421980293269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20582468705931791947448717 7718425764724421980293269)
                ·
                  refine ⟨361801207721457280326247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7718425764724421980293269 361801207721457280326247)
                  ·
                    rfl

theorem cell22_3170724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_3170724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170724 prefixEnd_3170724 := by exact prefixLift 3170724
  have htrace : WordTrace (prefixWord ++ tailWord_3170724) baseStart_3170724 baseEnd_3170724 := by
    simpa [prefixWord, tailWord_3170724, baseEnd_3170724] using wordTrace_append hprefix tailTrace_3170724
  have hstable : (prefixWord ++ tailWord_3170724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170724).length < 2 ^ (prefixWord ++ tailWord_3170724).sum := by decide
  have hdescent : baseEnd_3170724 < baseStart_3170724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170801 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_3170801 : Nat := 118140960795 + 3170801 * 2 ^ 59
def prefixEnd_3170801 : Nat := 4983230072969 + 3 ^ 40 * 3170801 * 2
def baseEnd_3170801 : Nat := 1085429981837969306803505

theorem tailTrace_3170801 : CollatzResearch.WordTrace tailWord_3170801 prefixEnd_3170801 1085429981837969306803505 := by
  unfold tailWord_3170801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115648613385736981542528257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77099075590491321028352171 115648613385736981542528257)
  ·
    refine ⟨86736460039302736156896193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115648613385736981542528257 86736460039302736156896193)
    ·
      refine ⟨65052345029477052117672145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86736460039302736156896193 65052345029477052117672145)
      ·
        refine ⟨48789258772107789088254109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65052345029477052117672145 48789258772107789088254109)
        ·
          refine ⟨18295972039540420908095291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48789258772107789088254109 18295972039540420908095291)
          ·
            refine ⟨27443958059310631362142937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295972039540420908095291 27443958059310631362142937)
            ·
              refine ⟨20582968544482973521607203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27443958059310631362142937 20582968544482973521607203)
              ·
                refine ⟨30874452816724460282410805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20582968544482973521607203 30874452816724460282410805)
                ·
                  refine ⟨2894479951567918151476013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30874452816724460282410805 2894479951567918151476013)
                  ·
                    refine ⟨1085429981837969306803505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2894479951567918151476013 1085429981837969306803505)
                    ·
                      rfl

theorem cell22_3170801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_3170801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170801 prefixEnd_3170801 := by exact prefixLift 3170801
  have htrace : WordTrace (prefixWord ++ tailWord_3170801) baseStart_3170801 baseEnd_3170801 := by
    simpa [prefixWord, tailWord_3170801, baseEnd_3170801] using wordTrace_append hprefix tailTrace_3170801
  have hstable : (prefixWord ++ tailWord_3170801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170801).length < 2 ^ (prefixWord ++ tailWord_3170801).sum := by decide
  have hdescent : baseEnd_3170801 < baseStart_3170801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170805 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3170805 : Nat := 118140960795 + 3170805 * 2 ^ 59
def prefixEnd_3170805 : Nat := 4983230072969 + 3 ^ 40 * 3170805 * 2
def baseEnd_3170805 : Nat := 1085431351119714629703493

theorem tailTrace_3170805 : CollatzResearch.WordTrace tailWord_3170805 prefixEnd_3170805 1085431351119714629703493 := by
  unfold tailWord_3170805
  simp only [CollatzResearch.WordTrace]
  refine ⟨115648759277722490225673869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77099172851814993483782579 115648759277722490225673869)
  ·
    refine ⟨43368284729145933834627701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115648759277722490225673869 43368284729145933834627701)
    ·
      refine ⟨4065776693357431296996347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43368284729145933834627701 4065776693357431296996347)
      ·
        refine ⟨6098665040036146945494521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065776693357431296996347 6098665040036146945494521)
        ·
          refine ⟨4573998780027110209120891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6098665040036146945494521 4573998780027110209120891)
          ·
            refine ⟨6860998170040665313681337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573998780027110209120891 6860998170040665313681337)
            ·
              refine ⟨5145748627530498985261003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860998170040665313681337 5145748627530498985261003)
              ·
                refine ⟨7718622941295748477891505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145748627530498985261003 7718622941295748477891505)
                ·
                  refine ⟨5788967205971811358418629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7718622941295748477891505 5788967205971811358418629)
                  ·
                    refine ⟨1085431351119714629703493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788967205971811358418629 1085431351119714629703493)
                    ·
                      rfl

theorem cell22_3170805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3170805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170805 prefixEnd_3170805 := by exact prefixLift 3170805
  have htrace : WordTrace (prefixWord ++ tailWord_3170805) baseStart_3170805 baseEnd_3170805 := by
    simpa [prefixWord, tailWord_3170805, baseEnd_3170805] using wordTrace_append hprefix tailTrace_3170805
  have hstable : (prefixWord ++ tailWord_3170805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170805).length < 2 ^ (prefixWord ++ tailWord_3170805).sum := by decide
  have hdescent : baseEnd_3170805 < baseStart_3170805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170822 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3170822 : Nat := 118140960795 + 3170822 * 2 ^ 59
def prefixEnd_3170822 : Nat := 4983230072969 + 3 ^ 40 * 3170822 * 2
def baseEnd_3170822 : Nat := 1085437170567132252028441

theorem tailTrace_3170822 : CollatzResearch.WordTrace tailWord_3170822 prefixEnd_3170822 1085437170567132252028441 := by
  unfold tailWord_3170822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3614043103708153191532585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77099586212440601419361813 3614043103708153191532585)
  ·
    refine ⟨2710532327781114893649439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3614043103708153191532585 2710532327781114893649439)
    ·
      refine ⟨4065798491671672340474159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710532327781114893649439 4065798491671672340474159)
      ·
        refine ⟨6098697737507508510711239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065798491671672340474159 6098697737507508510711239)
        ·
          refine ⟨9148046606261262766066859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098697737507508510711239 9148046606261262766066859)
          ·
            refine ⟨13722069909391894149100289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148046606261262766066859 13722069909391894149100289)
            ·
              refine ⟨10291552432043920611825217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13722069909391894149100289 10291552432043920611825217)
              ·
                refine ⟨7718664324032940458868913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10291552432043920611825217 7718664324032940458868913)
                ·
                  refine ⟨5788998243024705344151685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7718664324032940458868913 5788998243024705344151685)
                  ·
                    refine ⟨1085437170567132252028441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788998243024705344151685 1085437170567132252028441)
                    ·
                      rfl

theorem cell22_3170822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3170822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170822 prefixEnd_3170822 := by exact prefixLift 3170822
  have htrace : WordTrace (prefixWord ++ tailWord_3170822) baseStart_3170822 baseEnd_3170822 := by
    simpa [prefixWord, tailWord_3170822, baseEnd_3170822] using wordTrace_append hprefix tailTrace_3170822
  have hstable : (prefixWord ++ tailWord_3170822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170822).length < 2 ^ (prefixWord ++ tailWord_3170822).sum := by decide
  have hdescent : baseEnd_3170822 < baseStart_3170822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170893 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3170893 : Nat := 118140960795 + 3170893 * 2 ^ 59
def prefixEnd_3170893 : Nat := 4983230072969 + 3 ^ 40 * 3170893 * 2
def baseEnd_3170893 : Nat := 361820491772703911167741

theorem tailTrace_3170893 : CollatzResearch.WordTrace tailWord_3170893 prefixEnd_3170893 361820491772703911167741 := by
  unfold tailWord_3170893
  simp only [CollatzResearch.WordTrace]
  refine ⟨115651968901403681254877333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77101312600935787503251555 115651968901403681254877333)
  ·
    refine ⟨5421186042253297558822375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115651968901403681254877333 5421186042253297558822375)
    ·
      refine ⟨8131779063379946338233563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5421186042253297558822375 8131779063379946338233563)
      ·
        refine ⟨12197668595069919507350345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8131779063379946338233563 12197668595069919507350345)
        ·
          refine ⟨9148251446302439630512759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12197668595069919507350345 9148251446302439630512759)
          ·
            refine ⟨13722377169453659445769139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148251446302439630512759 13722377169453659445769139)
            ·
              refine ⟨20583565754180489168653709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13722377169453659445769139 20583565754180489168653709)
              ·
                refine ⟨7718837157817683438245141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20583565754180489168653709 7718837157817683438245141)
                ·
                  refine ⟨361820491772703911167741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7718837157817683438245141 361820491772703911167741)
                  ·
                    rfl

theorem cell22_3170893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3170893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170893 prefixEnd_3170893 := by exact prefixLift 3170893
  have htrace : WordTrace (prefixWord ++ tailWord_3170893) baseStart_3170893 baseEnd_3170893 := by
    simpa [prefixWord, tailWord_3170893, baseEnd_3170893] using wordTrace_append hprefix tailTrace_3170893
  have hstable : (prefixWord ++ tailWord_3170893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170893).length < 2 ^ (prefixWord ++ tailWord_3170893).sum := by decide
  have hdescent : baseEnd_3170893 < baseStart_3170893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170951 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3170951 : Nat := 118140960795 + 3170951 * 2 ^ 59
def prefixEnd_3170951 : Nat := 4983230072969 + 3 ^ 40 * 3170951 * 2
def baseEnd_3170951 : Nat := 1085481329903418915553045

theorem tailTrace_3170951 : CollatzResearch.WordTrace tailWord_3170951 prefixEnd_3170951 1085481329903418915553045 := by
  unfold tailWord_3170951
  simp only [CollatzResearch.WordTrace]
  refine ⟨115654084335193557160488707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77102722890129038106992471 115654084335193557160488707)
  ·
    refine ⟨173481126502790335740733061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115654084335193557160488707 173481126502790335740733061)
    ·
      refine ⟨32527711219273187951387449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173481126502790335740733061 32527711219273187951387449)
      ·
        refine ⟨24395783414454890963540587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32527711219273187951387449 24395783414454890963540587)
        ·
          refine ⟨36593675121682336445310881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24395783414454890963540587 36593675121682336445310881)
          ·
            refine ⟨27445256341261752333983161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36593675121682336445310881 27445256341261752333983161)
            ·
              refine ⟨20583942255946314250487371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27445256341261752333983161 20583942255946314250487371)
              ·
                refine ⟨30875913383919471375731057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20583942255946314250487371 30875913383919471375731057)
                ·
                  refine ⟨23156935037939603531798293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30875913383919471375731057 23156935037939603531798293)
                  ·
                    refine ⟨1085481329903418915553045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23156935037939603531798293 1085481329903418915553045)
                    ·
                      rfl

theorem cell22_3170951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3170951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170951 prefixEnd_3170951 := by exact prefixLift 3170951
  have htrace : WordTrace (prefixWord ++ tailWord_3170951) baseStart_3170951 baseEnd_3170951 := by
    simpa [prefixWord, tailWord_3170951, baseEnd_3170951] using wordTrace_append hprefix tailTrace_3170951
  have hstable : (prefixWord ++ tailWord_3170951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170951).length < 2 ^ (prefixWord ++ tailWord_3170951).sum := by decide
  have hdescent : baseEnd_3170951 < baseStart_3170951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170981 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_3170981 : Nat := 118140960795 + 3170981 * 2 ^ 59
def prefixEnd_3170981 : Nat := 4983230072969 + 3 ^ 40 * 3170981 * 2
def baseEnd_3170981 : Nat := 1085491599516508837302953

theorem tailTrace_3170981 : CollatzResearch.WordTrace tailWord_3170981 prefixEnd_3170981 1085491599516508837302953 := by
  unfold tailWord_3170981
  simp only [CollatzResearch.WordTrace]
  refine ⟨115655178525084872284080797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77103452350056581522720531 115655178525084872284080797)
  ·
    refine ⟨43370691946906827106530299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115655178525084872284080797 43370691946906827106530299)
    ·
      refine ⟨65056037920360240659795449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43370691946906827106530299 65056037920360240659795449)
      ·
        refine ⟨48792028440270180494846587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65056037920360240659795449 48792028440270180494846587)
        ·
          refine ⟨73188042660405270742269881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48792028440270180494846587 73188042660405270742269881)
          ·
            refine ⟨54891031995303953056702411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73188042660405270742269881 54891031995303953056702411)
            ·
              refine ⟨82336547992955929585053617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54891031995303953056702411 82336547992955929585053617)
              ·
                refine ⟨61752410994716947188790213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82336547992955929585053617 61752410994716947188790213)
                ·
                  refine ⟨11578577061509427597898165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61752410994716947188790213 11578577061509427597898165)
                  ·
                    refine ⟨1085491599516508837302953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11578577061509427597898165 1085491599516508837302953)
                    ·
                      rfl

theorem cell22_3170981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_3170981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170981 prefixEnd_3170981 := by exact prefixLift 3170981
  have htrace : WordTrace (prefixWord ++ tailWord_3170981) baseStart_3170981 baseEnd_3170981 := by
    simpa [prefixWord, tailWord_3170981, baseEnd_3170981] using wordTrace_append hprefix tailTrace_3170981
  have hstable : (prefixWord ++ tailWord_3170981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170981).length < 2 ^ (prefixWord ++ tailWord_3170981).sum := by decide
  have hdescent : baseEnd_3170981 < baseStart_3170981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171045 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 4]
def baseStart_3171045 : Nat := 118140960795 + 3171045 * 2 ^ 59
def prefixEnd_3171045 : Nat := 4983230072969 + 3 ^ 40 * 3171045 * 2
def baseEnd_3171045 : Nat := 361837836008144667900919

theorem tailTrace_3171045 : CollatzResearch.WordTrace tailWord_3171045 prefixEnd_3171045 361837836008144667900919 := by
  unfold tailWord_3171045
  simp only [CollatzResearch.WordTrace]
  refine ⟨115657512796853011214410589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77105008531235340809607059 115657512796853011214410589)
  ·
    refine ⟨43371567298819879205403971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115657512796853011214410589 43371567298819879205403971)
    ·
      refine ⟨65057350948229818808105957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43371567298819879205403971 65057350948229818808105957)
      ·
        refine ⟨12198253302793091026519867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65057350948229818808105957 12198253302793091026519867)
        ·
          refine ⟨18297379954189636539779801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12198253302793091026519867 18297379954189636539779801)
          ·
            refine ⟨13723034965642227404834851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18297379954189636539779801 13723034965642227404834851)
            ·
              refine ⟨20584552448463341107252277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13723034965642227404834851 20584552448463341107252277)
              ·
                refine ⟨1929801792043438228804901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20584552448463341107252277 1929801792043438228804901)
                ·
                  refine ⟨361837836008144667900919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929801792043438228804901 361837836008144667900919)
                  ·
                    rfl

theorem cell22_3171045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_3171045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171045 prefixEnd_3171045 := by exact prefixLift 3171045
  have htrace : WordTrace (prefixWord ++ tailWord_3171045) baseStart_3171045 baseEnd_3171045 := by
    simpa [prefixWord, tailWord_3171045, baseEnd_3171045] using wordTrace_append hprefix tailTrace_3171045
  have hstable : (prefixWord ++ tailWord_3171045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171045).length < 2 ^ (prefixWord ++ tailWord_3171045).sum := by decide
  have hdescent : baseEnd_3171045 < baseStart_3171045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171056 : List Nat := [2, 1, 1, 1, 3, 1, 13]
def baseStart_3171056 : Nat := 118140960795 + 3171056 * 2 ^ 59
def prefixEnd_3171056 : Nat := 4983230072969 + 3 ^ 40 * 3171056 * 2
def baseEnd_3171056 : Nat := 40204343464786431173249

theorem tailTrace_3171056 : CollatzResearch.WordTrace tailWord_3171056 prefixEnd_3171056 40204343464786431173249 := by
  unfold tailWord_3171056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57828956999906580046530511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77105275999875440062040681 57828956999906580046530511)
  ·
    refine ⟨86743435499859870069795767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57828956999906580046530511 86743435499859870069795767)
    ·
      refine ⟨130115153249789805104693651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86743435499859870069795767 130115153249789805104693651)
      ·
        refine ⟨195172729874684707657040477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130115153249789805104693651 195172729874684707657040477)
        ·
          refine ⟨73189773703006765371390179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195172729874684707657040477 73189773703006765371390179)
          ·
            refine ⟨109784660554510148057085269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73189773703006765371390179 109784660554510148057085269)
            ·
              refine ⟨40204343464786431173249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 109784660554510148057085269 40204343464786431173249)
              ·
                rfl

theorem cell22_3171056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 13].length) (baseStart_3171056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171056 prefixEnd_3171056 := by exact prefixLift 3171056
  have htrace : WordTrace (prefixWord ++ tailWord_3171056) baseStart_3171056 baseEnd_3171056 := by
    simpa [prefixWord, tailWord_3171056, baseEnd_3171056] using wordTrace_append hprefix tailTrace_3171056
  have hstable : (prefixWord ++ tailWord_3171056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171056).length < 2 ^ (prefixWord ++ tailWord_3171056).sum := by decide
  have hdescent : baseEnd_3171056 < baseStart_3171056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171135 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 5]
def baseStart_3171135 : Nat := 118140960795 + 3171135 * 2 ^ 59
def prefixEnd_3171135 : Nat := 4983230072969 + 3 ^ 40 * 3171135 * 2
def baseEnd_3171135 : Nat := 361848105621234589650827

theorem tailTrace_3171135 : CollatzResearch.WordTrace tailWord_3171135 prefixEnd_3171135 361848105621234589650827 := by
  unfold tailWord_3171135
  simp only [CollatzResearch.WordTrace]
  refine ⟨115660795366526956585186859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77107196911017971056791239 115660795366526956585186859)
  ·
    refine ⟨173491193049790434877780289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115660795366526956585186859 173491193049790434877780289)
    ·
      refine ⟨130118394787342826158335217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173491193049790434877780289 130118394787342826158335217)
      ·
        refine ⟨97588796090507119618751413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130118394787342826158335217 97588796090507119618751413)
        ·
          refine ⟨9148949633485042464257945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97588796090507119618751413 9148949633485042464257945)
          ·
            refine ⟨6861712225113781848193459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9148949633485042464257945 6861712225113781848193459)
            ·
              refine ⟨10292568337670672772290189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6861712225113781848193459 10292568337670672772290189)
              ·
                refine ⟨3859713126626502289608821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10292568337670672772290189 3859713126626502289608821)
                ·
                  refine ⟨361848105621234589650827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3859713126626502289608821 361848105621234589650827)
                  ·
                    rfl

theorem cell22_3171135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 5].length) (baseStart_3171135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171135 prefixEnd_3171135 := by exact prefixLift 3171135
  have htrace : WordTrace (prefixWord ++ tailWord_3171135) baseStart_3171135 baseEnd_3171135 := by
    simpa [prefixWord, tailWord_3171135, baseEnd_3171135] using wordTrace_append hprefix tailTrace_3171135
  have hstable : (prefixWord ++ tailWord_3171135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171135).length < 2 ^ (prefixWord ++ tailWord_3171135).sum := by decide
  have hdescent : baseEnd_3171135 < baseStart_3171135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171257 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_3171257 : Nat := 118140960795 + 3171257 * 2 ^ 59
def prefixEnd_3171257 : Nat := 4983230072969 + 3 ^ 40 * 3171257 * 2
def baseEnd_3171257 : Nat := 1085586079956936117402107

theorem tailTrace_3171257 : CollatzResearch.WordTrace tailWord_3171257 prefixEnd_3171257 1085586079956936117402107 := by
  unfold tailWord_3171257
  simp only [CollatzResearch.WordTrace]
  refine ⟨115665245072084971421128025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77110163381389980947418683 115665245072084971421128025)
  ·
    refine ⟨86748933804063728565846019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115665245072084971421128025 86748933804063728565846019)
    ·
      refine ⟨130123400706095592848769029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86748933804063728565846019 130123400706095592848769029)
      ·
        refine ⟨24398137632392923659144193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130123400706095592848769029 24398137632392923659144193)
        ·
          refine ⟨18298603224294692744358145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24398137632392923659144193 18298603224294692744358145)
          ·
            refine ⟨13723952418221019558268609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18298603224294692744358145 13723952418221019558268609)
            ·
              refine ⟨10292964313665764668701457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13723952418221019558268609 10292964313665764668701457)
              ·
                refine ⟨7719723235249323501526093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10292964313665764668701457 7719723235249323501526093)
                ·
                  refine ⟨2894896213218496313072285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7719723235249323501526093 2894896213218496313072285)
                  ·
                    refine ⟨1085586079956936117402107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2894896213218496313072285 1085586079956936117402107)
                    ·
                      rfl

theorem cell22_3171257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_3171257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171257 prefixEnd_3171257 := by exact prefixLift 3171257
  have htrace : WordTrace (prefixWord ++ tailWord_3171257) baseStart_3171257 baseEnd_3171257 := by
    simpa [prefixWord, tailWord_3171257, baseEnd_3171257] using wordTrace_append hprefix tailTrace_3171257
  have hstable : (prefixWord ++ tailWord_3171257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171257).length < 2 ^ (prefixWord ++ tailWord_3171257).sum := by decide
  have hdescent : baseEnd_3171257 < baseStart_3171257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171349 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 4]
def baseStart_3171349 : Nat := 118140960795 + 3171349 * 2 ^ 59
def prefixEnd_3171349 : Nat := 4983230072969 + 3 ^ 40 * 3171349 * 2
def baseEnd_3171349 : Nat := 361872524479026181367275

theorem tailTrace_3171349 : CollatzResearch.WordTrace tailWord_3171349 prefixEnd_3171349 361872524479026181367275 := by
  unfold tailWord_3171349
  simp only [CollatzResearch.WordTrace]
  refine ⟨115668600587751671133477101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77112400391834447422318067 115668600587751671133477101)
  ·
    refine ⟨43375725220406876675053913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115668600587751671133477101 43375725220406876675053913)
    ·
      refine ⟨32531793915305157506290435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43375725220406876675053913 32531793915305157506290435)
      ·
        refine ⟨48797690872957736259435653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32531793915305157506290435 48797690872957736259435653)
        ·
          refine ⟨9149567038679575548644185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48797690872957736259435653 9149567038679575548644185)
          ·
            refine ⟨6862175279009681661483139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9149567038679575548644185 6862175279009681661483139)
            ·
              refine ⟨10293262918514522492224709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6862175279009681661483139 10293262918514522492224709)
              ·
                refine ⟨1929986797221472967292133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10293262918514522492224709 1929986797221472967292133)
                ·
                  refine ⟨361872524479026181367275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929986797221472967292133 361872524479026181367275)
                  ·
                    rfl

theorem cell22_3171349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_3171349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171349 prefixEnd_3171349 := by exact prefixLift 3171349
  have htrace : WordTrace (prefixWord ++ tailWord_3171349) baseStart_3171349 baseEnd_3171349 := by
    simpa [prefixWord, tailWord_3171349, baseEnd_3171349] using wordTrace_append hprefix tailTrace_3171349
  have hstable : (prefixWord ++ tailWord_3171349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171349).length < 2 ^ (prefixWord ++ tailWord_3171349).sum := by decide
  have hdescent : baseEnd_3171349 < baseStart_3171349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171364 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_3171364 : Nat := 118140960795 + 3171364 * 2 ^ 59
def prefixEnd_3171364 : Nat := 4983230072969 + 3 ^ 40 * 3171364 * 2
def baseEnd_3171364 : Nat := 1085622708243623504976779

theorem tailTrace_3171364 : CollatzResearch.WordTrace tailWord_3171364 prefixEnd_3171364 1085622708243623504976779 := by
  unfold tailWord_3171364
  simp only [CollatzResearch.WordTrace]
  refine ⟨57834573841348664347636573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77112765121798219130182097 57834573841348664347636573)
  ·
    refine ⟨21687965190505749130363715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57834573841348664347636573 21687965190505749130363715)
    ·
      refine ⟨32531947785758623695545573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21687965190505749130363715 32531947785758623695545573)
      ·
        refine ⟨6099740209829741942914795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32531947785758623695545573 6099740209829741942914795)
        ·
          refine ⟨9149610314744612914372193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099740209829741942914795 9149610314744612914372193)
          ·
            refine ⟨6862207736058459685779145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9149610314744612914372193 6862207736058459685779145)
            ·
              refine ⟨5146655802043844764334359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6862207736058459685779145 5146655802043844764334359)
              ·
                refine ⟨7719983703065767146501539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146655802043844764334359 7719983703065767146501539)
                ·
                  refine ⟨11579975554598650719752309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7719983703065767146501539 11579975554598650719752309)
                  ·
                    refine ⟨1085622708243623504976779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11579975554598650719752309 1085622708243623504976779)
                    ·
                      rfl

theorem cell22_3171364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_3171364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171364 prefixEnd_3171364 := by exact prefixLift 3171364
  have htrace : WordTrace (prefixWord ++ tailWord_3171364) baseStart_3171364 baseEnd_3171364 := by
    simpa [prefixWord, tailWord_3171364, baseEnd_3171364] using wordTrace_append hprefix tailTrace_3171364
  have hstable : (prefixWord ++ tailWord_3171364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171364).length < 2 ^ (prefixWord ++ tailWord_3171364).sum := by decide
  have hdescent : baseEnd_3171364 < baseStart_3171364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171377 : List Nat := [1, 2, 2, 3, 1, 2, 5, 6]
def baseStart_3171377 : Nat := 118140960795 + 3171377 * 2 ^ 59
def prefixEnd_3171377 : Nat := 4983230072969 + 3 ^ 40 * 3171377 * 2
def baseEnd_3171377 : Nat := 120625239823255089377971

theorem tailTrace_3171377 : CollatzResearch.WordTrace tailWord_3171377 prefixEnd_3171377 120625239823255089377971 := by
  unfold tailWord_3171377
  simp only [CollatzResearch.WordTrace]
  refine ⟨115669621831650231915496385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77113081221100154610330923 115669621831650231915496385)
  ·
    refine ⟨86752216373737673936622289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115669621831650231915496385 86752216373737673936622289)
    ·
      refine ⟨65064162280303255452466717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86752216373737673936622289 65064162280303255452466717)
      ·
        refine ⟨24399060855113720794675019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65064162280303255452466717 24399060855113720794675019)
        ·
          refine ⟨36598591282670581192012529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24399060855113720794675019 36598591282670581192012529)
          ·
            refine ⟨27448943462002935894009397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36598591282670581192012529 27448943462002935894009397)
            ·
              refine ⟨2573338449562775240063381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27448943462002935894009397 2573338449562775240063381)
              ·
                refine ⟨120625239823255089377971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2573338449562775240063381 120625239823255089377971)
                ·
                  rfl

theorem cell22_3171377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 6].length) (baseStart_3171377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171377 prefixEnd_3171377 := by exact prefixLift 3171377
  have htrace : WordTrace (prefixWord ++ tailWord_3171377) baseStart_3171377 baseEnd_3171377 := by
    simpa [prefixWord, tailWord_3171377, baseEnd_3171377] using wordTrace_append hprefix tailTrace_3171377
  have hstable : (prefixWord ++ tailWord_3171377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171377).length < 2 ^ (prefixWord ++ tailWord_3171377).sum := by decide
  have hdescent : baseEnd_3171377 < baseStart_3171377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171392 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_3171392 : Nat := 118140960795 + 3171392 * 2 ^ 59
def prefixEnd_3171392 : Nat := 4983230072969 + 3 ^ 40 * 3171392 * 2
def baseEnd_3171392 : Nat := 1085632293215840765276693

theorem tailTrace_3171392 : CollatzResearch.WordTrace tailWord_3171392 prefixEnd_3171392 1085632293215840765276693 := by
  unfold tailWord_3171392
  simp only [CollatzResearch.WordTrace]
  refine ⟨57835084463297944738646215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77113445951063926318194953 57835084463297944738646215)
  ·
    refine ⟨86752626694946917107969323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57835084463297944738646215 86752626694946917107969323)
    ·
      refine ⟨130128940042420375661953985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86752626694946917107969323 130128940042420375661953985)
      ·
        refine ⟨97596705031815281746465489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130128940042420375661953985 97596705031815281746465489)
        ·
          refine ⟨73197528773861461309849117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97596705031815281746465489 73197528773861461309849117)
          ·
            refine ⟨27449073290198047991193419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73197528773861461309849117 27449073290198047991193419)
            ·
              refine ⟨41173609935297071986790129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27449073290198047991193419 41173609935297071986790129)
              ·
                refine ⟨30880207451472803990092597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41173609935297071986790129 30880207451472803990092597)
                ·
                  refine ⟨2895019448575575374071181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30880207451472803990092597 2895019448575575374071181)
                  ·
                    refine ⟨1085632293215840765276693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895019448575575374071181 1085632293215840765276693)
                    ·
                      rfl

theorem cell22_3171392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_3171392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171392 prefixEnd_3171392 := by exact prefixLift 3171392
  have htrace : WordTrace (prefixWord ++ tailWord_3171392) baseStart_3171392 baseEnd_3171392 := by
    simpa [prefixWord, tailWord_3171392, baseEnd_3171392] using wordTrace_append hprefix tailTrace_3171392
  have hstable : (prefixWord ++ tailWord_3171392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171392).length < 2 ^ (prefixWord ++ tailWord_3171392).sum := by decide
  have hdescent : baseEnd_3171392 < baseStart_3171392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171398 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3171398 : Nat := 118140960795 + 3171398 * 2 ^ 59
def prefixEnd_3171398 : Nat := 4983230072969 + 3 ^ 40 * 3171398 * 2
def baseEnd_3171398 : Nat := 1085634347138458749626675

theorem tailTrace_3171398 : CollatzResearch.WordTrace tailWord_3171398 prefixEnd_3171398 1085634347138458749626675 := by
  unfold tailWord_3171398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3614699617642942265687839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77113591843049435001340565 3614699617642942265687839)
  ·
    refine ⟨5422049426464413398531759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3614699617642942265687839 5422049426464413398531759)
    ·
      refine ⟨8133074139696620097797639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5422049426464413398531759 8133074139696620097797639)
      ·
        refine ⟨12199611209544930146696459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8133074139696620097797639 12199611209544930146696459)
        ·
          refine ⟨18299416814317395220044689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12199611209544930146696459 18299416814317395220044689)
          ·
            refine ⟨13724562610738046415033517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18299416814317395220044689 13724562610738046415033517)
            ·
              refine ⟨5146710979026767405637569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13724562610738046415033517 5146710979026767405637569)
              ·
                refine ⟨3860033234270075554228177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5146710979026767405637569 3860033234270075554228177)
                ·
                  refine ⟨2895024925702556665671133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3860033234270075554228177 2895024925702556665671133)
                  ·
                    refine ⟨1085634347138458749626675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895024925702556665671133 1085634347138458749626675)
                    ·
                      rfl

theorem cell22_3171398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3171398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171398 prefixEnd_3171398 := by exact prefixLift 3171398
  have htrace : WordTrace (prefixWord ++ tailWord_3171398) baseStart_3171398 baseEnd_3171398 := by
    simpa [prefixWord, tailWord_3171398, baseEnd_3171398] using wordTrace_append hprefix tailTrace_3171398
  have hstable : (prefixWord ++ tailWord_3171398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171398).length < 2 ^ (prefixWord ++ tailWord_3171398).sum := by decide
  have hdescent : baseEnd_3171398 < baseStart_3171398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171426 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3171426 : Nat := 118140960795 + 3171426 * 2 ^ 59
def prefixEnd_3171426 : Nat := 4983230072969 + 3 ^ 40 * 3171426 * 2
def baseEnd_3171426 : Nat := 1085643932110676009926589

theorem tailTrace_3171426 : CollatzResearch.WordTrace tailWord_3171426 prefixEnd_3171426 1085643932110676009926589 := by
  unfold tailWord_3171426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28917852252118178321007533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77114272672315142189353421 28917852252118178321007533)
  ·
    refine ⟨10844194594544316870377825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28917852252118178321007533 10844194594544316870377825)
    ·
      refine ⟨8133145945908237652783369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10844194594544316870377825 8133145945908237652783369)
      ·
        refine ⟨6099859459431178239587527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8133145945908237652783369 6099859459431178239587527)
        ·
          refine ⟨9149789189146767359381291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099859459431178239587527 9149789189146767359381291)
          ·
            refine ⟨13724683783720151039071937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149789189146767359381291 13724683783720151039071937)
            ·
              refine ⟨10293512837790113279303953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13724683783720151039071937 10293512837790113279303953)
              ·
                refine ⟨7720134628342584959477965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10293512837790113279303953 7720134628342584959477965)
                ·
                  refine ⟨2895050485628469359804237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7720134628342584959477965 2895050485628469359804237)
                  ·
                    refine ⟨1085643932110676009926589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895050485628469359804237 1085643932110676009926589)
                    ·
                      rfl

theorem cell22_3171426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3171426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171426 prefixEnd_3171426 := by exact prefixLift 3171426
  have htrace : WordTrace (prefixWord ++ tailWord_3171426) baseStart_3171426 baseEnd_3171426 := by
    simpa [prefixWord, tailWord_3171426, baseEnd_3171426] using wordTrace_append hprefix tailTrace_3171426
  have hstable : (prefixWord ++ tailWord_3171426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171426).length < 2 ^ (prefixWord ++ tailWord_3171426).sum := by decide
  have hdescent : baseEnd_3171426 < baseStart_3171426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171435 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_3171435 : Nat := 118140960795 + 3171435 * 2 ^ 59
def prefixEnd_3171435 : Nat := 4983230072969 + 3 ^ 40 * 3171435 * 2
def baseEnd_3171435 : Nat := 1085647012994602986451561

theorem tailTrace_3171435 : CollatzResearch.WordTrace tailWord_3171435 prefixEnd_3171435 1085647012994602986451561 := by
  unfold tailWord_3171435
  simp only [CollatzResearch.WordTrace]
  refine ⟨115671737265440107821107759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77114491510293405214071839 115671737265440107821107759)
  ·
    refine ⟨173507605898160161731661639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115671737265440107821107759 173507605898160161731661639)
    ·
      refine ⟨260261408847240242597492459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173507605898160161731661639 260261408847240242597492459)
      ·
        refine ⟨390392113270860363896238689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260261408847240242597492459 390392113270860363896238689)
        ·
          refine ⟨292794084953145272922179017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390392113270860363896238689 292794084953145272922179017)
          ·
            refine ⟨219595563714858954691634263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292794084953145272922179017 219595563714858954691634263)
            ·
              refine ⟨329393345572288432037451395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219595563714858954691634263 329393345572288432037451395)
              ·
                refine ⟨494090018358432648056177093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329393345572288432037451395 494090018358432648056177093)
                ·
                  refine ⟨92641878442206121510533205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 494090018358432648056177093 92641878442206121510533205)
                  ·
                    refine ⟨1085647012994602986451561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92641878442206121510533205 1085647012994602986451561)
                    ·
                      rfl

theorem cell22_3171435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_3171435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171435 prefixEnd_3171435 := by exact prefixLift 3171435
  have htrace : WordTrace (prefixWord ++ tailWord_3171435) baseStart_3171435 baseEnd_3171435 := by
    simpa [prefixWord, tailWord_3171435, baseEnd_3171435] using wordTrace_append hprefix tailTrace_3171435
  have hstable : (prefixWord ++ tailWord_3171435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171435).length < 2 ^ (prefixWord ++ tailWord_3171435).sum := by decide
  have hdescent : baseEnd_3171435 < baseStart_3171435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171486 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3171486 : Nat := 118140960795 + 3171486 * 2 ^ 59
def prefixEnd_3171486 : Nat := 4983230072969 + 3 ^ 40 * 3171486 * 2
def baseEnd_3171486 : Nat := 1085664471336855853426405

theorem tailTrace_3171486 : CollatzResearch.WordTrace tailWord_3171486 prefixEnd_3171486 1085664471336855853426405 := by
  unfold tailWord_3171486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459199673531917941401789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77115731592170229020809541 14459199673531917941401789)
  ·
    refine ⟨5422199877574469228025671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14459199673531917941401789 5422199877574469228025671)
    ·
      refine ⟨8133299816361703842038507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5422199877574469228025671 8133299816361703842038507)
      ·
        refine ⟨12199949724542555763057761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8133299816361703842038507 12199949724542555763057761)
        ·
          refine ⟨9149962293406916822293321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12199949724542555763057761 9149962293406916822293321)
          ·
            refine ⟨6862471720055187616719991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9149962293406916822293321 6862471720055187616719991)
            ·
              refine ⟨10293707580082781425079987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6862471720055187616719991 10293707580082781425079987)
              ·
                refine ⟨15440561370124172137619981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10293707580082781425079987 15440561370124172137619981)
                ·
                  refine ⟨5790210513796564551607493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15440561370124172137619981 5790210513796564551607493)
                  ·
                    refine ⟨1085664471336855853426405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790210513796564551607493 1085664471336855853426405)
                    ·
                      rfl

theorem cell22_3171486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3171486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171486 prefixEnd_3171486 := by exact prefixLift 3171486
  have htrace : WordTrace (prefixWord ++ tailWord_3171486) baseStart_3171486 baseEnd_3171486 := by
    simpa [prefixWord, tailWord_3171486, baseEnd_3171486] using wordTrace_append hprefix tailTrace_3171486
  have hstable : (prefixWord ++ tailWord_3171486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171486).length < 2 ^ (prefixWord ++ tailWord_3171486).sum := by decide
  have hdescent : baseEnd_3171486 < baseStart_3171486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171516 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_3171516 : Nat := 118140960795 + 3171516 * 2 ^ 59
def prefixEnd_3171516 : Nat := 4983230072969 + 3 ^ 40 * 3171516 * 2
def baseEnd_3171516 : Nat := 1085674740949945775176313

theorem tailTrace_3171516 : CollatzResearch.WordTrace tailWord_3171516 prefixEnd_3171516 1085674740949945775176313 := by
  unfold tailWord_3171516
  simp only [CollatzResearch.WordTrace]
  refine ⟨57837345789073329327403201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77116461052097772436537601 57837345789073329327403201)
  ·
    refine ⟨43378009341804996995552401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57837345789073329327403201 43378009341804996995552401)
    ·
      refine ⟨32533507006353747746664301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43378009341804996995552401 32533507006353747746664301)
      ·
        refine ⟨12200065127382655404999113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32533507006353747746664301 12200065127382655404999113)
        ·
          refine ⟨9150048845536991553749335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12200065127382655404999113 9150048845536991553749335)
          ·
            refine ⟨13725073268305487330624003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150048845536991553749335 13725073268305487330624003)
            ·
              refine ⟨20587609902458230995936005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13725073268305487330624003 20587609902458230995936005)
              ·
                refine ⟨3860176856710918311738001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20587609902458230995936005 3860176856710918311738001)
                ·
                  refine ⟨2895132642533188733803501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3860176856710918311738001 2895132642533188733803501)
                  ·
                    refine ⟨1085674740949945775176313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895132642533188733803501 1085674740949945775176313)
                    ·
                      rfl

theorem cell22_3171516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_3171516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171516 prefixEnd_3171516 := by exact prefixLift 3171516
  have htrace : WordTrace (prefixWord ++ tailWord_3171516) baseStart_3171516 baseEnd_3171516 := by
    simpa [prefixWord, tailWord_3171516, baseEnd_3171516] using wordTrace_append hprefix tailTrace_3171516
  have hstable : (prefixWord ++ tailWord_3171516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171516).length < 2 ^ (prefixWord ++ tailWord_3171516).sum := by decide
  have hdescent : baseEnd_3171516 < baseStart_3171516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171518 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_3171518 : Nat := 118140960795 + 3171518 * 2 ^ 59
def prefixEnd_3171518 : Nat := 4983230072969 + 3 ^ 40 * 3171518 * 2
def baseEnd_3171518 : Nat := 361891808530272812208769

theorem tailTrace_3171518 : CollatzResearch.WordTrace tailWord_3171518 prefixEnd_3171518 361891808530272812208769 := by
  unfold tailWord_3171518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459345565517426624547401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77116509682759608664252805 14459345565517426624547401)
  ·
    refine ⟨10844509174138069968410551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14459345565517426624547401 10844509174138069968410551)
    ·
      refine ⟨16266763761207104952615827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10844509174138069968410551 16266763761207104952615827)
      ·
        refine ⟨24400145641810657428923741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16266763761207104952615827 24400145641810657428923741)
        ·
          refine ⟨9150054615678996535846403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24400145641810657428923741 9150054615678996535846403)
          ·
            refine ⟨13725081923518494803769605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150054615678996535846403 13725081923518494803769605)
            ·
              refine ⟨2573452860659717775706801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13725081923518494803769605 2573452860659717775706801)
              ·
                refine ⟨1930089645494788331780101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573452860659717775706801 1930089645494788331780101)
                ·
                  refine ⟨361891808530272812208769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930089645494788331780101 361891808530272812208769)
                  ·
                    rfl

theorem cell22_3171518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_3171518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171518 prefixEnd_3171518 := by exact prefixLift 3171518
  have htrace : WordTrace (prefixWord ++ tailWord_3171518) baseStart_3171518 baseEnd_3171518 := by
    simpa [prefixWord, tailWord_3171518, baseEnd_3171518] using wordTrace_append hprefix tailTrace_3171518
  have hstable : (prefixWord ++ tailWord_3171518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171518).length < 2 ^ (prefixWord ++ tailWord_3171518).sum := by decide
  have hdescent : baseEnd_3171518 < baseStart_3171518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171621 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_3171621 : Nat := 118140960795 + 3171621 * 2 ^ 59
def prefixEnd_3171621 : Nat := 4983230072969 + 3 ^ 40 * 3171621 * 2
def baseEnd_3171621 : Nat := 1085710684595760501300991

theorem tailTrace_3171621 : CollatzResearch.WordTrace tailWord_3171621 prefixEnd_3171621 1085710684595760501300991 := by
  unfold tailWord_3171621
  simp only [CollatzResearch.WordTrace]
  refine ⟨115678521242766261587378717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77119014161844174391585811 115678521242766261587378717)
  ·
    refine ⟨43379445466037348095267019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115678521242766261587378717 43379445466037348095267019)
    ·
      refine ⟨65069168199056022142900529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43379445466037348095267019 65069168199056022142900529)
      ·
        refine ⟨48801876149292016607175397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65069168199056022142900529 48801876149292016607175397)
        ·
          refine ⟨9150351777992253113845387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48801876149292016607175397 9150351777992253113845387)
          ·
            refine ⟨13725527666988379670768081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150351777992253113845387 13725527666988379670768081)
            ·
              refine ⟨10294145750241284753076061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13725527666988379670768081 10294145750241284753076061)
              ·
                refine ⟨3860304656340481782403523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10294145750241284753076061 3860304656340481782403523)
                ·
                  refine ⟨5790456984510722673605285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860304656340481782403523 5790456984510722673605285)
                  ·
                    refine ⟨1085710684595760501300991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790456984510722673605285 1085710684595760501300991)
                    ·
                      rfl

theorem cell22_3171621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_3171621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171621 prefixEnd_3171621 := by exact prefixLift 3171621
  have htrace : WordTrace (prefixWord ++ tailWord_3171621) baseStart_3171621 baseEnd_3171621 := by
    simpa [prefixWord, tailWord_3171621, baseEnd_3171621] using wordTrace_append hprefix tailTrace_3171621
  have hstable : (prefixWord ++ tailWord_3171621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171621).length < 2 ^ (prefixWord ++ tailWord_3171621).sum := by decide
  have hdescent : baseEnd_3171621 < baseStart_3171621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171687 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 4]
def baseStart_3171687 : Nat := 118140960795 + 3171687 * 2 ^ 59
def prefixEnd_3171687 : Nat := 4983230072969 + 3 ^ 40 * 3171687 * 2
def baseEnd_3171687 : Nat := 361911092581519443050263

theorem tailTrace_3171687 : CollatzResearch.WordTrace tailWord_3171687 prefixEnd_3171687 361911092581519443050263 := by
  unfold tailWord_3171687
  simp only [CollatzResearch.WordTrace]
  refine ⟨115680928460527154859281315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77120618973684769906187543 115680928460527154859281315)
  ·
    refine ⟨173521392690790732288921973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115680928460527154859281315 173521392690790732288921973)
    ·
      refine ⟨16267630564761631152086435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173521392690790732288921973 16267630564761631152086435)
      ·
        refine ⟨24401445847142446728129653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16267630564761631152086435 24401445847142446728129653)
        ·
          refine ⟨2287635548169604380762155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24401445847142446728129653 2287635548169604380762155)
          ·
            refine ⟨3431453322254406571143233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287635548169604380762155 3431453322254406571143233)
            ·
              refine ⟨2573589991690804928357425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431453322254406571143233 2573589991690804928357425)
              ·
                refine ⟨1930192493768103696268069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573589991690804928357425 1930192493768103696268069)
                ·
                  refine ⟨361911092581519443050263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930192493768103696268069 361911092581519443050263)
                  ·
                    rfl

theorem cell22_3171687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 4].length) (baseStart_3171687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171687 prefixEnd_3171687 := by exact prefixLift 3171687
  have htrace : WordTrace (prefixWord ++ tailWord_3171687) baseStart_3171687 baseEnd_3171687 := by
    simpa [prefixWord, tailWord_3171687, baseEnd_3171687] using wordTrace_append hprefix tailTrace_3171687
  have hstable : (prefixWord ++ tailWord_3171687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171687).length < 2 ^ (prefixWord ++ tailWord_3171687).sum := by decide
  have hdescent : baseEnd_3171687 < baseStart_3171687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171696 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_3171696 : Nat := 118140960795 + 3171696 * 2 ^ 59
def prefixEnd_3171696 : Nat := 4983230072969 + 3 ^ 40 * 3171696 * 2
def baseEnd_3171696 : Nat := 1085736358628485305675761

theorem tailTrace_3171696 : CollatzResearch.WordTrace tailWord_3171696 prefixEnd_3171696 1085736358628485305675761 := by
  unfold tailWord_3171696
  simp only [CollatzResearch.WordTrace]
  refine ⟨57840628358747274698179471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77120837811663032930905961 57840628358747274698179471)
  ·
    refine ⟨86760942538120912047269207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57840628358747274698179471 86760942538120912047269207)
    ·
      refine ⟨130141413807181368070903811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86760942538120912047269207 130141413807181368070903811)
      ·
        refine ⟨195212120710772052106355717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130141413807181368070903811 195212120710772052106355717)
        ·
          refine ⟨36602272633269759769941697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195212120710772052106355717 36602272633269759769941697)
          ·
            refine ⟨27451704474952319827456273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36602272633269759769941697 27451704474952319827456273)
            ·
              refine ⟨20588778356214239870592205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27451704474952319827456273 20588778356214239870592205)
              ·
                refine ⟨7720791883580339951472077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20588778356214239870592205 7720791883580339951472077)
                ·
                  refine ⟨2895296956342627481802029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7720791883580339951472077 2895296956342627481802029)
                  ·
                    refine ⟨1085736358628485305675761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895296956342627481802029 1085736358628485305675761)
                    ·
                      rfl

theorem cell22_3171696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_3171696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171696 prefixEnd_3171696 := by exact prefixLift 3171696
  have htrace : WordTrace (prefixWord ++ tailWord_3171696) baseStart_3171696 baseEnd_3171696 := by
    simpa [prefixWord, tailWord_3171696, baseEnd_3171696] using wordTrace_append hprefix tailTrace_3171696
  have hstable : (prefixWord ++ tailWord_3171696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171696).length < 2 ^ (prefixWord ++ tailWord_3171696).sum := by decide
  have hdescent : baseEnd_3171696 < baseStart_3171696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171724 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_3171724 : Nat := 118140960795 + 3171724 * 2 ^ 59
def prefixEnd_3171724 : Nat := 4983230072969 + 3 ^ 40 * 3171724 * 2
def baseEnd_3171724 : Nat := 1085745943600702565975675

theorem tailTrace_3171724 : CollatzResearch.WordTrace tailWord_3171724 prefixEnd_3171724 1085745943600702565975675 := by
  unfold tailWord_3171724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57841138980696555089189113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77121518640928740118918817 57841138980696555089189113)
  ·
    refine ⟨43380854235522416316891835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57841138980696555089189113 43380854235522416316891835)
    ·
      refine ⟨65071281353283624475337753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43380854235522416316891835 65071281353283624475337753)
      ·
        refine ⟨48803461014962718356503315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65071281353283624475337753 48803461014962718356503315)
        ·
          refine ⟨73205191522444077534754973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48803461014962718356503315 73205191522444077534754973)
          ·
            refine ⟨27451946820916529075533115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73205191522444077534754973 27451946820916529075533115)
            ·
              refine ⟨41177920231374793613299673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27451946820916529075533115 41177920231374793613299673)
              ·
                refine ⟨30883440173531095209974755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41177920231374793613299673 30883440173531095209974755)
                ·
                  refine ⟨46325160260296642814962133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30883440173531095209974755 46325160260296642814962133)
                  ·
                    refine ⟨1085745943600702565975675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46325160260296642814962133 1085745943600702565975675)
                    ·
                      rfl

theorem cell22_3171724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_3171724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171724 prefixEnd_3171724 := by exact prefixLift 3171724
  have htrace : WordTrace (prefixWord ++ tailWord_3171724) baseStart_3171724 baseEnd_3171724 := by
    simpa [prefixWord, tailWord_3171724, baseEnd_3171724] using wordTrace_append hprefix tailTrace_3171724
  have hstable : (prefixWord ++ tailWord_3171724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171724).length < 2 ^ (prefixWord ++ tailWord_3171724).sum := by decide
  have hdescent : baseEnd_3171724 < baseStart_3171724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171741 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3171741 : Nat := 118140960795 + 3171741 * 2 ^ 59
def prefixEnd_3171741 : Nat := 4983230072969 + 3 ^ 40 * 3171741 * 2
def baseEnd_3171741 : Nat := 1085751763048120188300623

theorem tailTrace_3171741 : CollatzResearch.WordTrace tailWord_3171741 prefixEnd_3171741 1085751763048120188300623 := by
  unfold tailWord_3171741
  simp only [CollatzResearch.WordTrace]
  refine ⟨115682898002331522081747077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77121932001554348054498051 115682898002331522081747077)
  ·
    refine ⟨21690543375437160390327577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115682898002331522081747077 21690543375437160390327577)
    ·
      refine ⟨16267907531577870292745683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21690543375437160390327577 16267907531577870292745683)
      ·
        refine ⟨24401861297366805439118525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16267907531577870292745683 24401861297366805439118525)
        ·
          refine ⟨9150697986512552039669447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24401861297366805439118525 9150697986512552039669447)
          ·
            refine ⟨13726046979768828059504171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150697986512552039669447 13726046979768828059504171)
            ·
              refine ⟨20589070469653242089256257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13726046979768828059504171 20589070469653242089256257)
              ·
                refine ⟨15441802852239931566942193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20589070469653242089256257 15441802852239931566942193)
                ·
                  refine ⟨11581352139179948675206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15441802852239931566942193 11581352139179948675206645)
                  ·
                    refine ⟨1085751763048120188300623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11581352139179948675206645 1085751763048120188300623)
                    ·
                      rfl

theorem cell22_3171741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3171741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171741 prefixEnd_3171741 := by exact prefixLift 3171741
  have htrace : WordTrace (prefixWord ++ tailWord_3171741) baseStart_3171741 baseEnd_3171741 := by
    simpa [prefixWord, tailWord_3171741, baseEnd_3171741] using wordTrace_append hprefix tailTrace_3171741
  have hstable : (prefixWord ++ tailWord_3171741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171741).length < 2 ^ (prefixWord ++ tailWord_3171741).sum := by decide
  have hdescent : baseEnd_3171741 < baseStart_3171741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171743 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 5]
def baseStart_3171743 : Nat := 118140960795 + 3171743 * 2 ^ 59
def prefixEnd_3171743 : Nat := 4983230072969 + 3 ^ 40 * 3171743 * 2
def baseEnd_3171743 : Nat := 361917482562997616583539

theorem tailTrace_3171743 : CollatzResearch.WordTrace tailWord_3171743 prefixEnd_3171743 361917482562997616583539 := by
  unfold tailWord_3171743
  simp only [CollatzResearch.WordTrace]
  refine ⟨115682970948324276423319883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77121980632216184282213255 115682970948324276423319883)
  ·
    refine ⟨173524456422486414634979825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115682970948324276423319883 173524456422486414634979825)
    ·
      refine ⟨130143342316864810976234869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173524456422486414634979825 130143342316864810976234869)
      ·
        refine ⟨12200938342206076029022019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130143342316864810976234869 12200938342206076029022019)
        ·
          refine ⟨18301407513309114043533029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12200938342206076029022019 18301407513309114043533029)
          ·
            refine ⟨3431513908745458883162443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18301407513309114043533029 3431513908745458883162443)
            ·
              refine ⟨5147270863118188324743665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431513908745458883162443 5147270863118188324743665)
              ·
                refine ⟨3860453147338641243557749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5147270863118188324743665 3860453147338641243557749)
                ·
                  refine ⟨361917482562997616583539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3860453147338641243557749 361917482562997616583539)
                  ·
                    rfl

theorem cell22_3171743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 5].length) (baseStart_3171743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171743 prefixEnd_3171743 := by exact prefixLift 3171743
  have htrace : WordTrace (prefixWord ++ tailWord_3171743) baseStart_3171743 baseEnd_3171743 := by
    simpa [prefixWord, tailWord_3171743, baseEnd_3171743] using wordTrace_append hprefix tailTrace_3171743
  have hstable : (prefixWord ++ tailWord_3171743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171743).length < 2 ^ (prefixWord ++ tailWord_3171743).sum := by decide
  have hdescent : baseEnd_3171743 < baseStart_3171743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171773 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_3171773 : Nat := 118140960795 + 3171773 * 2 ^ 59
def prefixEnd_3171773 : Nat := 4983230072969 + 3 ^ 40 * 3171773 * 2
def baseEnd_3171773 : Nat := 1085762717302082771500525

theorem tailTrace_3171773 : CollatzResearch.WordTrace tailWord_3171773 prefixEnd_3171773 1085762717302082771500525 := by
  unfold tailWord_3171773
  simp only [CollatzResearch.WordTrace]
  refine ⟨115684065138215591546911973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77122710092143727697941315 115684065138215591546911973)
  ·
    refine ⟨21690762213415423415045995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115684065138215591546911973 21690762213415423415045995)
    ·
      refine ⟨32536143320123135122568993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21690762213415423415045995 32536143320123135122568993)
      ·
        refine ⟨24402107490092351341926745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32536143320123135122568993 24402107490092351341926745)
        ·
          refine ⟨18301580617569263506445059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24402107490092351341926745 18301580617569263506445059)
          ·
            refine ⟨27452370926353895259667589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18301580617569263506445059 27452370926353895259667589)
            ·
              refine ⟨5147319548691355361187673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27452370926353895259667589 5147319548691355361187673)
              ·
                refine ⟨3860489661518516520890755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5147319548691355361187673 3860489661518516520890755)
                ·
                  refine ⟨5790734492277774781336133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860489661518516520890755 5790734492277774781336133)
                  ·
                    refine ⟨1085762717302082771500525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790734492277774781336133 1085762717302082771500525)
                    ·
                      rfl

theorem cell22_3171773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_3171773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171773 prefixEnd_3171773 := by exact prefixLift 3171773
  have htrace : WordTrace (prefixWord ++ tailWord_3171773) baseStart_3171773 baseEnd_3171773 := by
    simpa [prefixWord, tailWord_3171773, baseEnd_3171773] using wordTrace_append hprefix tailTrace_3171773
  have hstable : (prefixWord ++ tailWord_3171773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171773).length < 2 ^ (prefixWord ++ tailWord_3171773).sum := by decide
  have hdescent : baseEnd_3171773 < baseStart_3171773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171801 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_3171801 : Nat := 118140960795 + 3171801 * 2 ^ 59
def prefixEnd_3171801 : Nat := 4983230072969 + 3 ^ 40 * 3171801 * 2
def baseEnd_3171801 : Nat := 1085772302274300031800439

theorem tailTrace_3171801 : CollatzResearch.WordTrace tailWord_3171801 prefixEnd_3171801 1085772302274300031800439 := by
  unfold tailWord_3171801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115685086382114152328931257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77123390921409434885954171 115685086382114152328931257)
  ·
    refine ⟨86763814786585614246698443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115685086382114152328931257 86763814786585614246698443)
    ·
      refine ⟨130145722179878421370047665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86763814786585614246698443 130145722179878421370047665)
      ·
        refine ⟨97609291634908816027535749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130145722179878421370047665 97609291634908816027535749)
        ·
          refine ⟨18301742181545403005162953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97609291634908816027535749 18301742181545403005162953)
          ·
            refine ⟨13726306636159052253872215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18301742181545403005162953 13726306636159052253872215)
            ·
              refine ⟨20589459954238578380808323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13726306636159052253872215 20589459954238578380808323)
              ·
                refine ⟨30884189931357867571212485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20589459954238578380808323 30884189931357867571212485)
                ·
                  refine ⟨5790785612129600169602341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30884189931357867571212485 5790785612129600169602341)
                  ·
                    refine ⟨1085772302274300031800439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790785612129600169602341 1085772302274300031800439)
                    ·
                      rfl

theorem cell22_3171801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_3171801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171801 prefixEnd_3171801 := by exact prefixLift 3171801
  have htrace : WordTrace (prefixWord ++ tailWord_3171801) baseStart_3171801 baseEnd_3171801 := by
    simpa [prefixWord, tailWord_3171801, baseEnd_3171801] using wordTrace_append hprefix tailTrace_3171801
  have hstable : (prefixWord ++ tailWord_3171801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171801).length < 2 ^ (prefixWord ++ tailWord_3171801).sum := by decide
  have hdescent : baseEnd_3171801 < baseStart_3171801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171816 : List Nat := [2, 1, 4, 1, 1, 2, 4, 7]
def baseStart_3171816 : Nat := 118140960795 + 3171816 * 2 ^ 59
def prefixEnd_3171816 : Nat := 4983230072969 + 3 ^ 40 * 3171816 * 2
def baseEnd_3171816 : Nat := 120641937453427221408377

theorem tailTrace_3171816 : CollatzResearch.WordTrace tailWord_3171816 prefixEnd_3171816 120641937453427221408377 := by
  unfold tailWord_3171816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57842816738529904945363651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77123755651373206593818201 57842816738529904945363651)
  ·
    refine ⟨86764225107794857418045477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57842816738529904945363651 86764225107794857418045477)
    ·
      refine ⟨16268292207711535765883527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86764225107794857418045477 16268292207711535765883527)
      ·
        refine ⟨24402438311567303648825291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16268292207711535765883527 24402438311567303648825291)
        ·
          refine ⟨36603657467350955473237937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24402438311567303648825291 36603657467350955473237937)
          ·
            refine ⟨27452743100513216604928453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36603657467350955473237937 27452743100513216604928453)
            ·
              refine ⟨5147389331346228113424085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27452743100513216604928453 5147389331346228113424085)
              ·
                refine ⟨120641937453427221408377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5147389331346228113424085 120641937453427221408377)
                ·
                  rfl

theorem cell22_3171816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_3171816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171816 prefixEnd_3171816 := by exact prefixLift 3171816
  have htrace : WordTrace (prefixWord ++ tailWord_3171816) baseStart_3171816 baseEnd_3171816 := by
    simpa [prefixWord, tailWord_3171816, baseEnd_3171816] using wordTrace_append hprefix tailTrace_3171816
  have hstable : (prefixWord ++ tailWord_3171816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171816).length < 2 ^ (prefixWord ++ tailWord_3171816).sum := by decide
  have hdescent : baseEnd_3171816 < baseStart_3171816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171957 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 4]
def baseStart_3171957 : Nat := 118140960795 + 3171957 * 2 ^ 59
def prefixEnd_3171957 : Nat := 4983230072969 + 3 ^ 40 * 3171957 * 2
def baseEnd_3171957 : Nat := 361941901420789208299987

theorem tailTrace_3171957 : CollatzResearch.WordTrace tailWord_3171957 prefixEnd_3171957 361941901420789208299987 := by
  unfold tailWord_3171957
  simp only [CollatzResearch.WordTrace]
  refine ⟨115690776169548990971610125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77127184113032660647740083 115690776169548990971610125)
  ·
    refine ⟨43384041063580871614353797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115690776169548990971610125 43384041063580871614353797)
    ·
      refine ⟨8134507699421413427691337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43384041063580871614353797 8134507699421413427691337)
      ·
        refine ⟨6100880774566060070768503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8134507699421413427691337 6100880774566060070768503)
        ·
          refine ⟨9151321161849090106152755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100880774566060070768503 9151321161849090106152755)
          ·
            refine ⟨13726981742773635159229133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151321161849090106152755 13726981742773635159229133)
            ·
              refine ⟨5147618153540113184710925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13726981742773635159229133 5147618153540113184710925)
              ·
                refine ⟨1930356807577542444266597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5147618153540113184710925 1930356807577542444266597)
                ·
                  refine ⟨361941901420789208299987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930356807577542444266597 361941901420789208299987)
                  ·
                    rfl

theorem cell22_3171957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_3171957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3171957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3171957 prefixEnd_3171957 := by exact prefixLift 3171957
  have htrace : WordTrace (prefixWord ++ tailWord_3171957) baseStart_3171957 baseEnd_3171957 := by
    simpa [prefixWord, tailWord_3171957, baseEnd_3171957] using wordTrace_append hprefix tailTrace_3171957
  have hstable : (prefixWord ++ tailWord_3171957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171957).length < 2 ^ (prefixWord ++ tailWord_3171957).sum := by decide
  have hdescent : baseEnd_3171957 < baseStart_3171957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172030 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3172030 : Nat := 118140960795 + 3172030 * 2 ^ 59
def prefixEnd_3172030 : Nat := 4983230072969 + 3 ^ 40 * 3172030 * 2
def baseEnd_3172030 : Nat := 361950231218073255941579

theorem tailTrace_3172030 : CollatzResearch.WordTrace tailWord_3172030 prefixEnd_3172030 361950231218073255941579 := by
  unfold tailWord_3172030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461679837285565554877193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77128959132189682959345029 14461679837285565554877193)
  ·
    refine ⟨10846259877964174166157895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14461679837285565554877193 10846259877964174166157895)
    ·
      refine ⟨16269389816946261249236843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10846259877964174166157895 16269389816946261249236843)
      ·
        refine ⟨24404084725419391873855265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16269389816946261249236843 24404084725419391873855265)
        ·
          refine ⟨18303063544064543905391449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24404084725419391873855265 18303063544064543905391449)
          ·
            refine ⟨13727297658048407929043587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18303063544064543905391449 13727297658048407929043587)
            ·
              refine ⟨20590946487072611893565381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13727297658048407929043587 20590946487072611893565381)
              ·
                refine ⟨3860802466326114730043509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20590946487072611893565381 3860802466326114730043509)
                ·
                  refine ⟨361950231218073255941579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3860802466326114730043509 361950231218073255941579)
                  ·
                    rfl

theorem cell22_3172030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3172030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172030 prefixEnd_3172030 := by exact prefixLift 3172030
  have htrace : WordTrace (prefixWord ++ tailWord_3172030) baseStart_3172030 baseEnd_3172030 := by
    simpa [prefixWord, tailWord_3172030, baseEnd_3172030] using wordTrace_append hprefix tailTrace_3172030
  have hstable : (prefixWord ++ tailWord_3172030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172030).length < 2 ^ (prefixWord ++ tailWord_3172030).sum := by decide
  have hdescent : baseEnd_3172030 < baseStart_3172030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172058 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_3172058 : Nat := 118140960795 + 3172058 * 2 ^ 59
def prefixEnd_3172058 : Nat := 4983230072969 + 3 ^ 40 * 3172058 * 2
def baseEnd_3172058 : Nat := 361953426208812342708217

theorem tailTrace_3172058 : CollatzResearch.WordTrace tailWord_3172058 prefixEnd_3172058 361953426208812342708217 := by
  unfold tailWord_3172058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28923614985545771305259207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77129639961455390147357885 28923614985545771305259207)
  ·
    refine ⟨43385422478318656957888811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28923614985545771305259207 43385422478318656957888811)
    ·
      refine ⟨65078133717477985436833217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43385422478318656957888811 65078133717477985436833217)
      ·
        refine ⟨48808600288108489077624913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65078133717477985436833217 48808600288108489077624913)
        ·
          refine ⟨36606450216081366808218685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48808600288108489077624913 36606450216081366808218685)
          ·
            refine ⟨13727418831030512553082007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36606450216081366808218685 13727418831030512553082007)
            ·
              refine ⟨20591128246545768829623011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13727418831030512553082007 20591128246545768829623011)
              ·
                refine ⟨30886692369818653244434517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20591128246545768829623011 30886692369818653244434517)
                ·
                  refine ⟨361953426208812342708217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30886692369818653244434517 361953426208812342708217)
                  ·
                    rfl

theorem cell22_3172058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_3172058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172058 prefixEnd_3172058 := by exact prefixLift 3172058
  have htrace : WordTrace (prefixWord ++ tailWord_3172058) baseStart_3172058 baseEnd_3172058 := by
    simpa [prefixWord, tailWord_3172058, baseEnd_3172058] using wordTrace_append hprefix tailTrace_3172058
  have hstable : (prefixWord ++ tailWord_3172058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172058).length < 2 ^ (prefixWord ++ tailWord_3172058).sum := by decide
  have hdescent : baseEnd_3172058 < baseStart_3172058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172075 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 4]
def baseStart_3172075 : Nat := 118140960795 + 3172075 * 2 ^ 59
def prefixEnd_3172075 : Nat := 4983230072969 + 3 ^ 40 * 3172075 * 2
def baseEnd_3172075 : Nat := 361955366024618216816533

theorem tailTrace_3172075 : CollatzResearch.WordTrace tailWord_3172075 prefixEnd_3172075 361955366024618216816533 := by
  unfold tailWord_3172075
  simp only [CollatzResearch.WordTrace]
  refine ⟨115695079983121497124405679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77130053322080998082937119 115695079983121497124405679)
  ·
    refine ⟨173542619974682245686608519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115695079983121497124405679 173542619974682245686608519)
    ·
      refine ⟨260313929962023368529912779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173542619974682245686608519 260313929962023368529912779)
      ·
        refine ⟨390470894943035052794869169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260313929962023368529912779 390470894943035052794869169)
        ·
          refine ⟨292853171207276289596151877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390470894943035052794869169 292853171207276289596151877)
          ·
            refine ⟨54909969601364304299278477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292853171207276289596151877 54909969601364304299278477)
            ·
              refine ⟨20591238600511614112229429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54909969601364304299278477 20591238600511614112229429)
              ·
                refine ⟨1930428618797963823021509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20591238600511614112229429 1930428618797963823021509)
                ·
                  refine ⟨361955366024618216816533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930428618797963823021509 361955366024618216816533)
                  ·
                    rfl

theorem cell22_3172075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 4].length) (baseStart_3172075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172075 prefixEnd_3172075 := by exact prefixLift 3172075
  have htrace : WordTrace (prefixWord ++ tailWord_3172075) baseStart_3172075 baseEnd_3172075 := by
    simpa [prefixWord, tailWord_3172075, baseEnd_3172075] using wordTrace_append hprefix tailTrace_3172075
  have hstable : (prefixWord ++ tailWord_3172075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172075).length < 2 ^ (prefixWord ++ tailWord_3172075).sum := by decide
  have hdescent : baseEnd_3172075 < baseStart_3172075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172077 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3172077 : Nat := 118140960795 + 3172077 * 2 ^ 59
def prefixEnd_3172077 : Nat := 4983230072969 + 3 ^ 40 * 3172077 * 2
def baseEnd_3172077 : Nat := 1085866782714727311899593

theorem tailTrace_3172077 : CollatzResearch.WordTrace tailWord_3172077 prefixEnd_3172077 1085866782714727311899593 := by
  unfold tailWord_3172077
  simp only [CollatzResearch.WordTrace]
  refine ⟨115695152929114251465978485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77130101952742834310652323 115695152929114251465978485)
  ·
    refine ⟨10846420587104461074935483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115695152929114251465978485 10846420587104461074935483)
    ·
      refine ⟨16269630880656691612403225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10846420587104461074935483 16269630880656691612403225)
      ·
        refine ⟨12202223160492518709302419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16269630880656691612403225 12202223160492518709302419)
        ·
          refine ⟨18303334740738778063953629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12202223160492518709302419 18303334740738778063953629)
          ·
            refine ⟨6863750527777041773982611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18303334740738778063953629 6863750527777041773982611)
            ·
              refine ⟨10295625791665562660973917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863750527777041773982611 10295625791665562660973917)
              ·
                refine ⟨3860859671874585997865219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10295625791665562660973917 3860859671874585997865219)
                ·
                  refine ⟨5791289507811878996797829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860859671874585997865219 5791289507811878996797829)
                  ·
                    refine ⟨1085866782714727311899593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5791289507811878996797829 1085866782714727311899593)
                    ·
                      rfl

theorem cell22_3172077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3172077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172077 prefixEnd_3172077 := by exact prefixLift 3172077
  have htrace : WordTrace (prefixWord ++ tailWord_3172077) baseStart_3172077 baseEnd_3172077 := by
    simpa [prefixWord, tailWord_3172077, baseEnd_3172077] using wordTrace_append hprefix tailTrace_3172077
  have hstable : (prefixWord ++ tailWord_3172077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172077).length < 2 ^ (prefixWord ++ tailWord_3172077).sum := by decide
  have hdescent : baseEnd_3172077 < baseStart_3172077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172120 : List Nat := [2, 1, 2, 3, 1, 1, 6, 6]
def baseStart_3172120 : Nat := 118140960795 + 3172120 * 2 ^ 59
def prefixEnd_3172120 : Nat := 4983230072969 + 3 ^ 40 * 3172120 * 2
def baseEnd_3172120 : Nat := 120653500277054392563829

theorem tailTrace_3172120 : CollatzResearch.WordTrace tailWord_3172120 prefixEnd_3172120 120653500277054392563829 := by
  unfold tailWord_3172120
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848360633979234904896907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77131147511972313206529209 57848360633979234904896907)
  ·
    refine ⟨86772540950968852357345361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57848360633979234904896907 86772540950968852357345361)
    ·
      refine ⟨65079405713226639268009021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86772540950968852357345361 65079405713226639268009021)
      ·
        refine ⟨24404777142459989725503383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65079405713226639268009021 24404777142459989725503383)
        ·
          refine ⟨36607165713689984588255075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24404777142459989725503383 36607165713689984588255075)
          ·
            refine ⟨54910748570534976882382613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36607165713689984588255075 54910748570534976882382613)
            ·
              refine ⟨2573941339243827041361685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54910748570534976882382613 2573941339243827041361685)
              ·
                refine ⟨120653500277054392563829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2573941339243827041361685 120653500277054392563829)
                ·
                  rfl

theorem cell22_3172120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_3172120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172120 prefixEnd_3172120 := by exact prefixLift 3172120
  have htrace : WordTrace (prefixWord ++ tailWord_3172120) baseStart_3172120 baseEnd_3172120 := by
    simpa [prefixWord, tailWord_3172120, baseEnd_3172120] using wordTrace_append hprefix tailTrace_3172120
  have hstable : (prefixWord ++ tailWord_3172120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172120).length < 2 ^ (prefixWord ++ tailWord_3172120).sum := by decide
  have hdescent : baseEnd_3172120 < baseStart_3172120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172152 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_3172152 : Nat := 118140960795 + 3172152 * 2 ^ 59
def prefixEnd_3172152 : Nat := 4983230072969 + 3 ^ 40 * 3172152 * 2
def baseEnd_3172152 : Nat := 1085892456747452116274363

theorem tailTrace_3172152 : CollatzResearch.WordTrace tailWord_3172152 prefixEnd_3172152 1085892456747452116274363 := by
  unfold tailWord_3172152
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848944201921269637479355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77131925602561692849972473 57848944201921269637479355)
  ·
    refine ⟨86773416302881904456219033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57848944201921269637479355 86773416302881904456219033)
    ·
      refine ⟨65080062227161428342164275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86773416302881904456219033 65080062227161428342164275)
      ·
        refine ⟨97620093340742142513246413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65080062227161428342164275 97620093340742142513246413)
        ·
          refine ⟨36607535002778303442467405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97620093340742142513246413 36607535002778303442467405)
          ·
            refine ⟨13727825626041863790925277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36607535002778303442467405 13727825626041863790925277)
            ·
              refine ⟨5147934609765698921596979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13727825626041863790925277 5147934609765698921596979)
              ·
                refine ⟨7721901914648548382395469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147934609765698921596979 7721901914648548382395469)
                ·
                  refine ⟨2895713217993205643398301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7721901914648548382395469 2895713217993205643398301)
                  ·
                    refine ⟨1085892456747452116274363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895713217993205643398301 1085892456747452116274363)
                    ·
                      rfl

theorem cell22_3172152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_3172152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172152 prefixEnd_3172152 := by exact prefixLift 3172152
  have htrace : WordTrace (prefixWord ++ tailWord_3172152) baseStart_3172152 baseEnd_3172152 := by
    simpa [prefixWord, tailWord_3172152, baseEnd_3172152] using wordTrace_append hprefix tailTrace_3172152
  have hstable : (prefixWord ++ tailWord_3172152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172152).length < 2 ^ (prefixWord ++ tailWord_3172152).sum := by decide
  have hdescent : baseEnd_3172152 < baseStart_3172152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172165 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 5]
def baseStart_3172165 : Nat := 118140960795 + 3172165 * 2 ^ 59
def prefixEnd_3172165 : Nat := 4983230072969 + 3 ^ 40 * 3172165 * 2
def baseEnd_3172165 : Nat := 361965635637708138566441

theorem tailTrace_3172165 : CollatzResearch.WordTrace tailWord_3172165 prefixEnd_3172165 361965635637708138566441 := by
  unfold tailWord_3172165
  simp only [CollatzResearch.WordTrace]
  refine ⟨115698362552795442495181949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77132241701863628330121299 115698362552795442495181949)
  ·
    refine ⟨43386885957298290935693231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115698362552795442495181949 43386885957298290935693231)
    ·
      refine ⟨65080328935947436403539847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43386885957298290935693231 65080328935947436403539847)
      ·
        refine ⟨97620493403921154605309771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65080328935947436403539847 97620493403921154605309771)
        ·
          refine ⟨146430740105881731907964657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97620493403921154605309771 146430740105881731907964657)
          ·
            refine ⟨109823055079411298930973493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146430740105881731907964657 109823055079411298930973493)
            ·
              refine ⟨10295911413694809274778765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109823055079411298930973493 10295911413694809274778765)
              ·
                refine ⟨3860966780135553478042037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10295911413694809274778765 3860966780135553478042037)
                ·
                  refine ⟨361965635637708138566441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3860966780135553478042037 361965635637708138566441)
                  ·
                    rfl

theorem cell22_3172165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_3172165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172165 prefixEnd_3172165 := by exact prefixLift 3172165
  have htrace : WordTrace (prefixWord ++ tailWord_3172165) baseStart_3172165 baseEnd_3172165 := by
    simpa [prefixWord, tailWord_3172165, baseEnd_3172165] using wordTrace_append hprefix tailTrace_3172165
  have hstable : (prefixWord ++ tailWord_3172165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172165).length < 2 ^ (prefixWord ++ tailWord_3172165).sum := by decide
  have hdescent : baseEnd_3172165 < baseStart_3172165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172210 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3172210 : Nat := 118140960795 + 3172210 * 2 ^ 59
def prefixEnd_3172210 : Nat := 4983230072969 + 3 ^ 40 * 3172210 * 2
def baseEnd_3172210 : Nat := 361970770444253099441395

theorem tailTrace_3172210 : CollatzResearch.WordTrace tailWord_3172210 prefixEnd_3172210 361970770444253099441395 := by
  unfold tailWord_3172210
  simp only [CollatzResearch.WordTrace]
  refine ⟨28925000959408103795142521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77133335891754943453713389 28925000959408103795142521)
  ·
    refine ⟨21693750719556077846356891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28925000959408103795142521 21693750719556077846356891)
    ·
      refine ⟨32540626079334116769535337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21693750719556077846356891 32540626079334116769535337)
      ·
        refine ⟨24405469559500587577151503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32540626079334116769535337 24405469559500587577151503)
        ·
          refine ⟨36608204339250881365727255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24405469559500587577151503 36608204339250881365727255)
          ·
            refine ⟨54912306508876322048590883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36608204339250881365727255 54912306508876322048590883)
            ·
              refine ⟨82368459763314483072886325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54912306508876322048590883 82368459763314483072886325)
              ·
                refine ⟨7722043102810732788083093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82368459763314483072886325 7722043102810732788083093)
                ·
                  refine ⟨361970770444253099441395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7722043102810732788083093 361970770444253099441395)
                  ·
                    rfl

theorem cell22_3172210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3172210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172210 prefixEnd_3172210 := by exact prefixLift 3172210
  have htrace : WordTrace (prefixWord ++ tailWord_3172210) baseStart_3172210 baseEnd_3172210 := by
    simpa [prefixWord, tailWord_3172210, baseEnd_3172210] using wordTrace_append hprefix tailTrace_3172210
  have hstable : (prefixWord ++ tailWord_3172210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172210).length < 2 ^ (prefixWord ++ tailWord_3172210).sum := by decide
  have hdescent : baseEnd_3172210 < baseStart_3172210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172214 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3172214 : Nat := 118140960795 + 3172214 * 2 ^ 59
def prefixEnd_3172214 : Nat := 4983230072969 + 3 ^ 40 * 3172214 * 2
def baseEnd_3172214 : Nat := 1085913680614504621224173

theorem tailTrace_3172214 : CollatzResearch.WordTrace tailWord_3172214 prefixEnd_3172214 1085913680614504621224173 := by
  unfold tailWord_3172214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231259358101120241482231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77133433153078615909143797 7231259358101120241482231)
  ·
    refine ⟨10846889037151680362223347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7231259358101120241482231 10846889037151680362223347)
    ·
      refine ⟨16270333555727520543335021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10846889037151680362223347 16270333555727520543335021)
      ·
        refine ⟨6101375083397820203750633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16270333555727520543335021 6101375083397820203750633)
        ·
          refine ⟨4576031312548365152812975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101375083397820203750633 4576031312548365152812975)
          ·
            refine ⟨6864046968822547729219463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576031312548365152812975 6864046968822547729219463)
            ·
              refine ⟨10296070453233821593829195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864046968822547729219463 10296070453233821593829195)
              ·
                refine ⟨15444105679850732390743793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10296070453233821593829195 15444105679850732390743793)
                ·
                  refine ⟨11583079259888049293057845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15444105679850732390743793 11583079259888049293057845)
                  ·
                    refine ⟨1085913680614504621224173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11583079259888049293057845 1085913680614504621224173)
                    ·
                      rfl

theorem cell22_3172214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3172214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172214 prefixEnd_3172214 := by exact prefixLift 3172214
  have htrace : WordTrace (prefixWord ++ tailWord_3172214) baseStart_3172214 baseEnd_3172214 := by
    simpa [prefixWord, tailWord_3172214, baseEnd_3172214] using wordTrace_append hprefix tailTrace_3172214
  have hstable : (prefixWord ++ tailWord_3172214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172214).length < 2 ^ (prefixWord ++ tailWord_3172214).sum := by decide
  have hdescent : baseEnd_3172214 < baseStart_3172214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172244 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 4]
def baseStart_3172244 : Nat := 118140960795 + 3172244 * 2 ^ 59
def prefixEnd_3172244 : Nat := 4983230072969 + 3 ^ 40 * 3172244 * 2
def baseEnd_3172244 : Nat := 361974650075864847658027

theorem tailTrace_3172244 : CollatzResearch.WordTrace tailWord_3172244 prefixEnd_3172244 361974650075864847658027 := by
  unfold tailWord_3172244
  simp only [CollatzResearch.WordTrace]
  refine ⟨57850621959754619493653893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77134162613006159324871857 57850621959754619493653893)
  ·
    refine ⟨10846991617453991155060105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57850621959754619493653893 10846991617453991155060105)
    ·
      refine ⟨8135243713090493366295079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10846991617453991155060105 8135243713090493366295079)
      ·
        refine ⟨12202865569635740049442619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8135243713090493366295079 12202865569635740049442619)
        ·
          refine ⟨18304298354453610074163929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12202865569635740049442619 18304298354453610074163929)
          ·
            refine ⟨13728223765840207555622947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18304298354453610074163929 13728223765840207555622947)
            ·
              refine ⟨20592335648760311333434421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13728223765840207555622947 20592335648760311333434421)
              ·
                refine ⟨1930531467071279187509477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20592335648760311333434421 1930531467071279187509477)
                ·
                  refine ⟨361974650075864847658027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930531467071279187509477 361974650075864847658027)
                  ·
                    rfl

theorem cell22_3172244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3172244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172244 prefixEnd_3172244 := by exact prefixLift 3172244
  have htrace : WordTrace (prefixWord ++ tailWord_3172244) baseStart_3172244 baseEnd_3172244 := by
    simpa [prefixWord, tailWord_3172244, baseEnd_3172244] using wordTrace_append hprefix tailTrace_3172244
  have hstable : (prefixWord ++ tailWord_3172244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172244).length < 2 ^ (prefixWord ++ tailWord_3172244).sum := by decide
  have hdescent : baseEnd_3172244 < baseStart_3172244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172287 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 3, 3]
def baseStart_3172287 : Nat := 118140960795 + 3172287 * 2 ^ 59
def prefixEnd_3172287 : Nat := 4983230072969 + 3 ^ 40 * 3172287 * 2
def baseEnd_3172287 : Nat := 1085938670006356764148949

theorem tailTrace_3172287 : CollatzResearch.WordTrace tailWord_3172287 prefixEnd_3172287 1085938670006356764148949 := by
  unfold tailWord_3172287
  simp only [CollatzResearch.WordTrace]
  refine ⟨115702812258353457331123115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77135208172235638220748743 115702812258353457331123115)
  ·
    refine ⟨173554218387530185996684673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115702812258353457331123115 173554218387530185996684673)
    ·
      refine ⟨130165663790647639497513505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173554218387530185996684673 130165663790647639497513505)
      ·
        refine ⟨97624247842985729623135129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130165663790647639497513505 97624247842985729623135129)
        ·
          refine ⟨73218185882239297217351347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97624247842985729623135129 73218185882239297217351347)
          ·
            refine ⟨109827278823358945826027021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73218185882239297217351347 109827278823358945826027021)
            ·
              refine ⟨41185229558759604684760133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109827278823358945826027021 41185229558759604684760133)
              ·
                refine ⟨7722230542267425878392525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41185229558759604684760133 7722230542267425878392525)
                ·
                  refine ⟨2895836453350284704397197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7722230542267425878392525 2895836453350284704397197)
                  ·
                    refine ⟨1085938670006356764148949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895836453350284704397197 1085938670006356764148949)
                    ·
                      rfl

theorem cell22_3172287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_3172287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172287 prefixEnd_3172287 := by exact prefixLift 3172287
  have htrace : WordTrace (prefixWord ++ tailWord_3172287) baseStart_3172287 baseEnd_3172287 := by
    simpa [prefixWord, tailWord_3172287, baseEnd_3172287] using wordTrace_append hprefix tailTrace_3172287
  have hstable : (prefixWord ++ tailWord_3172287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172287).length < 2 ^ (prefixWord ++ tailWord_3172287).sum := by decide
  have hdescent : baseEnd_3172287 < baseStart_3172287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172334 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_3172334 : Nat := 118140960795 + 3172334 * 2 ^ 59
def prefixEnd_3172334 : Nat := 4983230072969 + 3 ^ 40 * 3172334 * 2
def baseEnd_3172334 : Nat := 361984919688954769407935

theorem tailTrace_3172334 : CollatzResearch.WordTrace tailWord_3172334 prefixEnd_3172334 361984919688954769407935 := by
  unfold tailWord_3172334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14463065811147898044760507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77136350992788789572056037 14463065811147898044760507)
  ·
    refine ⟨21694598716721847067140761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14463065811147898044760507 21694598716721847067140761)
    ·
      refine ⟨16270949037541385300355571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21694598716721847067140761 16270949037541385300355571)
      ·
        refine ⟨24406423556312077950533357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16270949037541385300355571 24406423556312077950533357)
        ·
          refine ⟨9152408833617029231450009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24406423556312077950533357 9152408833617029231450009)
          ·
            refine ⟨6864306625212771923587507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9152408833617029231450009 6864306625212771923587507)
            ·
              refine ⟨10296459937819157885381261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864306625212771923587507 10296459937819157885381261)
              ·
                refine ⟨3861172476682184207017973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10296459937819157885381261 3861172476682184207017973)
                ·
                  refine ⟨361984919688954769407935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3861172476682184207017973 361984919688954769407935)
                  ·
                    rfl

theorem cell22_3172334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_3172334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172334 prefixEnd_3172334 := by exact prefixLift 3172334
  have htrace : WordTrace (prefixWord ++ tailWord_3172334) baseStart_3172334 baseEnd_3172334 := by
    simpa [prefixWord, tailWord_3172334, baseEnd_3172334] using wordTrace_append hprefix tailTrace_3172334
  have hstable : (prefixWord ++ tailWord_3172334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172334).length < 2 ^ (prefixWord ++ tailWord_3172334).sum := by decide
  have hdescent : baseEnd_3172334 < baseStart_3172334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172394 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3172394 : Nat := 118140960795 + 3172394 * 2 ^ 59
def prefixEnd_3172394 : Nat := 4983230072969 + 3 ^ 40 * 3172394 * 2
def baseEnd_3172394 : Nat := 1085975298293044151723621

theorem tailTrace_3172394 : CollatzResearch.WordTrace tailWord_3172394 prefixEnd_3172394 1085975298293044151723621 := by
  unfold tailWord_3172394
  simp only [CollatzResearch.WordTrace]
  refine ⟨28926678717241453651317059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77137809912643876403512157 28926678717241453651317059)
  ·
    refine ⟨43390018075862180476975589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28926678717241453651317059 43390018075862180476975589)
    ·
      refine ⟨8135628389224158839432923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43390018075862180476975589 8135628389224158839432923)
      ·
        refine ⟨12203442583836238259149385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8135628389224158839432923 12203442583836238259149385)
        ·
          refine ⟨9152581937877178694362039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12203442583836238259149385 9152581937877178694362039)
          ·
            refine ⟨13728872906815768041543059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9152581937877178694362039 13728872906815768041543059)
            ·
              refine ⟨20593309360223652062314589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13728872906815768041543059 20593309360223652062314589)
              ·
                refine ⟨7722491010083869523367971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20593309360223652062314589 7722491010083869523367971)
                ·
                  refine ⟨11583736515125804285051957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7722491010083869523367971 11583736515125804285051957)
                  ·
                    refine ⟨1085975298293044151723621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11583736515125804285051957 1085975298293044151723621)
                    ·
                      rfl

theorem cell22_3172394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3172394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172394 prefixEnd_3172394 := by exact prefixLift 3172394
  have htrace : WordTrace (prefixWord ++ tailWord_3172394) baseStart_3172394 baseEnd_3172394 := by
    simpa [prefixWord, tailWord_3172394, baseEnd_3172394] using wordTrace_append hprefix tailTrace_3172394
  have hstable : (prefixWord ++ tailWord_3172394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172394).length < 2 ^ (prefixWord ++ tailWord_3172394).sum := by decide
  have hdescent : baseEnd_3172394 < baseStart_3172394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172409 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_3172409 : Nat := 118140960795 + 3172409 * 2 ^ 59
def prefixEnd_3172409 : Nat := 4983230072969 + 3 ^ 40 * 3172409 * 2
def baseEnd_3172409 : Nat := 1085980433099589112598575

theorem tailTrace_3172409 : CollatzResearch.WordTrace tailWord_3172409 prefixEnd_3172409 1085980433099589112598575 := by
  unfold tailWord_3172409
  simp only [CollatzResearch.WordTrace]
  refine ⟨115707261963911472167064281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77138174642607648111376187 115707261963911472167064281)
  ·
    refine ⟨86780446472933604125298211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115707261963911472167064281 86780446472933604125298211)
    ·
      refine ⟨130170669709400406187947317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86780446472933604125298211 130170669709400406187947317)
      ·
        refine ⟨12203500285256288080120061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130170669709400406187947317 12203500285256288080120061)
        ·
          refine ⟨4576312606971108030045023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12203500285256288080120061 4576312606971108030045023)
          ·
            refine ⟨6864468910456662045067535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576312606971108030045023 6864468910456662045067535)
            ·
              refine ⟨10296703365684993067601303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864468910456662045067535 10296703365684993067601303)
              ·
                refine ⟨15445055048527489601401955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10296703365684993067601303 15445055048527489601401955)
                ·
                  refine ⟨23167582572791234402102933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15445055048527489601401955 23167582572791234402102933)
                  ·
                    refine ⟨1085980433099589112598575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23167582572791234402102933 1085980433099589112598575)
                    ·
                      rfl

theorem cell22_3172409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_3172409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172409 prefixEnd_3172409 := by exact prefixLift 3172409
  have htrace : WordTrace (prefixWord ++ tailWord_3172409) baseStart_3172409 baseEnd_3172409 := by
    simpa [prefixWord, tailWord_3172409, baseEnd_3172409] using wordTrace_append hprefix tailTrace_3172409
  have hstable : (prefixWord ++ tailWord_3172409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172409).length < 2 ^ (prefixWord ++ tailWord_3172409).sum := by decide
  have hdescent : baseEnd_3172409 < baseStart_3172409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172439 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 3, 3]
def baseStart_3172439 : Nat := 118140960795 + 3172439 * 2 ^ 59
def prefixEnd_3172439 : Nat := 4983230072969 + 3 ^ 40 * 3172439 * 2
def baseEnd_3172439 : Nat := 1085990702712679034348483

theorem tailTrace_3172439 : CollatzResearch.WordTrace tailWord_3172439 prefixEnd_3172439 1085990702712679034348483 := by
  unfold tailWord_3172439
  simp only [CollatzResearch.WordTrace]
  refine ⟨115708356153802787290656371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77138904102535191527104247 115708356153802787290656371)
  ·
    refine ⟨173562534230704180935984557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115708356153802787290656371 173562534230704180935984557)
    ·
      refine ⟨65085950336514067850994209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173562534230704180935984557 65085950336514067850994209)
      ·
        refine ⟨48814462752385550888245657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65085950336514067850994209 48814462752385550888245657)
        ·
          refine ⟨36610847064289163166184243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48814462752385550888245657 36610847064289163166184243)
          ·
            refine ⟨54916270596433744749276365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36610847064289163166184243 54916270596433744749276365)
            ·
              refine ⟨20593601473662654280978637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54916270596433744749276365 20593601473662654280978637)
              ·
                refine ⟨7722600552623495355366989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20593601473662654280978637 7722600552623495355366989)
                ·
                  refine ⟨2895975207233810758262621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7722600552623495355366989 2895975207233810758262621)
                  ·
                    refine ⟨1085990702712679034348483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895975207233810758262621 1085990702712679034348483)
                    ·
                      rfl

theorem cell22_3172439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_3172439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172439 prefixEnd_3172439 := by exact prefixLift 3172439
  have htrace : WordTrace (prefixWord ++ tailWord_3172439) baseStart_3172439 baseEnd_3172439 := by
    simpa [prefixWord, tailWord_3172439, baseEnd_3172439] using wordTrace_append hprefix tailTrace_3172439
  have hstable : (prefixWord ++ tailWord_3172439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172439).length < 2 ^ (prefixWord ++ tailWord_3172439).sum := by decide
  have hdescent : baseEnd_3172439 < baseStart_3172439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172445 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3172445 : Nat := 118140960795 + 3172445 * 2 ^ 59
def prefixEnd_3172445 : Nat := 4983230072969 + 3 ^ 40 * 3172445 * 2
def baseEnd_3172445 : Nat := 1085992756635297018698465

theorem tailTrace_3172445 : CollatzResearch.WordTrace tailWord_3172445 prefixEnd_3172445 1085992756635297018698465 := by
  unfold tailWord_3172445
  simp only [CollatzResearch.WordTrace]
  refine ⟨115708574991781050315374789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77139049994520700210249859 115708574991781050315374789)
  ·
    refine ⟨21695357810958946934132773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115708574991781050315374789 21695357810958946934132773)
    ·
      refine ⟨4067879589554802550149895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21695357810958946934132773 4067879589554802550149895)
      ·
        refine ⟨6101819384332203825224843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067879589554802550149895 6101819384332203825224843)
        ·
          refine ⟨9152729076498305737837265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6101819384332203825224843 9152729076498305737837265)
          ·
            refine ⟨6864546807373729303377949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9152729076498305737837265 6864546807373729303377949)
            ·
              refine ⟨2574205052765148488766731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6864546807373729303377949 2574205052765148488766731)
              ·
                refine ⟨3861307579147722733150097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574205052765148488766731 3861307579147722733150097)
                ·
                  refine ⟨2895980684360792049862573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861307579147722733150097 2895980684360792049862573)
                  ·
                    refine ⟨1085992756635297018698465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895980684360792049862573 1085992756635297018698465)
                    ·
                      rfl

theorem cell22_3172445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3172445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172445 prefixEnd_3172445 := by exact prefixLift 3172445
  have htrace : WordTrace (prefixWord ++ tailWord_3172445) baseStart_3172445 baseEnd_3172445 := by
    simpa [prefixWord, tailWord_3172445, baseEnd_3172445] using wordTrace_append hprefix tailTrace_3172445
  have hstable : (prefixWord ++ tailWord_3172445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172445).length < 2 ^ (prefixWord ++ tailWord_3172445).sum := by decide
  have hdescent : baseEnd_3172445 < baseStart_3172445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172458 : List Nat := [3, 1, 3, 2, 4, 1, 2, 6]
def baseStart_3172458 : Nat := 118140960795 + 3172458 * 2 ^ 59
def prefixEnd_3172458 : Nat := 4983230072969 + 3 ^ 40 * 3172458 * 2
def baseEnd_3172458 : Nat := 120666356311218813124825

theorem tailTrace_3172458 : CollatzResearch.WordTrace tailWord_3172458 prefixEnd_3172458 120666356311218813124825 := by
  unfold tailWord_3172458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28927262285183488383899507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77139366093822635690398685 28927262285183488383899507)
  ·
    refine ⟨43390893427775232575849261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28927262285183488383899507 43390893427775232575849261)
    ·
      refine ⟨16271585035415712215943473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43390893427775232575849261 16271585035415712215943473)
      ·
        refine ⟨12203688776561784161957605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16271585035415712215943473 12203688776561784161957605)
        ·
          refine ⟨2288191645605334530367051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12203688776561784161957605 2288191645605334530367051)
          ·
            refine ⟨3432287468408001795550577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288191645605334530367051 3432287468408001795550577)
            ·
              refine ⟨2574215601306001346662933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432287468408001795550577 2574215601306001346662933)
              ·
                refine ⟨120666356311218813124825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2574215601306001346662933 120666356311218813124825)
                ·
                  rfl

theorem cell22_3172458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_3172458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172458 prefixEnd_3172458 := by exact prefixLift 3172458
  have htrace : WordTrace (prefixWord ++ tailWord_3172458) baseStart_3172458 baseEnd_3172458 := by
    simpa [prefixWord, tailWord_3172458, baseEnd_3172458] using wordTrace_append hprefix tailTrace_3172458
  have hstable : (prefixWord ++ tailWord_3172458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172458).length < 2 ^ (prefixWord ++ tailWord_3172458).sum := by decide
  have hdescent : baseEnd_3172458 < baseStart_3172458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172473 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 1, 3]
def baseStart_3172473 : Nat := 118140960795 + 3172473 * 2 ^ 59
def prefixEnd_3172473 : Nat := 4983230072969 + 3 ^ 40 * 3172473 * 2
def baseEnd_3172473 : Nat := 1086002341607514278998379

theorem tailTrace_3172473 : CollatzResearch.WordTrace tailWord_3172473 prefixEnd_3172473 1086002341607514278998379 := by
  unfold tailWord_3172473
  simp only [CollatzResearch.WordTrace]
  refine ⟨115709596235679611097394073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77139730823786407398262715 115709596235679611097394073)
  ·
    refine ⟨86782197176759708323045555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115709596235679611097394073 86782197176759708323045555)
    ·
      refine ⟨130173295765139562484568333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86782197176759708323045555 130173295765139562484568333)
      ·
        refine ⟨48814985911927335931713125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130173295765139562484568333 48814985911927335931713125)
        ·
          refine ⟨9152809858486375487196211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48814985911927335931713125 9152809858486375487196211)
          ·
            refine ⟨13729214787729563230794317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9152809858486375487196211 13729214787729563230794317)
            ·
              refine ⟨5148455545398586211547869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13729214787729563230794317 5148455545398586211547869)
              ·
                refine ⟨1930670829524469829330451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5148455545398586211547869 1930670829524469829330451)
                ·
                  refine ⟨2896006244286704743995677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930670829524469829330451 2896006244286704743995677)
                  ·
                    refine ⟨1086002341607514278998379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896006244286704743995677 1086002341607514278998379)
                    ·
                      rfl

theorem cell22_3172473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_3172473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172473 prefixEnd_3172473 := by exact prefixLift 3172473
  have htrace : WordTrace (prefixWord ++ tailWord_3172473) baseStart_3172473 baseEnd_3172473 := by
    simpa [prefixWord, tailWord_3172473, baseEnd_3172473] using wordTrace_append hprefix tailTrace_3172473
  have hstable : (prefixWord ++ tailWord_3172473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172473).length < 2 ^ (prefixWord ++ tailWord_3172473).sum := by decide
  have hdescent : baseEnd_3172473 < baseStart_3172473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172490 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_3172490 : Nat := 118140960795 + 3172490 * 2 ^ 59
def prefixEnd_3172490 : Nat := 4983230072969 + 3 ^ 40 * 3172490 * 2
def baseEnd_3172490 : Nat := 1086008161054931901323327

theorem tailTrace_3172490 : CollatzResearch.WordTrace tailWord_3172490 prefixEnd_3172490 1086008161054931901323327 := by
  unfold tailWord_3172490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28927554069154505750190731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77140144184412015333841949 28927554069154505750190731)
  ·
    refine ⟨43391331103731758625286097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28927554069154505750190731 43391331103731758625286097)
    ·
      refine ⟨32543498327798818968964573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43391331103731758625286097 32543498327798818968964573)
      ·
        refine ⟨12203811872924557113361715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32543498327798818968964573 12203811872924557113361715)
        ·
          refine ⟨18305717809386835670042573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12203811872924557113361715 18305717809386835670042573)
          ·
            refine ⟨6864644178520063376265965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18305717809386835670042573 6864644178520063376265965)
            ·
              refine ⟨2574241566945023766099737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6864644178520063376265965 2574241566945023766099737)
              ·
                refine ⟨1930681175208767824574803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574241566945023766099737 1930681175208767824574803)
                ·
                  refine ⟨2896021762813151736862205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930681175208767824574803 2896021762813151736862205)
                  ·
                    refine ⟨1086008161054931901323327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896021762813151736862205 1086008161054931901323327)
                    ·
                      rfl

theorem cell22_3172490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_3172490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172490 prefixEnd_3172490 := by exact prefixLift 3172490
  have htrace : WordTrace (prefixWord ++ tailWord_3172490) baseStart_3172490 baseEnd_3172490 := by
    simpa [prefixWord, tailWord_3172490, baseEnd_3172490] using wordTrace_append hprefix tailTrace_3172490
  have hstable : (prefixWord ++ tailWord_3172490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172490).length < 2 ^ (prefixWord ++ tailWord_3172490).sum := by decide
  have hdescent : baseEnd_3172490 < baseStart_3172490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172503 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 5]
def baseStart_3172503 : Nat := 118140960795 + 3172503 * 2 ^ 59
def prefixEnd_3172503 : Nat := 4983230072969 + 3 ^ 40 * 3172503 * 2
def baseEnd_3172503 : Nat := 362004203740201400249429

theorem tailTrace_3172503 : CollatzResearch.WordTrace tailWord_3172503 prefixEnd_3172503 362004203740201400249429 := by
  unfold tailWord_3172503
  simp only [CollatzResearch.WordTrace]
  refine ⟨115710690425570926220986163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77140460283713950813990775 115710690425570926220986163)
  ·
    refine ⟨173566035638356389331479245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115710690425570926220986163 173566035638356389331479245)
    ·
      refine ⟨65087263364383645999304717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173566035638356389331479245 65087263364383645999304717)
      ·
        refine ⟨24407723761643867249739269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65087263364383645999304717 24407723761643867249739269)
        ·
          refine ⟨4576448205308225109326113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24407723761643867249739269 4576448205308225109326113)
          ·
            refine ⟨3432336153981168831994585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4576448205308225109326113 3432336153981168831994585)
            ·
              refine ⟨2574252115485876623995939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432336153981168831994585 2574252115485876623995939)
              ·
                refine ⟨3861378173228814935993909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574252115485876623995939 3861378173228814935993909)
                ·
                  refine ⟨362004203740201400249429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3861378173228814935993909 362004203740201400249429)
                  ·
                    rfl

theorem cell22_3172503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 5].length) (baseStart_3172503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172503 prefixEnd_3172503 := by exact prefixLift 3172503
  have htrace : WordTrace (prefixWord ++ tailWord_3172503) baseStart_3172503 baseEnd_3172503 := by
    simpa [prefixWord, tailWord_3172503, baseEnd_3172503] using wordTrace_append hprefix tailTrace_3172503
  have hstable : (prefixWord ++ tailWord_3172503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172503).length < 2 ^ (prefixWord ++ tailWord_3172503).sum := by decide
  have hdescent : baseEnd_3172503 < baseStart_3172503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172516 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_3172516 : Nat := 118140960795 + 3172516 * 2 ^ 59
def prefixEnd_3172516 : Nat := 4983230072969 + 3 ^ 40 * 3172516 * 2
def baseEnd_3172516 : Nat := 1086017061386276500173247

theorem tailTrace_3172516 : CollatzResearch.WordTrace tailWord_3172516 prefixEnd_3172516 1086017061386276500173247 := by
  unfold tailWord_3172516
  simp only [CollatzResearch.WordTrace]
  refine ⟨57855582287261914720604701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77140776383015886294139601 57855582287261914720604701)
  ·
    refine ⟨21695843357723218020226763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57855582287261914720604701 21695843357723218020226763)
    ·
      refine ⟨32543765036584827030340145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21695843357723218020226763 32543765036584827030340145)
      ·
        refine ⟨24407823777438620272755109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32543765036584827030340145 24407823777438620272755109)
        ·
          refine ⟨4576466958269741301141583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24407823777438620272755109 4576466958269741301141583)
          ·
            refine ⟨6864700437404611951712375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576466958269741301141583 6864700437404611951712375)
            ·
              refine ⟨10297050656106917927568563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864700437404611951712375 10297050656106917927568563)
              ·
                refine ⟨15445575984160376891352845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10297050656106917927568563 15445575984160376891352845)
                ·
                  refine ⟨5792090994060141334257317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15445575984160376891352845 5792090994060141334257317)
                  ·
                    refine ⟨1086017061386276500173247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5792090994060141334257317 1086017061386276500173247)
                    ·
                      rfl

theorem cell22_3172516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_3172516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172516 prefixEnd_3172516 := by exact prefixLift 3172516
  have htrace : WordTrace (prefixWord ++ tailWord_3172516) baseStart_3172516 baseEnd_3172516 := by
    simpa [prefixWord, tailWord_3172516, baseEnd_3172516] using wordTrace_append hprefix tailTrace_3172516
  have hstable : (prefixWord ++ tailWord_3172516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172516).length < 2 ^ (prefixWord ++ tailWord_3172516).sum := by decide
  have hdescent : baseEnd_3172516 < baseStart_3172516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172548 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 4]
def baseStart_3172548 : Nat := 118140960795 + 3172548 * 2 ^ 59
def prefixEnd_3172548 : Nat := 4983230072969 + 3 ^ 40 * 3172548 * 2
def baseEnd_3172548 : Nat := 362009338546746361124383

theorem tailTrace_3172548 : CollatzResearch.WordTrace tailWord_3172548 prefixEnd_3172548 362009338546746361124383 := by
  unfold tailWord_3172548
  simp only [CollatzResearch.WordTrace]
  refine ⟨57856165855203949453187149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77141554473605265937582865 57856165855203949453187149)
  ·
    refine ⟨21696062195701481044945181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57856165855203949453187149 21696062195701481044945181)
    ·
      refine ⟨8136023323388055391854443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21696062195701481044945181 8136023323388055391854443)
      ·
        refine ⟨12204034985082083087781665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136023323388055391854443 12204034985082083087781665)
        ·
          refine ⟨9153026238811562315836249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12204034985082083087781665 9153026238811562315836249)
          ·
            refine ⟨6864769679108671736877187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9153026238811562315836249 6864769679108671736877187)
            ·
              refine ⟨10297154518663007605315781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864769679108671736877187 10297154518663007605315781)
              ·
                refine ⟨1930716472249313925996709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10297154518663007605315781 1930716472249313925996709)
                ·
                  refine ⟨362009338546746361124383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930716472249313925996709 362009338546746361124383)
                  ·
                    rfl

theorem cell22_3172548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_3172548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172548 prefixEnd_3172548 := by exact prefixLift 3172548
  have htrace : WordTrace (prefixWord ++ tailWord_3172548) baseStart_3172548 baseEnd_3172548 := by
    simpa [prefixWord, tailWord_3172548, baseEnd_3172548] using wordTrace_append hprefix tailTrace_3172548
  have hstable : (prefixWord ++ tailWord_3172548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172548).length < 2 ^ (prefixWord ++ tailWord_3172548).sum := by decide
  have hdescent : baseEnd_3172548 < baseStart_3172548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172608 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 1, 3]
def baseStart_3172608 : Nat := 118140960795 + 3172608 * 2 ^ 59
def prefixEnd_3172608 : Nat := 4983230072969 + 3 ^ 40 * 3172608 * 2
def baseEnd_3172608 : Nat := 1086048554866418926872965

theorem tailTrace_3172608 : CollatzResearch.WordTrace tailWord_3172608 prefixEnd_3172608 1086048554866418926872965 := by
  unfold tailWord_3172608
  simp only [CollatzResearch.WordTrace]
  refine ⟨57857260045095264576779239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77143013393460352769038985 57857260045095264576779239)
  ·
    refine ⟨86785890067642896865168859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57857260045095264576779239 86785890067642896865168859)
    ·
      refine ⟨130178835101464345297753289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86785890067642896865168859 130178835101464345297753289)
      ·
        refine ⟨97634126326098258973314967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130178835101464345297753289 97634126326098258973314967)
        ·
          refine ⟨146451189489147388459972451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97634126326098258973314967 146451189489147388459972451)
          ·
            refine ⟨219676784233721082689958677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146451189489147388459972451 219676784233721082689958677)
            ·
              refine ⟨10297349260955675751091813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219676784233721082689958677 10297349260955675751091813)
              ·
                refine ⟨1930752986429189203329715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10297349260955675751091813 1930752986429189203329715)
                ·
                  refine ⟨2896129479643783804994573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930752986429189203329715 2896129479643783804994573)
                  ·
                    refine ⟨1086048554866418926872965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896129479643783804994573 1086048554866418926872965)
                    ·
                      rfl

theorem cell22_3172608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_3172608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172608 prefixEnd_3172608 := by exact prefixLift 3172608
  have htrace : WordTrace (prefixWord ++ tailWord_3172608) baseStart_3172608 baseEnd_3172608 := by
    simpa [prefixWord, tailWord_3172608, baseEnd_3172608] using wordTrace_append hprefix tailTrace_3172608
  have hstable : (prefixWord ++ tailWord_3172608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172608).length < 2 ^ (prefixWord ++ tailWord_3172608).sum := by decide
  have hdescent : baseEnd_3172608 < baseStart_3172608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172619 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_3172619 : Nat := 118140960795 + 3172619 * 2 ^ 59
def prefixEnd_3172619 : Nat := 4983230072969 + 3 ^ 40 * 3172619 * 2
def baseEnd_3172619 : Nat := 1086052320391218564847931

theorem tailTrace_3172619 : CollatzResearch.WordTrace tailWord_3172619 prefixEnd_3172619 1086052320391218564847931 := by
  unfold tailWord_3172619
  simp only [CollatzResearch.WordTrace]
  refine ⟨115714921293150678032208911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77143280862100452021472607 115714921293150678032208911)
  ·
    refine ⟨173572381939726017048313367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115714921293150678032208911 173572381939726017048313367)
    ·
      refine ⟨260358572909589025572470051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173572381939726017048313367 260358572909589025572470051)
      ·
        refine ⟨390537859364383538358705077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260358572909589025572470051 390537859364383538358705077)
        ·
          refine ⟨36612924315410956721128601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390537859364383538358705077 36612924315410956721128601)
          ·
            refine ⟨27459693236558217540846451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36612924315410956721128601 27459693236558217540846451)
            ·
              refine ⟨41189539854837326311269677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27459693236558217540846451 41189539854837326311269677)
              ·
                refine ⟨15446077445563997366726129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41189539854837326311269677 15446077445563997366726129)
                ·
                  refine ⟨11584558084172998025044597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15446077445563997366726129 11584558084172998025044597)
                  ·
                    refine ⟨1086052320391218564847931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11584558084172998025044597 1086052320391218564847931)
                    ·
                      rfl

theorem cell22_3172619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_3172619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172619 prefixEnd_3172619 := by exact prefixLift 3172619
  have htrace : WordTrace (prefixWord ++ tailWord_3172619) baseStart_3172619 baseEnd_3172619 := by
    simpa [prefixWord, tailWord_3172619, baseEnd_3172619] using wordTrace_append hprefix tailTrace_3172619
  have hstable : (prefixWord ++ tailWord_3172619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172619).length < 2 ^ (prefixWord ++ tailWord_3172619).sum := by decide
  have hdescent : baseEnd_3172619 < baseStart_3172619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172638 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3172638 : Nat := 118140960795 + 3172638 * 2 ^ 59
def prefixEnd_3172638 : Nat := 4983230072969 + 3 ^ 40 * 3172638 * 2
def baseEnd_3172638 : Nat := 362019608159836282874291

theorem tailTrace_3172638 : CollatzResearch.WordTrace tailWord_3172638 prefixEnd_3172638 362019608159836282874291 := by
  unfold tailWord_3172638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464451785010230534643821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77143742853387896184767045 14464451785010230534643821)
  ·
    refine ⟨5424169419378836450491433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14464451785010230534643821 5424169419378836450491433)
    ·
      refine ⟨4068127064534127337868575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5424169419378836450491433 4068127064534127337868575)
      ·
        refine ⟨6102190596801191006802863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068127064534127337868575 6102190596801191006802863)
        ·
          refine ⟨9153285895201786510204295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102190596801191006802863 9153285895201786510204295)
          ·
            refine ⟨13729928842802679765306443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153285895201786510204295 13729928842802679765306443)
            ·
              refine ⟨20594893264204019647959665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13729928842802679765306443 20594893264204019647959665)
              ·
                refine ⟨15446169948153014735969749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20594893264204019647959665 15446169948153014735969749)
                ·
                  refine ⟨362019608159836282874291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15446169948153014735969749 362019608159836282874291)
                  ·
                    rfl

theorem cell22_3172638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3172638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172638 prefixEnd_3172638 := by exact prefixLift 3172638
  have htrace : WordTrace (prefixWord ++ tailWord_3172638) baseStart_3172638 baseEnd_3172638 := by
    simpa [prefixWord, tailWord_3172638, baseEnd_3172638] using wordTrace_append hprefix tailTrace_3172638
  have hstable : (prefixWord ++ tailWord_3172638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172638).length < 2 ^ (prefixWord ++ tailWord_3172638).sum := by decide
  have hdescent : baseEnd_3172638 < baseStart_3172638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172642 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3172642 : Nat := 118140960795 + 3172642 * 2 ^ 59
def prefixEnd_3172642 : Nat := 4983230072969 + 3 ^ 40 * 3172642 * 2
def baseEnd_3172642 : Nat := 1086060193761254171522861

theorem tailTrace_3172642 : CollatzResearch.WordTrace tailWord_3172642 prefixEnd_3172642 1086060193761254171522861 := by
  unfold tailWord_3172642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28928940043016838240074045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77143840114711568640197453 28928940043016838240074045)
  ·
    refine ⟨10848352516131314340027767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28928940043016838240074045 10848352516131314340027767)
    ·
      refine ⟨16272528774196971510041651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10848352516131314340027767 16272528774196971510041651)
      ·
        refine ⟨24408793161295457265062477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16272528774196971510041651 24408793161295457265062477)
        ·
          refine ⟨9153297435485796474398429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24408793161295457265062477 9153297435485796474398429)
          ·
            refine ⟨3432486538307173677899411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9153297435485796474398429 3432486538307173677899411)
            ·
              refine ⟨5148729807460760516849117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432486538307173677899411 5148729807460760516849117)
              ·
                refine ⟨1930773677797785193818419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5148729807460760516849117 1930773677797785193818419)
                ·
                  refine ⟨2896160516696677790727629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930773677797785193818419 2896160516696677790727629)
                  ·
                    refine ⟨1086060193761254171522861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896160516696677790727629 1086060193761254171522861)
                    ·
                      rfl

theorem cell22_3172642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3172642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172642 prefixEnd_3172642 := by exact prefixLift 3172642
  have htrace : WordTrace (prefixWord ++ tailWord_3172642) baseStart_3172642 baseEnd_3172642 := by
    simpa [prefixWord, tailWord_3172642, baseEnd_3172642] using wordTrace_append hprefix tailTrace_3172642
  have hstable : (prefixWord ++ tailWord_3172642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172642).length < 2 ^ (prefixWord ++ tailWord_3172642).sum := by decide
  have hdescent : baseEnd_3172642 < baseStart_3172642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172666 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_3172666 : Nat := 118140960795 + 3172666 * 2 ^ 59
def prefixEnd_3172666 : Nat := 4983230072969 + 3 ^ 40 * 3172666 * 2
def baseEnd_3172666 : Nat := 362022803150575369640929

theorem tailTrace_3172666 : CollatzResearch.WordTrace tailWord_3172666 prefixEnd_3172666 362022803150575369640929 := by
  unfold tailWord_3172666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28929158880995101264792463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77144423682653603372779901 28929158880995101264792463)
  ·
    refine ⟨43393738321492651897188695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28929158880995101264792463 43393738321492651897188695)
    ·
      refine ⟨65090607482238977845783043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43393738321492651897188695 65090607482238977845783043)
      ·
        refine ⟨97635911223358466768674565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65090607482238977845783043 97635911223358466768674565)
        ·
          refine ⟨18306733354379712519126481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97635911223358466768674565 18306733354379712519126481)
          ·
            refine ⟨13730050015784784389344861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18306733354379712519126481 13730050015784784389344861)
            ·
              refine ⟨5148768755919294146004323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13730050015784784389344861 5148768755919294146004323)
              ·
                refine ⟨7723153133878941219006485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5148768755919294146004323 7723153133878941219006485)
                ·
                  refine ⟨362022803150575369640929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7723153133878941219006485 362022803150575369640929)
                  ·
                    rfl

theorem cell22_3172666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_3172666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172666 prefixEnd_3172666 := by exact prefixLift 3172666
  have htrace : WordTrace (prefixWord ++ tailWord_3172666) baseStart_3172666 baseEnd_3172666 := by
    simpa [prefixWord, tailWord_3172666, baseEnd_3172666] using wordTrace_append hprefix tailTrace_3172666
  have hstable : (prefixWord ++ tailWord_3172666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172666).length < 2 ^ (prefixWord ++ tailWord_3172666).sum := by decide
  have hdescent : baseEnd_3172666 < baseStart_3172666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172743 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 3, 3]
def baseStart_3172743 : Nat := 118140960795 + 3172743 * 2 ^ 59
def prefixEnd_3172743 : Nat := 4983230072969 + 3 ^ 40 * 3172743 * 2
def baseEnd_3172743 : Nat := 1086094768125323574747551

theorem tailTrace_3172743 : CollatzResearch.WordTrace tailWord_3172743 prefixEnd_3172743 1086094768125323574747551 := by
  unfold tailWord_3172743
  simp only [CollatzResearch.WordTrace]
  refine ⟨115719443944701447209722883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77146295963134298139815255 115719443944701447209722883)
  ·
    refine ⟨173579165917052170814584325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115719443944701447209722883 173579165917052170814584325)
    ·
      refine ⟨32546093609447282027734561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173579165917052170814584325 32546093609447282027734561)
      ·
        refine ⟨24409570207085461520800921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32546093609447282027734561 24409570207085461520800921)
        ·
          refine ⟨18307177655314096140600691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24409570207085461520800921 18307177655314096140600691)
          ·
            refine ⟨27460766482971144210901037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18307177655314096140600691 27460766482971144210901037)
            ·
              refine ⟨10297787431114179079087889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27460766482971144210901037 10297787431114179079087889)
              ·
                refine ⟨7723340573335634309315917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10297787431114179079087889 7723340573335634309315917)
                ·
                  refine ⟨2896252715000862865993469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7723340573335634309315917 2896252715000862865993469)
                  ·
                    refine ⟨1086094768125323574747551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896252715000862865993469 1086094768125323574747551)
                    ·
                      rfl

theorem cell22_3172743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_3172743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172743 prefixEnd_3172743 := by exact prefixLift 3172743
  have htrace : WordTrace (prefixWord ++ tailWord_3172743) baseStart_3172743 baseEnd_3172743 := by
    simpa [prefixWord, tailWord_3172743, baseEnd_3172743] using wordTrace_append hprefix tailTrace_3172743
  have hstable : (prefixWord ++ tailWord_3172743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172743).length < 2 ^ (prefixWord ++ tailWord_3172743).sum := by decide
  have hdescent : baseEnd_3172743 < baseStart_3172743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172771 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_3172771 : Nat := 118140960795 + 3172771 * 2 ^ 59
def prefixEnd_3172771 : Nat := 4983230072969 + 3 ^ 40 * 3172771 * 2
def baseEnd_3172771 : Nat := 1086104353097540835047465

theorem tailTrace_3172771 : CollatzResearch.WordTrace tailWord_3172771 prefixEnd_3172771 1086104353097540835047465 := by
  unfold tailWord_3172771
  simp only [CollatzResearch.WordTrace]
  refine ⟨115720465188600007991742167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77146976792400005327828111 115720465188600007991742167)
  ·
    refine ⟨173580697782900011987613251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115720465188600007991742167 173580697782900011987613251)
    ·
      refine ⟨260371046674350017981419877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173580697782900011987613251 260371046674350017981419877)
      ·
        refine ⟨48819571251440628371516227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260371046674350017981419877 48819571251440628371516227)
        ·
          refine ⟨73229356877160942557274341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48819571251440628371516227 73229356877160942557274341)
          ·
            refine ⟨13730504414467676729488939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73229356877160942557274341 13730504414467676729488939)
            ·
              refine ⟨20595756621701515094233409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13730504414467676729488939 20595756621701515094233409)
              ·
                refine ⟨15446817466276136320675057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20595756621701515094233409 15446817466276136320675057)
                ·
                  refine ⟨11585113099707102240506293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15446817466276136320675057 11585113099707102240506293)
                  ·
                    refine ⟨1086104353097540835047465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11585113099707102240506293 1086104353097540835047465)
                    ·
                      rfl

theorem cell22_3172771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_3172771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172771 prefixEnd_3172771 := by exact prefixLift 3172771
  have htrace : WordTrace (prefixWord ++ tailWord_3172771) baseStart_3172771 baseEnd_3172771 := by
    simpa [prefixWord, tailWord_3172771, baseEnd_3172771] using wordTrace_append hprefix tailTrace_3172771
  have hstable : (prefixWord ++ tailWord_3172771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172771).length < 2 ^ (prefixWord ++ tailWord_3172771).sum := by decide
  have hdescent : baseEnd_3172771 < baseStart_3172771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172820 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3172820 : Nat := 118140960795 + 3172820 * 2 ^ 59
def prefixEnd_3172820 : Nat := 4983230072969 + 3 ^ 40 * 3172820 * 2
def baseEnd_3172820 : Nat := 1086121126798921040572315

theorem tailTrace_3172820 : CollatzResearch.WordTrace tailWord_3172820 prefixEnd_3172820 1086121126798921040572315 := by
  unfold tailWord_3172820
  simp only [CollatzResearch.WordTrace]
  refine ⟨57861126182711244680137957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77148168243614992906850609 57861126182711244680137957)
  ·
    refine ⟨10848961159258358377525867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57861126182711244680137957 10848961159258358377525867)
    ·
      refine ⟨16273441738887537566288801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10848961159258358377525867 16273441738887537566288801)
      ·
        refine ⟨12205081304165653174716601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16273441738887537566288801 12205081304165653174716601)
        ·
          refine ⟨9153810978124239881037451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12205081304165653174716601 9153810978124239881037451)
          ·
            refine ⟨13730716467186359821556177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153810978124239881037451 13730716467186359821556177)
            ·
              refine ⟨10298037350389769866167133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13730716467186359821556177 10298037350389769866167133)
              ·
                refine ⟨3861764006396163699812675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10298037350389769866167133 3861764006396163699812675)
                ·
                  refine ⟨5792646009594245549719013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861764006396163699812675 5792646009594245549719013)
                  ·
                    refine ⟨1086121126798921040572315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5792646009594245549719013 1086121126798921040572315)
                    ·
                      rfl

theorem cell22_3172820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3172820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172820 prefixEnd_3172820 := by exact prefixLift 3172820
  have htrace : WordTrace (prefixWord ++ tailWord_3172820) baseStart_3172820 baseEnd_3172820 := by
    simpa [prefixWord, tailWord_3172820, baseEnd_3172820] using wordTrace_append hprefix tailTrace_3172820
  have hstable : (prefixWord ++ tailWord_3172820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172820).length < 2 ^ (prefixWord ++ tailWord_3172820).sum := by decide
  have hdescent : baseEnd_3172820 < baseStart_3172820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172833 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3172833 : Nat := 118140960795 + 3172833 * 2 ^ 59
def prefixEnd_3172833 : Nat := 4983230072969 + 3 ^ 40 * 3172833 * 2
def baseEnd_3172833 : Nat := 1086125576964593339997275

theorem tailTrace_3172833 : CollatzResearch.WordTrace tailWord_3172833 prefixEnd_3172833 1086125576964593339997275 := by
  unfold tailWord_3172833
  simp only [CollatzResearch.WordTrace]
  refine ⟨115722726514375392580499153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77148484342916928386999435 115722726514375392580499153)
  ·
    refine ⟨86792044885781544435374365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115722726514375392580499153 86792044885781544435374365)
    ·
      refine ⟨32547016832168079163265387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86792044885781544435374365 32547016832168079163265387)
      ·
        refine ⟨48820525248252118744898081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32547016832168079163265387 48820525248252118744898081)
        ·
          refine ⟨36615393936189089058673561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48820525248252118744898081 36615393936189089058673561)
          ·
            refine ⟨27461545452141816794005171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36615393936189089058673561 27461545452141816794005171)
            ·
              refine ⟨41192318178212725191007757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27461545452141816794005171 41192318178212725191007757)
              ·
                refine ⟨15447119316829771946627909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41192318178212725191007757 15447119316829771946627909)
                ·
                  refine ⟨2896334871905582239992733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15447119316829771946627909 2896334871905582239992733)
                  ·
                    refine ⟨1086125576964593339997275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896334871905582239992733 1086125576964593339997275)
                    ·
                      rfl

theorem cell22_3172833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3172833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172833 prefixEnd_3172833 := by exact prefixLift 3172833
  have htrace : WordTrace (prefixWord ++ tailWord_3172833) baseStart_3172833 baseEnd_3172833 := by
    simpa [prefixWord, tailWord_3172833, baseEnd_3172833] using wordTrace_append hprefix tailTrace_3172833
  have hstable : (prefixWord ++ tailWord_3172833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172833).length < 2 ^ (prefixWord ++ tailWord_3172833).sum := by decide
  have hdescent : baseEnd_3172833 < baseStart_3172833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172835 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 6]
def baseStart_3172835 : Nat := 118140960795 + 3172835 * 2 ^ 59
def prefixEnd_3172835 : Nat := 4983230072969 + 3 ^ 40 * 3172835 * 2
def baseEnd_3172835 : Nat := 362042087201822000482423

theorem tailTrace_3172835 : CollatzResearch.WordTrace tailWord_3172835 prefixEnd_3172835 362042087201822000482423 := by
  unfold tailWord_3172835
  simp only [CollatzResearch.WordTrace]
  refine ⟨115722799460368146922071959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77148532973578764614714639 115722799460368146922071959)
  ·
    refine ⟨173584199190552220383107939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115722799460368146922071959 173584199190552220383107939)
    ·
      refine ⟨260376298785828330574661909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173584199190552220383107939 260376298785828330574661909)
      ·
        refine ⟨12205139005585702995687277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 260376298785828330574661909 12205139005585702995687277)
        ·
          refine ⟨4576927127094638623382729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12205139005585702995687277 4576927127094638623382729)
          ·
            refine ⟨3432695345320978967537047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4576927127094638623382729 3432695345320978967537047)
            ·
              refine ⟨5149043017981468451305571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432695345320978967537047 5149043017981468451305571)
              ·
                refine ⟨7723564526972202676958357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149043017981468451305571 7723564526972202676958357)
                ·
                  refine ⟨362042087201822000482423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7723564526972202676958357 362042087201822000482423)
                  ·
                    rfl

theorem cell22_3172835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 6].length) (baseStart_3172835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172835 prefixEnd_3172835 := by exact prefixLift 3172835
  have htrace : WordTrace (prefixWord ++ tailWord_3172835) baseStart_3172835 baseEnd_3172835 := by
    simpa [prefixWord, tailWord_3172835, baseEnd_3172835] using wordTrace_append hprefix tailTrace_3172835
  have hstable : (prefixWord ++ tailWord_3172835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172835).length < 2 ^ (prefixWord ++ tailWord_3172835).sum := by decide
  have hdescent : baseEnd_3172835 < baseStart_3172835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172865 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3172865 : Nat := 118140960795 + 3172865 * 2 ^ 59
def prefixEnd_3172865 : Nat := 4983230072969 + 3 ^ 40 * 3172865 * 2
def baseEnd_3172865 : Nat := 1086136531218555923197177

theorem tailTrace_3172865 : CollatzResearch.WordTrace tailWord_3172865 prefixEnd_3172865 1086136531218555923197177 := by
  unfold tailWord_3172865
  simp only [CollatzResearch.WordTrace]
  refine ⟨115723893650259462045664049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77149262433506308030442699 115723893650259462045664049)
  ·
    refine ⟨86792920237694596534248037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115723893650259462045664049 86792920237694596534248037)
    ·
      refine ⟨16273672544567736850171507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86792920237694596534248037 16273672544567736850171507)
      ·
        refine ⟨24410508816851605275257261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16273672544567736850171507 24410508816851605275257261)
        ·
          refine ⟨9153940806319351978221473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24410508816851605275257261 9153940806319351978221473)
          ·
            refine ⟨6865455604739513983666105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9153940806319351978221473 6865455604739513983666105)
            ·
              refine ⟨5149091703554635487749579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6865455604739513983666105 5149091703554635487749579)
              ·
                refine ⟨7723637555331953231624369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149091703554635487749579 7723637555331953231624369)
                ·
                  refine ⟨5792728166498964923718277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7723637555331953231624369 5792728166498964923718277)
                  ·
                    refine ⟨1086136531218555923197177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5792728166498964923718277 1086136531218555923197177)
                    ·
                      rfl

theorem cell22_3172865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3172865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172865 prefixEnd_3172865 := by exact prefixLift 3172865
  have htrace : WordTrace (prefixWord ++ tailWord_3172865) baseStart_3172865 baseEnd_3172865 := by
    simpa [prefixWord, tailWord_3172865, baseEnd_3172865] using wordTrace_append hprefix tailTrace_3172865
  have hstable : (prefixWord ++ tailWord_3172865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172865).length < 2 ^ (prefixWord ++ tailWord_3172865).sum := by decide
  have hdescent : baseEnd_3172865 < baseStart_3172865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172884 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3172884 : Nat := 118140960795 + 3172884 * 2 ^ 59
def prefixEnd_3172884 : Nat := 4983230072969 + 3 ^ 40 * 3172884 * 2
def baseEnd_3172884 : Nat := 1086143035306846206972119

theorem tailTrace_3172884 : CollatzResearch.WordTrace tailWord_3172884 prefixEnd_3172884 1086143035306846206972119 := by
  unfold tailWord_3172884
  simp only [CollatzResearch.WordTrace]
  refine ⟨57862293318595314145302853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77149724424793752193737137 57862293318595314145302853)
  ·
    refine ⟨10849179997236621402244285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57862293318595314145302853 10849179997236621402244285)
    ·
      refine ⟨4068442498963733025841607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10849179997236621402244285 4068442498963733025841607)
      ·
        refine ⟨6102663748445599538762411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068442498963733025841607 6102663748445599538762411)
        ·
          refine ⟨9153995622668399308143617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102663748445599538762411 9153995622668399308143617)
          ·
            refine ⟨6865496717001299481107713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9153995622668399308143617 6865496717001299481107713)
            ·
              refine ⟨5149122537750974610830785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6865496717001299481107713 5149122537750974610830785)
              ·
                refine ⟨3861841903313230958123089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5149122537750974610830785 3861841903313230958123089)
                ·
                  refine ⟨2896381427484923218592317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861841903313230958123089 2896381427484923218592317)
                  ·
                    refine ⟨1086143035306846206972119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896381427484923218592317 1086143035306846206972119)
                    ·
                      rfl

theorem cell22_3172884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3172884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172884 prefixEnd_3172884 := by exact prefixLift 3172884
  have htrace : WordTrace (prefixWord ++ tailWord_3172884) baseStart_3172884 baseEnd_3172884 := by
    simpa [prefixWord, tailWord_3172884, baseEnd_3172884] using wordTrace_append hprefix tailTrace_3172884
  have hstable : (prefixWord ++ tailWord_3172884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172884).length < 2 ^ (prefixWord ++ tailWord_3172884).sum := by decide
  have hdescent : baseEnd_3172884 < baseStart_3172884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172893 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3172893 : Nat := 118140960795 + 3172893 * 2 ^ 59
def prefixEnd_3172893 : Nat := 4983230072969 + 3 ^ 40 * 3172893 * 2
def baseEnd_3172893 : Nat := 1086146116190773183497091

theorem tailTrace_3172893 : CollatzResearch.WordTrace tailWord_3172893 prefixEnd_3172893 1086146116190773183497091 := by
  unfold tailWord_3172893
  simp only [CollatzResearch.WordTrace]
  refine ⟨115724914894158022827683333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77149943262772015218455555 115724914894158022827683333)
  ·
    refine ⟨21698421542654629280190625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115724914894158022827683333 21698421542654629280190625)
    ·
      refine ⟨16273816156990971960142969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21698421542654629280190625 16273816156990971960142969)
      ·
        refine ⟨12205362117743228970107227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16273816156990971960142969 12205362117743228970107227)
        ·
          refine ⟨18308043176614843455160841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12205362117743228970107227 18308043176614843455160841)
          ·
            refine ⟨13731032382461132591370631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18308043176614843455160841 13731032382461132591370631)
            ·
              refine ⟨20596548573691698887055947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13731032382461132591370631 20596548573691698887055947)
              ·
                refine ⟨30894822860537548330583921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20596548573691698887055947 30894822860537548330583921)
                ·
                  refine ⟨23171117145403161247937941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30894822860537548330583921 23171117145403161247937941)
                  ·
                    refine ⟨1086146116190773183497091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23171117145403161247937941 1086146116190773183497091)
                    ·
                      rfl

theorem cell22_3172893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3172893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172893 prefixEnd_3172893 := by exact prefixLift 3172893
  have htrace : WordTrace (prefixWord ++ tailWord_3172893) baseStart_3172893 baseEnd_3172893 := by
    simpa [prefixWord, tailWord_3172893, baseEnd_3172893] using wordTrace_append hprefix tailTrace_3172893
  have hstable : (prefixWord ++ tailWord_3172893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172893).length < 2 ^ (prefixWord ++ tailWord_3172893).sum := by decide
  have hdescent : baseEnd_3172893 < baseStart_3172893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172916 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3172916 : Nat := 118140960795 + 3172916 * 2 ^ 59
def prefixEnd_3172916 : Nat := 4983230072969 + 3 ^ 40 * 3172916 * 2
def baseEnd_3172916 : Nat := 1086153989560808790172021

theorem tailTrace_3172916 : CollatzResearch.WordTrace tailWord_3172916 prefixEnd_3172916 1086153989560808790172021 := by
  unfold tailWord_3172916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57862876886537348877885301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77150502515383131837180401 57862876886537348877885301)
  ·
    refine ⟨5424644708112876457301747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57862876886537348877885301 5424644708112876457301747)
    ·
      refine ⟨8136967062169314685952621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424644708112876457301747 8136967062169314685952621)
      ·
        refine ⟨3051362648313493007232233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8136967062169314685952621 3051362648313493007232233)
        ·
          refine ⟨2288521986235119755424175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051362648313493007232233 2288521986235119755424175)
          ·
            refine ⟨3432782979352679633136263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288521986235119755424175 3432782979352679633136263)
            ·
              refine ⟨5149174469029019449704395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432782979352679633136263 5149174469029019449704395)
              ·
                refine ⟨7723761703543529174556593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149174469029019449704395 7723761703543529174556593)
                ·
                  refine ⟨5792821277657646880917445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7723761703543529174556593 5792821277657646880917445)
                  ·
                    refine ⟨1086153989560808790172021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5792821277657646880917445 1086153989560808790172021)
                    ·
                      rfl

theorem cell22_3172916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3172916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172916 prefixEnd_3172916 := by exact prefixLift 3172916
  have htrace : WordTrace (prefixWord ++ tailWord_3172916) baseStart_3172916 baseEnd_3172916 := by
    simpa [prefixWord, tailWord_3172916, baseEnd_3172916] using wordTrace_append hprefix tailTrace_3172916
  have hstable : (prefixWord ++ tailWord_3172916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172916).length < 2 ^ (prefixWord ++ tailWord_3172916).sum := by decide
  have hdescent : baseEnd_3172916 < baseStart_3172916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172929 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3172929 : Nat := 118140960795 + 3172929 * 2 ^ 59
def prefixEnd_3172929 : Nat := 4983230072969 + 3 ^ 40 * 3172929 * 2
def baseEnd_3172929 : Nat := 1086158439726481089596981

theorem tailTrace_3172929 : CollatzResearch.WordTrace tailWord_3172929 prefixEnd_3172929 1086158439726481089596981 := by
  unfold tailWord_3172929
  simp only [CollatzResearch.WordTrace]
  refine ⟨115726227922027600975993841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77150818614685067317329227 115726227922027600975993841)
  ·
    refine ⟨86794670941520700731995381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115726227922027600975993841 86794670941520700731995381)
    ·
      refine ⟨8137000400767565693624567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86794670941520700731995381 8137000400767565693624567)
      ·
        refine ⟨12205500601151348540436851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137000400767565693624567 12205500601151348540436851)
        ·
          refine ⟨18308250901727022810655277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12205500601151348540436851 18308250901727022810655277)
          ·
            refine ⟨6865594088147633553995729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18308250901727022810655277 6865594088147633553995729)
            ·
              refine ⟨5149195566110725165496797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6865594088147633553995729 5149195566110725165496797)
              ·
                refine ⟨1930948337291521937061299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5149195566110725165496797 1930948337291521937061299)
                ·
                  refine ⟨2896422505937282905591949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930948337291521937061299 2896422505937282905591949)
                  ·
                    refine ⟨1086158439726481089596981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896422505937282905591949 1086158439726481089596981)
                    ·
                      rfl

theorem cell22_3172929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3172929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172929 prefixEnd_3172929 := by exact prefixLift 3172929
  have htrace : WordTrace (prefixWord ++ tailWord_3172929) baseStart_3172929 baseEnd_3172929 := by
    simpa [prefixWord, tailWord_3172929, baseEnd_3172929] using wordTrace_append hprefix tailTrace_3172929
  have hstable : (prefixWord ++ tailWord_3172929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172929).length < 2 ^ (prefixWord ++ tailWord_3172929).sum := by decide
  have hdescent : baseEnd_3172929 < baseStart_3172929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172983 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3172983 : Nat := 118140960795 + 3172983 * 2 ^ 59
def prefixEnd_3172983 : Nat := 4983230072969 + 3 ^ 40 * 3172983 * 2
def baseEnd_3172983 : Nat := 1086176925030042948746815

theorem tailTrace_3172983 : CollatzResearch.WordTrace tailWord_3172983 prefixEnd_3172983 1086176925030042948746815 := by
  unfold tailWord_3172983
  simp only [CollatzResearch.WordTrace]
  refine ⟨115728197463831968198459603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77152131642554645465639735 115728197463831968198459603)
  ·
    refine ⟨173592296195747952297689405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115728197463831968198459603 173592296195747952297689405)
    ·
      refine ⟨65097111073405482111633527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173592296195747952297689405 65097111073405482111633527)
      ·
        refine ⟨97645666610108223167450291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65097111073405482111633527 97645666610108223167450291)
        ·
          refine ⟨146468499915162334751175437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97645666610108223167450291 146468499915162334751175437)
          ·
            refine ⟨54925687468185875531690789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146468499915162334751175437 54925687468185875531690789)
            ·
              refine ⟨10298566400284851662192023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54925687468185875531690789 10298566400284851662192023)
              ·
                refine ⟨15447849600427277493288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10298566400284851662192023 15447849600427277493288035)
                ·
                  refine ⟨23171774400640916239932053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15447849600427277493288035 23171774400640916239932053)
                  ·
                    refine ⟨1086176925030042948746815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23171774400640916239932053 1086176925030042948746815)
                    ·
                      rfl

theorem cell22_3172983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3172983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172983 prefixEnd_3172983 := by exact prefixLift 3172983
  have htrace : WordTrace (prefixWord ++ tailWord_3172983) baseStart_3172983 baseEnd_3172983 := by
    simpa [prefixWord, tailWord_3172983, baseEnd_3172983] using wordTrace_append hprefix tailTrace_3172983
  have hstable : (prefixWord ++ tailWord_3172983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172983).length < 2 ^ (prefixWord ++ tailWord_3172983).sum := by decide
  have hdescent : baseEnd_3172983 < baseStart_3172983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172985 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_3172985 : Nat := 118140960795 + 3172985 * 2 ^ 59
def prefixEnd_3172985 : Nat := 4983230072969 + 3 ^ 40 * 3172985 * 2
def baseEnd_3172985 : Nat := 1086177609670915610196809

theorem tailTrace_3172985 : CollatzResearch.WordTrace tailWord_3172985 prefixEnd_3172985 1086177609670915610196809 := by
  unfold tailWord_3172985
  simp only [CollatzResearch.WordTrace]
  refine ⟨115728270409824722540032409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77152180273216481693354939 115728270409824722540032409)
  ·
    refine ⟨86796202807368541905024307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115728270409824722540032409 86796202807368541905024307)
    ·
      refine ⟨130194304211052812857536461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86796202807368541905024307 130194304211052812857536461)
      ·
        refine ⟨48822864079144804821576173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130194304211052812857536461 48822864079144804821576173)
        ·
          refine ⟨18308574029679301808091065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48822864079144804821576173 18308574029679301808091065)
          ·
            refine ⟨13731430522259476356068299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18308574029679301808091065 13731430522259476356068299)
            ·
              refine ⟨20597145783389214534102449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13731430522259476356068299 20597145783389214534102449)
              ·
                refine ⟨15447859337541910900576837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20597145783389214534102449 15447859337541910900576837)
                ·
                  refine ⟨2896473625789108293858157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15447859337541910900576837 2896473625789108293858157)
                  ·
                    refine ⟨1086177609670915610196809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896473625789108293858157 1086177609670915610196809)
                    ·
                      rfl

theorem cell22_3172985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_3172985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3172985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3172985 prefixEnd_3172985 := by exact prefixLift 3172985
  have htrace : WordTrace (prefixWord ++ tailWord_3172985) baseStart_3172985 baseEnd_3172985 := by
    simpa [prefixWord, tailWord_3172985, baseEnd_3172985] using wordTrace_append hprefix tailTrace_3172985
  have hstable : (prefixWord ++ tailWord_3172985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172985).length < 2 ^ (prefixWord ++ tailWord_3172985).sum := by decide
  have hdescent : baseEnd_3172985 < baseStart_3172985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173064 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 1, 3]
def baseStart_3173064 : Nat := 118140960795 + 3173064 * 2 ^ 59
def prefixEnd_3173064 : Nat := 4983230072969 + 3 ^ 40 * 3173064 * 2
def baseEnd_3173064 : Nat := 1086204652985385737471567

theorem tailTrace_3173064 : CollatzResearch.WordTrace tailWord_3173064 prefixEnd_3173064 1086204652985385737471567 := by
  unfold tailWord_3173064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57865575888269259516079123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77154101184359012688105497 57865575888269259516079123)
  ·
    refine ⟨86798363832403889274118685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57865575888269259516079123 86798363832403889274118685)
    ·
      refine ⟨32549386437151458477794507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86798363832403889274118685 32549386437151458477794507)
      ·
        refine ⟨48824079655727187716691761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32549386437151458477794507 48824079655727187716691761)
        ·
          refine ⟨36618059741795390787518821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48824079655727187716691761 36618059741795390787518821)
          ·
            refine ⟨6865886201586635772659779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36618059741795390787518821 6865886201586635772659779)
            ·
              refine ⟨10298829302379953658989669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865886201586635772659779 10298829302379953658989669)
              ·
                refine ⟨1931030494196241311060563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10298829302379953658989669 1931030494196241311060563)
                ·
                  refine ⟨2896545741294361966590845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931030494196241311060563 2896545741294361966590845)
                  ·
                    refine ⟨1086204652985385737471567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896545741294361966590845 1086204652985385737471567)
                    ·
                      rfl

theorem cell22_3173064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_3173064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173064 prefixEnd_3173064 := by exact prefixLift 3173064
  have htrace : WordTrace (prefixWord ++ tailWord_3173064) baseStart_3173064 baseEnd_3173064 := by
    simpa [prefixWord, tailWord_3173064, baseEnd_3173064] using wordTrace_append hprefix tailTrace_3173064
  have hstable : (prefixWord ++ tailWord_3173064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173064).length < 2 ^ (prefixWord ++ tailWord_3173064).sum := by decide
  have hdescent : baseEnd_3173064 < baseStart_3173064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173122 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3173122 : Nat := 118140960795 + 3173122 * 2 ^ 59
def prefixEnd_3173122 : Nat := 4983230072969 + 3 ^ 40 * 3173122 * 2
def baseEnd_3173122 : Nat := 362074835856897639840463

theorem tailTrace_3173122 : CollatzResearch.WordTrace tailWord_3173122 prefixEnd_3173122 362074835856897639840463 := by
  unfold tailWord_3173122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28933316802582098734442405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77155511473552263291846413 28933316802582098734442405)
  ·
    refine ⟨5424996900484143512707951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28933316802582098734442405 5424996900484143512707951)
    ·
      refine ⟨8137495350726215269061927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424996900484143512707951 8137495350726215269061927)
      ·
        refine ⟨12206243026089322903592891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137495350726215269061927 12206243026089322903592891)
        ·
          refine ⟨18309364539133984355389337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12206243026089322903592891 18309364539133984355389337)
          ·
            refine ⟨13732023404350488266542003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18309364539133984355389337 13732023404350488266542003)
            ·
              refine ⟨20598035106525732399813005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13732023404350488266542003 20598035106525732399813005)
              ·
                refine ⟨7724263164947149649929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20598035106525732399813005 7724263164947149649929877)
                ·
                  refine ⟨362074835856897639840463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7724263164947149649929877 362074835856897639840463)
                  ·
                    rfl

theorem cell22_3173122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3173122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173122 prefixEnd_3173122 := by exact prefixLift 3173122
  have htrace : WordTrace (prefixWord ++ tailWord_3173122) baseStart_3173122 baseEnd_3173122 := by
    simpa [prefixWord, tailWord_3173122, baseEnd_3173122] using wordTrace_append hprefix tailTrace_3173122
  have hstable : (prefixWord ++ tailWord_3173122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173122).length < 2 ^ (prefixWord ++ tailWord_3173122).sum := by decide
  have hdescent : baseEnd_3173122 < baseStart_3173122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173137 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_3173137 : Nat := 118140960795 + 3173137 * 2 ^ 59
def prefixEnd_3173137 : Nat := 4983230072969 + 3 ^ 40 * 3173137 * 2
def baseEnd_3173137 : Nat := 1086229642377237880396343

theorem tailTrace_3173137 : CollatzResearch.WordTrace tailWord_3173137 prefixEnd_3173137 1086229642377237880396343 := by
  unfold tailWord_3173137
  simp only [CollatzResearch.WordTrace]
  refine ⟨115733814305274052499565665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77155876203516034999710443 115733814305274052499565665)
  ·
    refine ⟨86800360728955539374674249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115733814305274052499565665 86800360728955539374674249)
    ·
      refine ⟨65100270546716654531005687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86800360728955539374674249 65100270546716654531005687)
      ·
        refine ⟨97650405820074981796508531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65100270546716654531005687 97650405820074981796508531)
        ·
          refine ⟨146475608730112472694762797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97650405820074981796508531 146475608730112472694762797)
          ·
            refine ⟨54928353273792177260536049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146475608730112472694762797 54928353273792177260536049)
            ·
              refine ⟨41196264955344132945402037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54928353273792177260536049 41196264955344132945402037)
              ·
                refine ⟨3862149839563512463631441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41196264955344132945402037 3862149839563512463631441)
                ·
                  refine ⟨2896612379672634347723581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862149839563512463631441 2896612379672634347723581)
                  ·
                    refine ⟨1086229642377237880396343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896612379672634347723581 1086229642377237880396343)
                    ·
                      rfl

theorem cell22_3173137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_3173137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173137 prefixEnd_3173137 := by exact prefixLift 3173137
  have htrace : WordTrace (prefixWord ++ tailWord_3173137) baseStart_3173137 baseEnd_3173137 := by
    simpa [prefixWord, tailWord_3173137, baseEnd_3173137] using wordTrace_append hprefix tailTrace_3173137
  have hstable : (prefixWord ++ tailWord_3173137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173137).length < 2 ^ (prefixWord ++ tailWord_3173137).sum := by decide
  have hdescent : baseEnd_3173137 < baseStart_3173137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173156 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 4]
def baseStart_3173156 : Nat := 118140960795 + 3173156 * 2 ^ 59
def prefixEnd_3173156 : Nat := 4983230072969 + 3 ^ 40 * 3173156 * 2
def baseEnd_3173156 : Nat := 362078715488509388057095

theorem tailTrace_3173156 : CollatzResearch.WordTrace tailWord_3173156 prefixEnd_3173156 362078715488509388057095 := by
  unfold tailWord_3173156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57867253646102609372253661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77156338194803479163004881 57867253646102609372253661)
  ·
    refine ⟨21700220117288478514595123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57867253646102609372253661 21700220117288478514595123)
    ·
      refine ⟨32550330175932717771892685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21700220117288478514595123 32550330175932717771892685)
      ·
        refine ⟨12206373815974769164459757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32550330175932717771892685 12206373815974769164459757)
        ·
          refine ⟨4577390180990538436672409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12206373815974769164459757 4577390180990538436672409)
          ·
            refine ⟨3433042635742903827504307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4577390180990538436672409 3433042635742903827504307)
            ·
              refine ⟨5149563953614355741256461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433042635742903827504307 5149563953614355741256461)
              ·
                refine ⟨1931086482605383402971173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5149563953614355741256461 1931086482605383402971173)
                ·
                  refine ⟨362078715488509388057095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931086482605383402971173 362078715488509388057095)
                  ·
                    rfl

theorem cell22_3173156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_3173156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173156 prefixEnd_3173156 := by exact prefixLift 3173156
  have htrace : WordTrace (prefixWord ++ tailWord_3173156) baseStart_3173156 baseEnd_3173156 := by
    simpa [prefixWord, tailWord_3173156, baseEnd_3173156] using wordTrace_append hprefix tailTrace_3173156
  have hstable : (prefixWord ++ tailWord_3173156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173156).length < 2 ^ (prefixWord ++ tailWord_3173156).sum := by decide
  have hdescent : baseEnd_3173156 < baseStart_3173156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173180 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3173180 : Nat := 118140960795 + 3173180 * 2 ^ 59
def prefixEnd_3173180 : Nat := 4983230072969 + 3 ^ 40 * 3173180 * 2
def baseEnd_3173180 : Nat := 1086244362156000101571211

theorem tailTrace_3173180 : CollatzResearch.WordTrace tailWord_3173180 prefixEnd_3173180 1086244362156000101571211 := by
  unfold tailWord_3173180
  simp only [CollatzResearch.WordTrace]
  refine ⟨57867691322059135421690497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77156921762745513895587329 57867691322059135421690497)
  ·
    refine ⟨43400768491544351566267873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57867691322059135421690497 43400768491544351566267873)
    ·
      refine ⟨32550576368658263674700905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43400768491544351566267873 32550576368658263674700905)
      ·
        refine ⟨24412932276493697756025679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32550576368658263674700905 24412932276493697756025679)
        ·
          refine ⟨36619398414740546634038519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24412932276493697756025679 36619398414740546634038519)
          ·
            refine ⟨54929097622110819951057779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36619398414740546634038519 54929097622110819951057779)
            ·
              refine ⟨82393646433166229926586669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54929097622110819951057779 82393646433166229926586669)
              ·
                refine ⟨30897617412437336222470001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82393646433166229926586669 30897617412437336222470001)
                ·
                  refine ⟨23173213059328002166852501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30897617412437336222470001 23173213059328002166852501)
                  ·
                    refine ⟨1086244362156000101571211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23173213059328002166852501 1086244362156000101571211)
                    ·
                      rfl

theorem cell22_3173180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3173180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173180 prefixEnd_3173180 := by exact prefixLift 3173180
  have htrace : WordTrace (prefixWord ++ tailWord_3173180) baseStart_3173180 baseEnd_3173180 := by
    simpa [prefixWord, tailWord_3173180, baseEnd_3173180] using wordTrace_append hprefix tailTrace_3173180
  have hstable : (prefixWord ++ tailWord_3173180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173180).length < 2 ^ (prefixWord ++ tailWord_3173180).sum := by decide
  have hdescent : baseEnd_3173180 < baseStart_3173180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173188 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3173188 : Nat := 118140960795 + 3173188 * 2 ^ 59
def prefixEnd_3173188 : Nat := 4983230072969 + 3 ^ 40 * 3173188 * 2
def baseEnd_3173188 : Nat := 1086247100719490747371187

theorem tailTrace_3173188 : CollatzResearch.WordTrace tailWord_3173188 prefixEnd_3173188 1086247100719490747371187 := by
  unfold tailWord_3173188
  simp only [CollatzResearch.WordTrace]
  refine ⟨57867837214044644104836109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77157116285392858806448145 57867837214044644104836109)
  ·
    refine ⟨21700438955266741539313541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57867837214044644104836109 21700438955266741539313541)
    ·
      refine ⟨4068832304112514038621289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21700438955266741539313541 4068832304112514038621289)
      ·
        refine ⟨3051624228084385528965967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4068832304112514038621289 3051624228084385528965967)
        ·
          refine ⟨4577436342126578293448951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051624228084385528965967 4577436342126578293448951)
          ·
            refine ⟨6866154513189867440173427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577436342126578293448951 6866154513189867440173427)
            ·
              refine ⟨10299231769784801160260141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866154513189867440173427 10299231769784801160260141)
              ·
                refine ⟨3862211913669300435097553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10299231769784801160260141 3862211913669300435097553)
                ·
                  refine ⟨2896658935251975326323165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862211913669300435097553 2896658935251975326323165)
                  ·
                    refine ⟨1086247100719490747371187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896658935251975326323165 1086247100719490747371187)
                    ·
                      rfl

theorem cell22_3173188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3173188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173188 prefixEnd_3173188 := by exact prefixLift 3173188
  have htrace : WordTrace (prefixWord ++ tailWord_3173188) baseStart_3173188 baseEnd_3173188 := by
    simpa [prefixWord, tailWord_3173188, baseEnd_3173188] using wordTrace_append hprefix tailTrace_3173188
  have hstable : (prefixWord ++ tailWord_3173188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173188).length < 2 ^ (prefixWord ++ tailWord_3173188).sum := by decide
  have hdescent : baseEnd_3173188 < baseStart_3173188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173233 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 1, 3]
def baseStart_3173233 : Nat := 118140960795 + 3173233 * 2 ^ 59
def prefixEnd_3173233 : Nat := 4983230072969 + 3 ^ 40 * 3173233 * 2
def baseEnd_3173233 : Nat := 1086262505139125629996049

theorem tailTrace_3173233 : CollatzResearch.WordTrace tailWord_3173233 prefixEnd_3173233 1086262505139125629996049 := by
  unfold tailWord_3173233
  simp only [CollatzResearch.WordTrace]
  refine ⟨115737315712926260895060353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77158210475284173930040235 115737315712926260895060353)
  ·
    refine ⟨86802986784694695671295265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115737315712926260895060353 86802986784694695671295265)
    ·
      refine ⟨65102240088521021753471449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86802986784694695671295265 65102240088521021753471449)
      ·
        refine ⟨48826680066390766315103587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65102240088521021753471449 48826680066390766315103587)
        ·
          refine ⟨73240020099586149472655381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48826680066390766315103587 73240020099586149472655381)
          ·
            refine ⟨3433125942168100756530721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73240020099586149472655381 3433125942168100756530721)
            ·
              refine ⟨2574844456626075567398041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3433125942168100756530721 2574844456626075567398041)
              ·
                refine ⟨1931133342469556675548531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574844456626075567398041 1931133342469556675548531)
                ·
                  refine ⟨2896700013704335013322797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931133342469556675548531 2896700013704335013322797)
                  ·
                    refine ⟨1086262505139125629996049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896700013704335013322797 1086262505139125629996049)
                    ·
                      rfl

theorem cell22_3173233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_3173233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173233 prefixEnd_3173233 := by exact prefixLift 3173233
  have htrace : WordTrace (prefixWord ++ tailWord_3173233) baseStart_3173233 baseEnd_3173233 := by
    simpa [prefixWord, tailWord_3173233, baseEnd_3173233] using wordTrace_append hprefix tailTrace_3173233
  have hstable : (prefixWord ++ tailWord_3173233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173233).length < 2 ^ (prefixWord ++ tailWord_3173233).sum := by decide
  have hdescent : baseEnd_3173233 < baseStart_3173233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173257 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 6]
def baseStart_3173257 : Nat := 118140960795 + 3173257 * 2 ^ 59
def prefixEnd_3173257 : Nat := 4983230072969 + 3 ^ 40 * 3173257 * 2
def baseEnd_3173257 : Nat := 362090240276532522465325

theorem tailTrace_3173257 : CollatzResearch.WordTrace tailWord_3173257 prefixEnd_3173257 362090240276532522465325 := by
  unfold tailWord_3173257
  simp only [CollatzResearch.WordTrace]
  refine ⟨115738191064839312993934025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77158794043226208662622683 115738191064839312993934025)
  ·
    refine ⟨86803643298629484745450519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115738191064839312993934025 86803643298629484745450519)
    ·
      refine ⟨130205464947944227118175779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86803643298629484745450519 130205464947944227118175779)
      ·
        refine ⟨195308197421916340677263669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130205464947944227118175779 195308197421916340677263669)
        ·
          refine ⟨18310143508304656938493469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195308197421916340677263669 18310143508304656938493469)
          ·
            refine ⟨6866303815614246351935051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18310143508304656938493469 6866303815614246351935051)
            ·
              refine ⟨10299455723421369527902577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866303815614246351935051 10299455723421369527902577)
              ·
                refine ⟨7724591792566027145926933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10299455723421369527902577 7724591792566027145926933)
                ·
                  refine ⟨362090240276532522465325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7724591792566027145926933 362090240276532522465325)
                  ·
                    rfl

theorem cell22_3173257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_3173257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173257 prefixEnd_3173257 := by exact prefixLift 3173257
  have htrace : WordTrace (prefixWord ++ tailWord_3173257) baseStart_3173257 baseEnd_3173257 := by
    simpa [prefixWord, tailWord_3173257, baseEnd_3173257] using wordTrace_append hprefix tailTrace_3173257
  have hstable : (prefixWord ++ tailWord_3173257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173257).length < 2 ^ (prefixWord ++ tailWord_3173257).sum := by decide
  have hdescent : baseEnd_3173257 < baseStart_3173257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173276 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3173276 : Nat := 118140960795 + 3173276 * 2 ^ 59
def prefixEnd_3173276 : Nat := 4983230072969 + 3 ^ 40 * 3173276 * 2
def baseEnd_3173276 : Nat := 1086277224917887851170917

theorem tailTrace_3173276 : CollatzResearch.WordTrace tailWord_3173276 prefixEnd_3173276 1086277224917887851170917 := by
  unfold tailWord_3173276
  simp only [CollatzResearch.WordTrace]
  refine ⟨57869442025885239619437841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77159256034513652825917121 57869442025885239619437841)
  ·
    refine ⟨43402081519413929714578381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57869442025885239619437841 43402081519413929714578381)
    ·
      refine ⟨16275780569780223642966893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43402081519413929714578381 16275780569780223642966893)
      ·
        refine ⟨6103417713667583866112585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16275780569780223642966893 6103417713667583866112585)
        ·
          refine ⟨4577563285250687899584439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6103417713667583866112585 4577563285250687899584439)
          ·
            refine ⟨6866344927876031849376659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577563285250687899584439 6866344927876031849376659)
            ·
              refine ⟨10299517391814047774064989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866344927876031849376659 10299517391814047774064989)
              ·
                refine ⟨3862319021930267915274371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10299517391814047774064989 3862319021930267915274371)
                ·
                  refine ⟨5793478532895401872911557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862319021930267915274371 5793478532895401872911557)
                  ·
                    refine ⟨1086277224917887851170917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5793478532895401872911557 1086277224917887851170917)
                    ·
                      rfl

theorem cell22_3173276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3173276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173276 prefixEnd_3173276 := by exact prefixLift 3173276
  have htrace : WordTrace (prefixWord ++ tailWord_3173276) baseStart_3173276 baseEnd_3173276 := by
    simpa [prefixWord, tailWord_3173276, baseEnd_3173276] using wordTrace_append hprefix tailTrace_3173276
  have hstable : (prefixWord ++ tailWord_3173276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173276).length < 2 ^ (prefixWord ++ tailWord_3173276).sum := by decide
  have hdescent : baseEnd_3173276 < baseStart_3173276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173306 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_3173306 : Nat := 118140960795 + 3173306 * 2 ^ 59
def prefixEnd_3173306 : Nat := 4983230072969 + 3 ^ 40 * 3173306 * 2
def baseEnd_3173306 : Nat := 1086287494530977772920825

theorem tailTrace_3173306 : CollatzResearch.WordTrace tailWord_3173306 prefixEnd_3173306 1086287494530977772920825 := by
  unfold tailWord_3173306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28934994560415448590616943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77159985494441196241645181 28934994560415448590616943)
  ·
    refine ⟨43402491840623172885925415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28934994560415448590616943 43402491840623172885925415)
    ·
      refine ⟨65103737760934759328888123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43402491840623172885925415 65103737760934759328888123)
      ·
        refine ⟨97655606641402138993332185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65103737760934759328888123 97655606641402138993332185)
        ·
          refine ⟨73241704981051604244999139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97655606641402138993332185 73241704981051604244999139)
          ·
            refine ⟨109862557471577406367498709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73241704981051604244999139 109862557471577406367498709)
            ·
              refine ⟨2574903690740095461738251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109862557471577406367498709 2574903690740095461738251)
              ·
                refine ⟨3862355536110143192607377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574903690740095461738251 3862355536110143192607377)
                ·
                  refine ⟨2896766652082607394455533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862355536110143192607377 2896766652082607394455533)
                  ·
                    refine ⟨1086287494530977772920825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896766652082607394455533 1086287494530977772920825)
                    ·
                      rfl

theorem cell22_3173306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_3173306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173306 prefixEnd_3173306 := by exact prefixLift 3173306
  have htrace : WordTrace (prefixWord ++ tailWord_3173306) baseStart_3173306 baseEnd_3173306 := by
    simpa [prefixWord, tailWord_3173306, baseEnd_3173306] using wordTrace_append hprefix tailTrace_3173306
  have hstable : (prefixWord ++ tailWord_3173306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173306).length < 2 ^ (prefixWord ++ tailWord_3173306).sum := by decide
  have hdescent : baseEnd_3173306 < baseStart_3173306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173347 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 7]
def baseStart_3173347 : Nat := 118140960795 + 3173347 * 2 ^ 59
def prefixEnd_3173347 : Nat := 4983230072969 + 3 ^ 40 * 3173347 * 2
def baseEnd_3173347 : Nat := 362100509889622444215233

theorem tailTrace_3173347 : CollatzResearch.WordTrace tailWord_3173347 prefixEnd_3173347 362100509889622444215233 := by
  unfold tailWord_3173347
  simp only [CollatzResearch.WordTrace]
  refine ⟨115741473634513258364710295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77160982423008838909806863 115741473634513258364710295)
  ·
    refine ⟨173612210451769887547065443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115741473634513258364710295 173612210451769887547065443)
    ·
      refine ⟨260418315677654831320598165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173612210451769887547065443 260418315677654831320598165)
      ·
        refine ⟨12207108547390070218153039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 260418315677654831320598165 12207108547390070218153039)
        ·
          refine ⟨18310662821085105327229559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12207108547390070218153039 18310662821085105327229559)
          ·
            refine ⟨27465994231627657990844339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18310662821085105327229559 27465994231627657990844339)
            ·
              refine ⟨41198991347441486986266509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27465994231627657990844339 41198991347441486986266509)
              ·
                refine ⟨15449621755290557619849941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41198991347441486986266509 15449621755290557619849941)
                ·
                  refine ⟨362100509889622444215233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15449621755290557619849941 362100509889622444215233)
                  ·
                    rfl

theorem cell22_3173347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_3173347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173347 prefixEnd_3173347 := by exact prefixLift 3173347
  have htrace : WordTrace (prefixWord ++ tailWord_3173347) baseStart_3173347 baseEnd_3173347 := by
    simpa [prefixWord, tailWord_3173347, baseEnd_3173347] using wordTrace_append hprefix tailTrace_3173347
  have hstable : (prefixWord ++ tailWord_3173347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173347).length < 2 ^ (prefixWord ++ tailWord_3173347).sum := by decide
  have hdescent : baseEnd_3173347 < baseStart_3173347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173351 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3173351 : Nat := 118140960795 + 3173351 * 2 ^ 59
def prefixEnd_3173351 : Nat := 4983230072969 + 3 ^ 40 * 3173351 * 2
def baseEnd_3173351 : Nat := 1086302898950612655545687

theorem tailTrace_3173351 : CollatzResearch.WordTrace tailWord_3173351 prefixEnd_3173351 1086302898950612655545687 := by
  unfold tailWord_3173351
  simp only [CollatzResearch.WordTrace]
  refine ⟨115741619526498767047855907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77161079684332511365237271 115741619526498767047855907)
  ·
    refine ⟨173612429289748150571783861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115741619526498767047855907 173612429289748150571783861)
    ·
      refine ⟨16276165245913889116104737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173612429289748150571783861 16276165245913889116104737)
      ·
        refine ⟨12207123934435416837078553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16276165245913889116104737 12207123934435416837078553)
        ·
          refine ⟨9155342950826562627808915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12207123934435416837078553 9155342950826562627808915)
          ·
            refine ⟨13733014426239843941713373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155342950826562627808915 13733014426239843941713373)
            ·
              refine ⟨5149880409839941478142515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13733014426239843941713373 5149880409839941478142515)
              ·
                refine ⟨7724820614759912217213773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149880409839941478142515 7724820614759912217213773)
                ·
                  refine ⟨2896807730534967081455165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7724820614759912217213773 2896807730534967081455165)
                  ·
                    refine ⟨1086302898950612655545687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896807730534967081455165 1086302898950612655545687)
                    ·
                      rfl

theorem cell22_3173351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3173351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173351 prefixEnd_3173351 := by exact prefixLift 3173351
  have htrace : WordTrace (prefixWord ++ tailWord_3173351) baseStart_3173351 baseEnd_3173351 := by
    simpa [prefixWord, tailWord_3173351, baseEnd_3173351] using wordTrace_append hprefix tailTrace_3173351
  have hstable : (prefixWord ++ tailWord_3173351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173351).length < 2 ^ (prefixWord ++ tailWord_3173351).sum := by decide
  have hdescent : baseEnd_3173351 < baseStart_3173351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173424 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_3173424 : Nat := 118140960795 + 3173424 * 2 ^ 59
def prefixEnd_3173424 : Nat := 4983230072969 + 3 ^ 40 * 3173424 * 2
def baseEnd_3173424 : Nat := 1086327888342464798470463

theorem tailTrace_3173424 : CollatzResearch.WordTrace tailWord_3173424 prefixEnd_3173424 1086327888342464798470463 := by
  unfold tailWord_3173424
  simp only [CollatzResearch.WordTrace]
  refine ⟨57872141027617150257631663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77162854703489533676842217 57872141027617150257631663)
  ·
    refine ⟨86808211541425725386447495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57872141027617150257631663 86808211541425725386447495)
    ·
      refine ⟨130212317312138588079671243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86808211541425725386447495 130212317312138588079671243)
      ·
        refine ⟨195318475968207882119506865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130212317312138588079671243 195318475968207882119506865)
        ·
          refine ⟨146488856976155911589630149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195318475968207882119506865 146488856976155911589630149)
          ·
            refine ⟨27466660683029233423055653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146488856976155911589630149 27466660683029233423055653)
            ·
              refine ⟨5149998878067981266822935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27466660683029233423055653 5149998878067981266822935)
              ·
                refine ⟨7724998317101971900234403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149998878067981266822935 7724998317101971900234403)
                ·
                  refine ⟨11587497475652957850351605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7724998317101971900234403 11587497475652957850351605)
                  ·
                    refine ⟨1086327888342464798470463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11587497475652957850351605 1086327888342464798470463)
                    ·
                      rfl

theorem cell22_3173424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_3173424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173424 prefixEnd_3173424 := by exact prefixLift 3173424
  have htrace : WordTrace (prefixWord ++ tailWord_3173424) baseStart_3173424 baseEnd_3173424 := by
    simpa [prefixWord, tailWord_3173424, baseEnd_3173424] using wordTrace_append hprefix tailTrace_3173424
  have hstable : (prefixWord ++ tailWord_3173424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173424).length < 2 ^ (prefixWord ++ tailWord_3173424).sum := by decide
  have hdescent : baseEnd_3173424 < baseStart_3173424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173458 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3173458 : Nat := 118140960795 + 3173458 * 2 ^ 59
def prefixEnd_3173458 : Nat := 4983230072969 + 3 ^ 40 * 3173458 * 2
def baseEnd_3173458 : Nat := 1086339527237300043120359

theorem tailTrace_3173458 : CollatzResearch.WordTrace tailWord_3173458 prefixEnd_3173458 1086339527237300043120359 := by
  unfold tailWord_3173458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28936380534277781080500257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77163681424740749548000685 28936380534277781080500257)
  ·
    refine ⟨21702285400708335810375193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28936380534277781080500257 21702285400708335810375193)
    ·
      refine ⟨16276714050531251857781395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21702285400708335810375193 16276714050531251857781395)
      ·
        refine ⟨24415071075796877786672093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16276714050531251857781395 24415071075796877786672093)
        ·
          refine ⟨9155651653423829170002035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24415071075796877786672093 9155651653423829170002035)
          ·
            refine ⟨13733477480135743755003053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155651653423829170002035 13733477480135743755003053)
            ·
              refine ⟨5150054055050903908126145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13733477480135743755003053 5150054055050903908126145)
              ·
                refine ⟨3862540541288177931094609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150054055050903908126145 3862540541288177931094609)
                ·
                  refine ⟨2896905405966133448320957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862540541288177931094609 2896905405966133448320957)
                  ·
                    refine ⟨1086339527237300043120359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896905405966133448320957 1086339527237300043120359)
                    ·
                      rfl

theorem cell22_3173458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3173458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173458 prefixEnd_3173458 := by exact prefixLift 3173458
  have htrace : WordTrace (prefixWord ++ tailWord_3173458) baseStart_3173458 baseEnd_3173458 := by
    simpa [prefixWord, tailWord_3173458, baseEnd_3173458] using wordTrace_append hprefix tailTrace_3173458
  have hstable : (prefixWord ++ tailWord_3173458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173458).length < 2 ^ (prefixWord ++ tailWord_3173458).sum := by decide
  have hdescent : baseEnd_3173458 < baseStart_3173458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173576 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_3173576 : Nat := 118140960795 + 3173576 * 2 ^ 59
def prefixEnd_3173576 : Nat := 4983230072969 + 3 ^ 40 * 3173576 * 2
def baseEnd_3173576 : Nat := 1086379921048787068669997

theorem tailTrace_3173576 : CollatzResearch.WordTrace tailWord_3173576 prefixEnd_3173576 1086379921048787068669997 := by
  unfold tailWord_3173576
  simp only [CollatzResearch.WordTrace]
  refine ⟨57874912975341815237398291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77166550633789086983197721 57874912975341815237398291)
  ·
    refine ⟨86812369463012722856097437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57874912975341815237398291 86812369463012722856097437)
    ·
      refine ⟨32554638548629771071036539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86812369463012722856097437 32554638548629771071036539)
      ·
        refine ⟨48831957822944656606554809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32554638548629771071036539 48831957822944656606554809)
        ·
          refine ⟨36623968367208492454916107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48831957822944656606554809 36623968367208492454916107)
          ·
            refine ⟨54935952550812738682374161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36623968367208492454916107 54935952550812738682374161)
            ·
              refine ⟨41201964413109554011780621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54935952550812738682374161 41201964413109554011780621)
              ·
                refine ⟨15450736654916082754417733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41201964413109554011780621 15450736654916082754417733)
                ·
                  refine ⟨2897013122796765516453325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15450736654916082754417733 2897013122796765516453325)
                  ·
                    refine ⟨1086379921048787068669997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897013122796765516453325 1086379921048787068669997)
                    ·
                      rfl

theorem cell22_3173576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_3173576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173576 prefixEnd_3173576 := by exact prefixLift 3173576
  have htrace : WordTrace (prefixWord ++ tailWord_3173576) baseStart_3173576 baseEnd_3173576 := by
    simpa [prefixWord, tailWord_3173576, baseEnd_3173576] using wordTrace_append hprefix tailTrace_3173576
  have hstable : (prefixWord ++ tailWord_3173576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173576).length < 2 ^ (prefixWord ++ tailWord_3173576).sum := by decide
  have hdescent : baseEnd_3173576 < baseStart_3173576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173578 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_3173578 : Nat := 118140960795 + 3173578 * 2 ^ 59
def prefixEnd_3173578 : Nat := 4983230072969 + 3 ^ 40 * 3173578 * 2
def baseEnd_3173578 : Nat := 362126868563219910039997

theorem tailTrace_3173578 : CollatzResearch.WordTrace tailWord_3173578 prefixEnd_3173578 362126868563219910039997 := by
  unfold tailWord_3173578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937474724169096204092347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77166599264450923210912925 28937474724169096204092347)
  ·
    refine ⟨43406212086253644306138521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28937474724169096204092347 43406212086253644306138521)
    ·
      refine ⟨32554659064690233229603891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43406212086253644306138521 32554659064690233229603891)
      ·
        refine ⟨48831988597035349844405837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32554659064690233229603891 48831988597035349844405837)
        ·
          refine ⟨18311995723888256191652189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48831988597035349844405837 18311995723888256191652189)
          ·
            refine ⟨6866998396458096071869571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18311995723888256191652189 6866998396458096071869571)
            ·
              refine ⟨10300497594687144107804357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866998396458096071869571 10300497594687144107804357)
              ·
                refine ⟨1931343299003839520213317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10300497594687144107804357 1931343299003839520213317)
                ·
                  refine ⟨362126868563219910039997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931343299003839520213317 362126868563219910039997)
                  ·
                    rfl

theorem cell22_3173578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_3173578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173578 prefixEnd_3173578 := by exact prefixLift 3173578
  have htrace : WordTrace (prefixWord ++ tailWord_3173578) baseStart_3173578 baseEnd_3173578 := by
    simpa [prefixWord, tailWord_3173578, baseEnd_3173578] using wordTrace_append hprefix tailTrace_3173578
  have hstable : (prefixWord ++ tailWord_3173578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173578).length < 2 ^ (prefixWord ++ tailWord_3173578).sum := by decide
  have hdescent : baseEnd_3173578 < baseStart_3173578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173672 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3173672 : Nat := 118140960795 + 3173672 * 2 ^ 59
def prefixEnd_3173672 : Nat := 4983230072969 + 3 ^ 40 * 3173672 * 2
def baseEnd_3173672 : Nat := 1086412783810674818269703

theorem tailTrace_3173672 : CollatzResearch.WordTrace tailWord_3173672 prefixEnd_3173672 1086412783810674818269703 := by
  unfold tailWord_3173672
  simp only [CollatzResearch.WordTrace]
  refine ⟨57876663679167919435145635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77168884905557225913527513 57876663679167919435145635)
  ·
    refine ⟨86814995518751879152718453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57876663679167919435145635 86814995518751879152718453)
    ·
      refine ⟨8138905829882988670567355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86814995518751879152718453 8138905829882988670567355)
      ·
        refine ⟨12208358744824483005851033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8138905829882988670567355 12208358744824483005851033)
        ·
          refine ⟨9156269058618362254388275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12208358744824483005851033 9156269058618362254388275)
          ·
            refine ⟨13734403587927543381582413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156269058618362254388275 13734403587927543381582413)
            ·
              refine ⟨5150401345472828768093405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13734403587927543381582413 5150401345472828768093405)
              ·
                refine ⟨1931400504552310788035027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5150401345472828768093405 1931400504552310788035027)
                ·
                  refine ⟨2897100756828466182052541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931400504552310788035027 2897100756828466182052541)
                  ·
                    refine ⟨1086412783810674818269703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897100756828466182052541 1086412783810674818269703)
                    ·
                      rfl

theorem cell22_3173672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3173672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173672 prefixEnd_3173672 := by exact prefixLift 3173672
  have htrace : WordTrace (prefixWord ++ tailWord_3173672) baseStart_3173672 baseEnd_3173672 := by
    simpa [prefixWord, tailWord_3173672, baseEnd_3173672] using wordTrace_append hprefix tailTrace_3173672
  have hstable : (prefixWord ++ tailWord_3173672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173672).length < 2 ^ (prefixWord ++ tailWord_3173672).sum := by decide
  have hdescent : baseEnd_3173672 < baseStart_3173672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173689 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 1, 3]
def baseStart_3173689 : Nat := 118140960795 + 3173689 * 2 ^ 59
def prefixEnd_3173689 : Nat := 4983230072969 + 3 ^ 40 * 3173689 * 2
def baseEnd_3173689 : Nat := 1086418603258092440594651

theorem tailTrace_3173689 : CollatzResearch.WordTrace tailWord_3173689 prefixEnd_3173689 1086418603258092440594651 := by
  unfold tailWord_3173689
  simp only [CollatzResearch.WordTrace]
  refine ⟨115753947399274250773660121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77169298266182833849106747 115753947399274250773660121)
  ·
    refine ⟨86815460549455688080245091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115753947399274250773660121 86815460549455688080245091)
    ·
      refine ⟨130223190824183532120367637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86815460549455688080245091 130223190824183532120367637)
      ·
        refine ⟨6104212069883603068142233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130223190824183532120367637 6104212069883603068142233)
        ·
          refine ⟨4578159052412702301106675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104212069883603068142233 4578159052412702301106675)
          ·
            refine ⟨6867238578619053451660013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578159052412702301106675 6867238578619053451660013)
            ·
              refine ⟨2575214466982145044372505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6867238578619053451660013 2575214466982145044372505)
              ·
                refine ⟨1931410850236608783279379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575214466982145044372505 1931410850236608783279379)
                ·
                  refine ⟨2897116275354913174919069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931410850236608783279379 2897116275354913174919069)
                  ·
                    refine ⟨1086418603258092440594651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897116275354913174919069 1086418603258092440594651)
                    ·
                      rfl

theorem cell22_3173689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_3173689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173689 prefixEnd_3173689 := by exact prefixLift 3173689
  have htrace : WordTrace (prefixWord ++ tailWord_3173689) baseStart_3173689 baseEnd_3173689 := by
    simpa [prefixWord, tailWord_3173689, baseEnd_3173689] using wordTrace_append hprefix tailTrace_3173689
  have hstable : (prefixWord ++ tailWord_3173689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173689).length < 2 ^ (prefixWord ++ tailWord_3173689).sum := by decide
  have hdescent : baseEnd_3173689 < baseStart_3173689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173728 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_3173728 : Nat := 118140960795 + 3173728 * 2 ^ 59
def prefixEnd_3173728 : Nat := 4983230072969 + 3 ^ 40 * 3173728 * 2
def baseEnd_3173728 : Nat := 1086431953755109338869531

theorem tailTrace_3173728 : CollatzResearch.WordTrace tailWord_3173728 prefixEnd_3173728 1086431953755109338869531 := by
  unfold tailWord_3173728
  simp only [CollatzResearch.WordTrace]
  refine ⟨57877684923066480217164919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77170246564088640289553225 57877684923066480217164919)
  ·
    refine ⟨86816527384599720325747379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57877684923066480217164919 86816527384599720325747379)
    ·
      refine ⟨130224791076899580488621069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86816527384599720325747379 130224791076899580488621069)
      ·
        refine ⟨48834296653837342683232901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130224791076899580488621069 48834296653837342683232901)
        ·
          refine ⟨9156430622594501753106169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48834296653837342683232901 9156430622594501753106169)
          ·
            refine ⟨6867322966945876314829627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9156430622594501753106169 6867322966945876314829627)
            ·
              refine ⟨10300984450418814472244441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6867322966945876314829627 10300984450418814472244441)
              ·
                refine ⟨7725738337814110854183331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10300984450418814472244441 7725738337814110854183331)
                ·
                  refine ⟨11588607506721166281274997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725738337814110854183331 11588607506721166281274997)
                  ·
                    refine ⟨1086431953755109338869531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11588607506721166281274997 1086431953755109338869531)
                    ·
                      rfl

theorem cell22_3173728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_3173728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173728 prefixEnd_3173728 := by exact prefixLift 3173728
  have htrace : WordTrace (prefixWord ++ tailWord_3173728) baseStart_3173728 baseEnd_3173728 := by
    simpa [prefixWord, tailWord_3173728, baseEnd_3173728] using wordTrace_append hprefix tailTrace_3173728
  have hstable : (prefixWord ++ tailWord_3173728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173728).length < 2 ^ (prefixWord ++ tailWord_3173728).sum := by decide
  have hdescent : baseEnd_3173728 < baseStart_3173728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173730 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3173730 : Nat := 118140960795 + 3173730 * 2 ^ 59
def prefixEnd_3173730 : Nat := 4983230072969 + 3 ^ 40 * 3173730 * 2
def baseEnd_3173730 : Nat := 362144212798660666773175

theorem tailTrace_3173730 : CollatzResearch.WordTrace tailWord_3173730 prefixEnd_3173730 362144212798660666773175 := by
  unfold tailWord_3173730
  simp only [CollatzResearch.WordTrace]
  refine ⟨28938860698031428693975661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77170295194750476517268429 28938860698031428693975661)
  ·
    refine ⟨10852072761761785760240873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28938860698031428693975661 10852072761761785760240873)
    ·
      refine ⟨8139054571321339320180655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10852072761761785760240873 8139054571321339320180655)
      ·
        refine ⟨12208581856982008980270983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8139054571321339320180655 12208581856982008980270983)
        ·
          refine ⟨18312872785473013470406475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12208581856982008980270983 18312872785473013470406475)
          ·
            refine ⟨27469309178209520205609713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18312872785473013470406475 27469309178209520205609713)
            ·
              refine ⟨20601981883657140154207285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27469309178209520205609713 20601981883657140154207285)
              ·
                refine ⟨1931435801592856889456933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20601981883657140154207285 1931435801592856889456933)
                ·
                  refine ⟨362144212798660666773175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931435801592856889456933 362144212798660666773175)
                  ·
                    rfl

theorem cell22_3173730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3173730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173730 prefixEnd_3173730 := by exact prefixLift 3173730
  have htrace : WordTrace (prefixWord ++ tailWord_3173730) baseStart_3173730 baseEnd_3173730 := by
    simpa [prefixWord, tailWord_3173730, baseEnd_3173730] using wordTrace_append hprefix tailTrace_3173730
  have hstable : (prefixWord ++ tailWord_3173730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173730).length < 2 ^ (prefixWord ++ tailWord_3173730).sum := by decide
  have hdescent : baseEnd_3173730 < baseStart_3173730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173741 : List Nat := [1, 5, 1, 1, 1, 13]
def baseStart_3173741 : Nat := 118140960795 + 3173741 * 2 ^ 59
def prefixEnd_3173741 : Nat := 4983230072969 + 3 ^ 40 * 3173741 * 2
def baseEnd_3173741 : Nat := 13412795110133106645611

theorem tailTrace_3173741 : CollatzResearch.WordTrace tailWord_3173741 prefixEnd_3173741 13412795110133106645611 := by
  unfold tailWord_3173741
  simp only [CollatzResearch.WordTrace]
  refine ⟨115755843995085863654553077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77170562663390575769702051 115755843995085863654553077)
  ·
    refine ⟨10852110374539299717614351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115755843995085863654553077 10852110374539299717614351)
    ·
      refine ⟨16278165561808949576421527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10852110374539299717614351 16278165561808949576421527)
      ·
        refine ⟨24417248342713424364632291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278165561808949576421527 24417248342713424364632291)
        ·
          refine ⟨36625872514070136546948437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24417248342713424364632291 36625872514070136546948437)
          ·
            refine ⟨13412795110133106645611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 36625872514070136546948437 13412795110133106645611)
            ·
              rfl

theorem cell22_3173741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 13].length) (baseStart_3173741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173741 prefixEnd_3173741 := by exact prefixLift 3173741
  have htrace : WordTrace (prefixWord ++ tailWord_3173741) baseStart_3173741 baseEnd_3173741 := by
    simpa [prefixWord, tailWord_3173741, baseEnd_3173741] using wordTrace_append hprefix tailTrace_3173741
  have hstable : (prefixWord ++ tailWord_3173741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173741).length < 2 ^ (prefixWord ++ tailWord_3173741).sum := by decide
  have hdescent : baseEnd_3173741 < baseStart_3173741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173762 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3173762 : Nat := 118140960795 + 3173762 * 2 ^ 59
def prefixEnd_3173762 : Nat := 4983230072969 + 3 ^ 40 * 3173762 * 2
def baseEnd_3173762 : Nat := 1086443592649944583519427

theorem tailTrace_3173762 : CollatzResearch.WordTrace tailWord_3173762 prefixEnd_3173762 1086443592649944583519427 := by
  unfold tailWord_3173762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28939152482002446060266885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77171073285339856160711693 28939152482002446060266885)
  ·
    refine ⟨5426091090375458636300041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28939152482002446060266885 5426091090375458636300041)
    ·
      refine ⟨4069568317781593977225031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5426091090375458636300041 4069568317781593977225031)
      ·
        refine ⟨6104352476672390965837547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069568317781593977225031 6104352476672390965837547)
        ·
          refine ⟨9156528715008586448756321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104352476672390965837547 9156528715008586448756321)
          ·
            refine ⟨6867396536256439836567241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9156528715008586448756321 6867396536256439836567241)
            ·
              refine ⟨5150547402192329877425431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6867396536256439836567241 5150547402192329877425431)
              ·
                refine ⟨7725821103288494816138147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5150547402192329877425431 7725821103288494816138147)
                ·
                  refine ⟨11588731654932742224207221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725821103288494816138147 11588731654932742224207221)
                  ·
                    refine ⟨1086443592649944583519427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11588731654932742224207221 1086443592649944583519427)
                    ·
                      rfl

theorem cell22_3173762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3173762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173762 prefixEnd_3173762 := by exact prefixLift 3173762
  have htrace : WordTrace (prefixWord ++ tailWord_3173762) baseStart_3173762 baseEnd_3173762 := by
    simpa [prefixWord, tailWord_3173762, baseEnd_3173762] using wordTrace_append hprefix tailTrace_3173762
  have hstable : (prefixWord ++ tailWord_3173762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173762).length < 2 ^ (prefixWord ++ tailWord_3173762).sum := by decide
  have hdescent : baseEnd_3173762 < baseStart_3173762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173771 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_3173771 : Nat := 118140960795 + 3173771 * 2 ^ 59
def prefixEnd_3173771 : Nat := 4983230072969 + 3 ^ 40 * 3173771 * 2
def baseEnd_3173771 : Nat := 1086446673533871560044399

theorem tailTrace_3173771 : CollatzResearch.WordTrace tailWord_3173771 prefixEnd_3173771 1086446673533871560044399 := by
  unfold tailWord_3173771
  simp only [CollatzResearch.WordTrace]
  refine ⟨115756938184977178778145167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77171292123318119185430111 115756938184977178778145167)
  ·
    refine ⟨173635407277465768167217751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115756938184977178778145167 173635407277465768167217751)
    ·
      refine ⟨260453110916198652250826627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173635407277465768167217751 260453110916198652250826627)
      ·
        refine ⟨390679666374297978376239941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260453110916198652250826627 390679666374297978376239941)
        ·
          refine ⟨73252437445180870945544989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390679666374297978376239941 73252437445180870945544989)
          ·
            refine ⟨27469664041942826604579371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73252437445180870945544989 27469664041942826604579371)
            ·
              refine ⟨41204496062914239906869057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27469664041942826604579371 41204496062914239906869057)
              ·
                refine ⟨30903372047185679930151793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41204496062914239906869057 30903372047185679930151793)
                ·
                  refine ⟨23177529035389259947613845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30903372047185679930151793 23177529035389259947613845)
                  ·
                    refine ⟨1086446673533871560044399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23177529035389259947613845 1086446673533871560044399)
                    ·
                      rfl

theorem cell22_3173771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_3173771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173771 prefixEnd_3173771 := by exact prefixLift 3173771
  have htrace : WordTrace (prefixWord ++ tailWord_3173771) baseStart_3173771 baseEnd_3173771 := by
    simpa [prefixWord, tailWord_3173771, baseEnd_3173771] using wordTrace_append hprefix tailTrace_3173771
  have hstable : (prefixWord ++ tailWord_3173771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173771).length < 2 ^ (prefixWord ++ tailWord_3173771).sum := by decide
  have hdescent : baseEnd_3173771 < baseStart_3173771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173850 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_3173850 : Nat := 118140960795 + 3173850 * 2 ^ 59
def prefixEnd_3173850 : Nat := 4983230072969 + 3 ^ 40 * 3173850 * 2
def baseEnd_3173850 : Nat := 1086473716848341687319157

theorem tailTrace_3173850 : CollatzResearch.WordTrace tailWord_3173850 prefixEnd_3173850 1086473716848341687319157 := by
  unfold tailWord_3173850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28939954887922743817567751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77173213034460650180180669 28939954887922743817567751)
  ·
    refine ⟨43409932331884115726351627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28939954887922743817567751 43409932331884115726351627)
    ·
      refine ⟨65114898497826173589527441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43409932331884115726351627 65114898497826173589527441)
      ·
        refine ⟨48836173873369630192145581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65114898497826173589527441 48836173873369630192145581)
        ·
          refine ⟨18313565202513611322054593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48836173873369630192145581 18313565202513611322054593)
          ·
            refine ⟨13735173901885208491540945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18313565202513611322054593 13735173901885208491540945)
            ·
              refine ⟨10301380426413906368655709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13735173901885208491540945 10301380426413906368655709)
              ·
                refine ⟨3863017659905214888245891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10301380426413906368655709 3863017659905214888245891)
                ·
                  refine ⟨5794526489857822332368837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863017659905214888245891 5794526489857822332368837)
                  ·
                    refine ⟨1086473716848341687319157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794526489857822332368837 1086473716848341687319157)
                    ·
                      rfl

theorem cell22_3173850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_3173850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173850 prefixEnd_3173850 := by exact prefixLift 3173850
  have htrace : WordTrace (prefixWord ++ tailWord_3173850) baseStart_3173850 baseEnd_3173850 := by
    simpa [prefixWord, tailWord_3173850, baseEnd_3173850] using wordTrace_append hprefix tailTrace_3173850
  have hstable : (prefixWord ++ tailWord_3173850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173850).length < 2 ^ (prefixWord ++ tailWord_3173850).sum := by decide
  have hdescent : baseEnd_3173850 < baseStart_3173850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173895 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3173895 : Nat := 118140960795 + 3173895 * 2 ^ 59
def prefixEnd_3173895 : Nat := 4983230072969 + 3 ^ 40 * 3173895 * 2
def baseEnd_3173895 : Nat := 1086489121267976569944019

theorem tailTrace_3173895 : CollatzResearch.WordTrace tailWord_3173895 prefixEnd_3173895 1086489121267976569944019 := by
  unfold tailWord_3173895
  simp only [CollatzResearch.WordTrace]
  refine ⟨115761460836527947955659139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77174307224351965303772759 115761460836527947955659139)
  ·
    refine ⟨173642191254791921933488709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115761460836527947955659139 173642191254791921933488709)
    ·
      refine ⟨32557910860273485362529133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173642191254791921933488709 32557910860273485362529133)
      ·
        refine ⟨12209216572602557010948425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32557910860273485362529133 12209216572602557010948425)
        ·
          refine ⟨9156912429451917758211319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12209216572602557010948425 9156912429451917758211319)
          ·
            refine ⟨13735368644177876637316979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156912429451917758211319 13735368644177876637316979)
            ·
              refine ⟨20603052966266814955975469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735368644177876637316979 20603052966266814955975469)
              ·
                refine ⟨7726144862350055608490801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20603052966266814955975469 7726144862350055608490801)
                ·
                  refine ⟨5794608646762541706368101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7726144862350055608490801 5794608646762541706368101)
                  ·
                    refine ⟨1086489121267976569944019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794608646762541706368101 1086489121267976569944019)
                    ·
                      rfl

theorem cell22_3173895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3173895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173895 prefixEnd_3173895 := by exact prefixLift 3173895
  have htrace : WordTrace (prefixWord ++ tailWord_3173895) baseStart_3173895 baseEnd_3173895 := by
    simpa [prefixWord, tailWord_3173895, baseEnd_3173895] using wordTrace_append hprefix tailTrace_3173895
  have hstable : (prefixWord ++ tailWord_3173895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173895).length < 2 ^ (prefixWord ++ tailWord_3173895).sum := by decide
  have hdescent : baseEnd_3173895 < baseStart_3173895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173925 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_3173925 : Nat := 118140960795 + 3173925 * 2 ^ 59
def prefixEnd_3173925 : Nat := 4983230072969 + 3 ^ 40 * 3173925 * 2
def baseEnd_3173925 : Nat := 1086499390881066491693927

theorem tailTrace_3173925 : CollatzResearch.WordTrace tailWord_3173925 prefixEnd_3173925 1086499390881066491693927 := by
  unfold tailWord_3173925
  simp only [CollatzResearch.WordTrace]
  refine ⟨115762555026419263079251229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77175036684279508719500819 115762555026419263079251229)
  ·
    refine ⟨43410958134907223654719211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115762555026419263079251229 43410958134907223654719211)
    ·
      refine ⟨65116437202360835482078817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43410958134907223654719211 65116437202360835482078817)
      ·
        refine ⟨48837327901770626611559113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65116437202360835482078817 48837327901770626611559113)
        ·
          refine ⟨36627995926327969958669335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48837327901770626611559113 36627995926327969958669335)
          ·
            refine ⟨54941993889491954938004003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36627995926327969958669335 54941993889491954938004003)
            ·
              refine ⟨82412990834237932407006005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54941993889491954938004003 82412990834237932407006005)
              ·
                refine ⟨7726217890709806163156813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82412990834237932407006005 7726217890709806163156813)
                ·
                  refine ⟨2897331709016177311183805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7726217890709806163156813 2897331709016177311183805)
                  ·
                    refine ⟨1086499390881066491693927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897331709016177311183805 1086499390881066491693927)
                    ·
                      rfl

theorem cell22_3173925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_3173925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173925 prefixEnd_3173925 := by exact prefixLift 3173925
  have htrace : WordTrace (prefixWord ++ tailWord_3173925) baseStart_3173925 baseEnd_3173925 := by
    simpa [prefixWord, tailWord_3173925, baseEnd_3173925] using wordTrace_append hprefix tailTrace_3173925
  have hstable : (prefixWord ++ tailWord_3173925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173925).length < 2 ^ (prefixWord ++ tailWord_3173925).sum := by decide
  have hdescent : baseEnd_3173925 < baseStart_3173925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173938 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3173938 : Nat := 118140960795 + 3173938 * 2 ^ 59
def prefixEnd_3173938 : Nat := 4983230072969 + 3 ^ 40 * 3173938 * 2
def baseEnd_3173938 : Nat := 362167947015579597039629

theorem tailTrace_3173938 : CollatzResearch.WordTrace tailWord_3173938 prefixEnd_3173938 362167947015579597039629 := by
  unfold tailWord_3173938
  simp only [CollatzResearch.WordTrace]
  refine ⟨28940757293843041574868617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77175352783581444199649645 28940757293843041574868617)
  ·
    refine ⟨21705567970382281181151463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28940757293843041574868617 21705567970382281181151463)
    ·
      refine ⟨32558351955573421771727195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21705567970382281181151463 32558351955573421771727195)
      ·
        refine ⟨48837527933360132657590793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32558351955573421771727195 48837527933360132657590793)
        ·
          refine ⟨36628145950020099493193095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48837527933360132657590793 36628145950020099493193095)
          ·
            refine ⟨54942218925030149239789643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36628145950020099493193095 54942218925030149239789643)
            ·
              refine ⟨82413328387545223859684465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54942218925030149239789643 82413328387545223859684465)
              ·
                refine ⟨61809996290658917894763349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82413328387545223859684465 61809996290658917894763349)
                ·
                  refine ⟨362167947015579597039629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61809996290658917894763349 362167947015579597039629)
                  ·
                    rfl

theorem cell22_3173938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3173938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173938 prefixEnd_3173938 := by exact prefixLift 3173938
  have htrace : WordTrace (prefixWord ++ tailWord_3173938) baseStart_3173938 baseEnd_3173938 := by
    simpa [prefixWord, tailWord_3173938, baseEnd_3173938] using wordTrace_append hprefix tailTrace_3173938
  have hstable : (prefixWord ++ tailWord_3173938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173938).length < 2 ^ (prefixWord ++ tailWord_3173938).sum := by decide
  have hdescent : baseEnd_3173938 < baseStart_3173938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173970 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_3173970 : Nat := 118140960795 + 3173970 * 2 ^ 59
def prefixEnd_3173970 : Nat := 4983230072969 + 3 ^ 40 * 3173970 * 2
def baseEnd_3173970 : Nat := 1086514795300701374318789

theorem tailTrace_3173970 : CollatzResearch.WordTrace tailWord_3173970 prefixEnd_3173970 1086514795300701374318789 := by
  unfold tailWord_3173970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941049077814058941159841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77176130874170823843092909 28941049077814058941159841)
  ·
    refine ⟨21705786808360544205869881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28941049077814058941159841 21705786808360544205869881)
    ·
      refine ⟨16279340106270408154402411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21705786808360544205869881 16279340106270408154402411)
      ·
        refine ⟨24419010159405612231603617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16279340106270408154402411 24419010159405612231603617)
        ·
          refine ⟨18314257619554209173702713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24419010159405612231603617 18314257619554209173702713)
          ·
            refine ⟨13735693214665656880277035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18314257619554209173702713 13735693214665656880277035)
            ·
              refine ⟨20603539821998485320415553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735693214665656880277035 20603539821998485320415553)
              ·
                refine ⟨15452654866498863990311665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20603539821998485320415553 15452654866498863990311665)
                ·
                  refine ⟨11589491149874147992733749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15452654866498863990311665 11589491149874147992733749)
                  ·
                    refine ⟨1086514795300701374318789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11589491149874147992733749 1086514795300701374318789)
                    ·
                      rfl

theorem cell22_3173970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_3173970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3173970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3173970 prefixEnd_3173970 := by exact prefixLift 3173970
  have htrace : WordTrace (prefixWord ++ tailWord_3173970) baseStart_3173970 baseEnd_3173970 := by
    simpa [prefixWord, tailWord_3173970, baseEnd_3173970] using wordTrace_append hprefix tailTrace_3173970
  have hstable : (prefixWord ++ tailWord_3173970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173970).length < 2 ^ (prefixWord ++ tailWord_3173970).sum := by decide
  have hdescent : baseEnd_3173970 < baseStart_3173970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174000 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_3174000 : Nat := 118140960795 + 3174000 * 2 ^ 59
def prefixEnd_3174000 : Nat := 4983230072969 + 3 ^ 40 * 3174000 * 2
def baseEnd_3174000 : Nat := 362175021637930432022899

theorem tailTrace_3174000 : CollatzResearch.WordTrace tailWord_3174000 prefixEnd_3174000 362175021637930432022899 := by
  unfold tailWord_3174000
  simp only [CollatzResearch.WordTrace]
  refine ⟨57882645250573775444115727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77176860334098367258820969 57882645250573775444115727)
  ·
    refine ⟨86823967875860663166173591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57882645250573775444115727 86823967875860663166173591)
    ·
      refine ⟨130235951813790994749260387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86823967875860663166173591 130235951813790994749260387)
      ·
        refine ⟨195353927720686492123890581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130235951813790994749260387 195353927720686492123890581)
        ·
          refine ⟨9157215361907179318307371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195353927720686492123890581 9157215361907179318307371)
          ·
            refine ⟨13735823042860768977461057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157215361907179318307371 13735823042860768977461057)
            ·
              refine ⟨10301867282145576733095793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13735823042860768977461057 10301867282145576733095793)
              ·
                refine ⟨7726400461609182549821845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10301867282145576733095793 7726400461609182549821845)
                ·
                  refine ⟨362175021637930432022899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7726400461609182549821845 362175021637930432022899)
                  ·
                    rfl

theorem cell22_3174000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_3174000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174000 prefixEnd_3174000 := by exact prefixLift 3174000
  have htrace : WordTrace (prefixWord ++ tailWord_3174000) baseStart_3174000 baseEnd_3174000 := by
    simpa [prefixWord, tailWord_3174000, baseEnd_3174000] using wordTrace_append hprefix tailTrace_3174000
  have hstable : (prefixWord ++ tailWord_3174000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174000).length < 2 ^ (prefixWord ++ tailWord_3174000).sum := by decide
  have hdescent : baseEnd_3174000 < baseStart_3174000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174002 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_3174002 : Nat := 118140960795 + 3174002 * 2 ^ 59
def prefixEnd_3174002 : Nat := 4983230072969 + 3 ^ 40 * 3174002 * 2
def baseEnd_3174002 : Nat := 1086525749554663957518691

theorem tailTrace_3174002 : CollatzResearch.WordTrace tailWord_3174002 prefixEnd_3174002 1086525749554663957518691 := by
  unfold tailWord_3174002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941340861785076307451065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77176908964760203486536173 28941340861785076307451065)
  ·
    refine ⟨21706005646338807230588299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28941340861785076307451065 21706005646338807230588299)
    ·
      refine ⟨32559008469508210845882449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21706005646338807230588299 32559008469508210845882449)
      ·
        refine ⟨24419256352131158134411837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32559008469508210845882449 24419256352131158134411837)
        ·
          refine ⟨9157221132049184300404439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24419256352131158134411837 9157221132049184300404439)
          ·
            refine ⟨13735831698073776450606659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157221132049184300404439 13735831698073776450606659)
            ·
              refine ⟨20603747547110664675909989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735831698073776450606659 20603747547110664675909989)
              ·
                refine ⟨3863202665083249626733123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20603747547110664675909989 3863202665083249626733123)
                ·
                  refine ⟨5794803997624874440099685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863202665083249626733123 5794803997624874440099685)
                  ·
                    refine ⟨1086525749554663957518691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794803997624874440099685 1086525749554663957518691)
                    ·
                      rfl

theorem cell22_3174002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_3174002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174002 prefixEnd_3174002 := by exact prefixLift 3174002
  have htrace : WordTrace (prefixWord ++ tailWord_3174002) baseStart_3174002 baseEnd_3174002 := by
    simpa [prefixWord, tailWord_3174002, baseEnd_3174002] using wordTrace_append hprefix tailTrace_3174002
  have hstable : (prefixWord ++ tailWord_3174002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174002).length < 2 ^ (prefixWord ++ tailWord_3174002).sum := by decide
  have hdescent : baseEnd_3174002 < baseStart_3174002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174034 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_3174034 : Nat := 118140960795 + 3174034 * 2 ^ 59
def prefixEnd_3174034 : Nat := 4983230072969 + 3 ^ 40 * 3174034 * 2
def baseEnd_3174034 : Nat := 362178901269542180239531

theorem tailTrace_3174034 : CollatzResearch.WordTrace tailWord_3174034 prefixEnd_3174034 362178901269542180239531 := by
  unfold tailWord_3174034
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941632645756093673742289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77177687055349583129979437 28941632645756093673742289)
  ·
    refine ⟨21706224484317070255306717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28941632645756093673742289 21706224484317070255306717)
    ·
      refine ⟨8139834181618901345740019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21706224484317070255306717 8139834181618901345740019)
      ·
        refine ⟨12209751272428352018610029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8139834181618901345740019 12209751272428352018610029)
        ·
          refine ⟨4578656727160632006978761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12209751272428352018610029 4578656727160632006978761)
          ·
            refine ⟨3433992545370474005234071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4578656727160632006978761 3433992545370474005234071)
            ·
              refine ⟨5150988818055711007851107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433992545370474005234071 5150988818055711007851107)
              ·
                refine ⟨7726483227083566511776661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5150988818055711007851107 7726483227083566511776661)
                ·
                  refine ⟨362178901269542180239531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7726483227083566511776661 362178901269542180239531)
                  ·
                    rfl

theorem cell22_3174034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_3174034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174034 prefixEnd_3174034 := by exact prefixLift 3174034
  have htrace : WordTrace (prefixWord ++ tailWord_3174034) baseStart_3174034 baseEnd_3174034 := by
    simpa [prefixWord, tailWord_3174034, baseEnd_3174034] using wordTrace_append hprefix tailTrace_3174034
  have hstable : (prefixWord ++ tailWord_3174034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174034).length < 2 ^ (prefixWord ++ tailWord_3174034).sum := by decide
  have hdescent : baseEnd_3174034 < baseStart_3174034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174049 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_3174049 : Nat := 118140960795 + 3174049 * 2 ^ 59
def prefixEnd_3174049 : Nat := 4983230072969 + 3 ^ 40 * 3174049 * 2
def baseEnd_3174049 : Nat := 1086541838615171501593547

theorem tailTrace_3174049 : CollatzResearch.WordTrace tailWord_3174049 prefixEnd_3174049 1086541838615171501593547 := by
  unfold tailWord_3174049
  simp only [CollatzResearch.WordTrace]
  refine ⟨115767077677970032256765201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77178051785313354837843467 115767077677970032256765201)
  ·
    refine ⟨86825308258477524192573901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115767077677970032256765201 86825308258477524192573901)
    ·
      refine ⟨32559490596929071572215213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86825308258477524192573901 32559490596929071572215213)
      ·
        refine ⟨12209808973848401839580705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32559490596929071572215213 12209808973848401839580705)
        ·
          refine ⟨9157356730386301379685529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12209808973848401839580705 9157356730386301379685529)
          ·
            refine ⟨6868017547789726034764147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9157356730386301379685529 6868017547789726034764147)
            ·
              refine ⟨10302026321684589052146221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6868017547789726034764147 10302026321684589052146221)
              ·
                refine ⟨3863259870631720894554833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10302026321684589052146221 3863259870631720894554833)
                ·
                  refine ⟨2897444902973790670916125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3863259870631720894554833 2897444902973790670916125)
                  ·
                    refine ⟨1086541838615171501593547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897444902973790670916125 1086541838615171501593547)
                    ·
                      rfl

theorem cell22_3174049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_3174049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174049 prefixEnd_3174049 := by exact prefixLift 3174049
  have htrace : WordTrace (prefixWord ++ tailWord_3174049) baseStart_3174049 baseEnd_3174049 := by
    simpa [prefixWord, tailWord_3174049, baseEnd_3174049] using wordTrace_append hprefix tailTrace_3174049
  have hstable : (prefixWord ++ tailWord_3174049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174049).length < 2 ^ (prefixWord ++ tailWord_3174049).sum := by decide
  have hdescent : baseEnd_3174049 < baseStart_3174049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174105 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_3174105 : Nat := 118140960795 + 3174105 * 2 ^ 59
def prefixEnd_3174105 : Nat := 4983230072969 + 3 ^ 40 * 3174105 * 2
def baseEnd_3174105 : Nat := 1086561008559606022193375

theorem tailTrace_3174105 : CollatzResearch.WordTrace tailWord_3174105 prefixEnd_3174105 1086561008559606022193375 := by
  unfold tailWord_3174105
  simp only [CollatzResearch.WordTrace]
  refine ⟨115769120165767153820803769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77179413443844769213869179 115769120165767153820803769)
  ·
    refine ⟨86826840124325365365602827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115769120165767153820803769 86826840124325365365602827)
    ·
      refine ⟨130240260186488048048404241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86826840124325365365602827 130240260186488048048404241)
      ·
        refine ⟨97680195139866036036303181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130240260186488048048404241 97680195139866036036303181)
        ·
          refine ⟨36630073177449763513613693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97680195139866036036303181 36630073177449763513613693)
          ·
            refine ⟨13736277441543661317605135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36630073177449763513613693 13736277441543661317605135)
            ·
              refine ⟨20604416162315491976407703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736277441543661317605135 20604416162315491976407703)
              ·
                refine ⟨30906624243473237964611555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20604416162315491976407703 30906624243473237964611555)
                ·
                  refine ⟨46359936365209856946917333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30906624243473237964611555 46359936365209856946917333)
                  ·
                    refine ⟨1086561008559606022193375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46359936365209856946917333 1086561008559606022193375)
                    ·
                      rfl

theorem cell22_3174105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_3174105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174105 prefixEnd_3174105 := by exact prefixLift 3174105
  have htrace : WordTrace (prefixWord ++ tailWord_3174105) baseStart_3174105 baseEnd_3174105 := by
    simpa [prefixWord, tailWord_3174105, baseEnd_3174105] using wordTrace_append hprefix tailTrace_3174105
  have hstable : (prefixWord ++ tailWord_3174105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174105).length < 2 ^ (prefixWord ++ tailWord_3174105).sum := by decide
  have hdescent : baseEnd_3174105 < baseStart_3174105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174152 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_3174152 : Nat := 118140960795 + 3174152 * 2 ^ 59
def prefixEnd_3174152 : Nat := 4983230072969 + 3 ^ 40 * 3174152 * 2
def baseEnd_3174152 : Nat := 362192365873371188756077

theorem tailTrace_3174152 : CollatzResearch.WordTrace tailWord_3174152 prefixEnd_3174152 362192365873371188756077 := by
  unfold tailWord_3174152
  simp only [CollatzResearch.WordTrace]
  refine ⟨57885417198298440423882355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77180556264397920565176473 57885417198298440423882355)
  ·
    refine ⟨86828125797447660635823533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57885417198298440423882355 86828125797447660635823533)
    ·
      refine ⟨32560547174042872738433825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86828125797447660635823533 32560547174042872738433825)
      ·
        refine ⟨24420410380532154553825369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32560547174042872738433825 24420410380532154553825369)
        ·
          refine ⟨18315307785399115915369027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24420410380532154553825369 18315307785399115915369027)
          ·
            refine ⟨27472961678098673873053541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18315307785399115915369027 27472961678098673873053541)
            ·
              refine ⟨5151180314643501351197539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27472961678098673873053541 5151180314643501351197539)
              ·
                refine ⟨7726770471965252026796309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151180314643501351197539 7726770471965252026796309)
                ·
                  refine ⟨362192365873371188756077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7726770471965252026796309 362192365873371188756077)
                  ·
                    rfl

theorem cell22_3174152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_3174152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174152 prefixEnd_3174152 := by exact prefixLift 3174152
  have htrace : WordTrace (prefixWord ++ tailWord_3174152) baseStart_3174152 baseEnd_3174152 := by
    simpa [prefixWord, tailWord_3174152, baseEnd_3174152] using wordTrace_append hprefix tailTrace_3174152
  have hstable : (prefixWord ++ tailWord_3174152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174152).length < 2 ^ (prefixWord ++ tailWord_3174152).sum := by decide
  have hdescent : baseEnd_3174152 < baseStart_3174152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174184 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3174184 : Nat := 118140960795 + 3174184 * 2 ^ 59
def prefixEnd_3174184 : Nat := 4983230072969 + 3 ^ 40 * 3174184 * 2
def baseEnd_3174184 : Nat := 1086588051874076149468133

theorem tailTrace_3174184 : CollatzResearch.WordTrace tailWord_3174184 prefixEnd_3174184 1086588051874076149468133 := by
  unfold tailWord_3174184
  simp only [CollatzResearch.WordTrace]
  refine ⟨57886000766240475156464803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77181334354987300208619737 57886000766240475156464803)
  ·
    refine ⟨86829001149360712734697205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57886000766240475156464803 86829001149360712734697205)
    ·
      refine ⟨8140218857752566818877863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86829001149360712734697205 8140218857752566818877863)
      ·
        refine ⟨12210328286628850228316795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140218857752566818877863 12210328286628850228316795)
        ·
          refine ⟨18315492429943275342475193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12210328286628850228316795 18315492429943275342475193)
          ·
            refine ⟨13736619322457456506856395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18315492429943275342475193 13736619322457456506856395)
            ·
              refine ⟨20604928983686184760284593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736619322457456506856395 20604928983686184760284593)
              ·
                refine ⟨15453696737764638570213445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20604928983686184760284593 15453696737764638570213445)
                ·
                  refine ⟨2897568138330869731915021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15453696737764638570213445 2897568138330869731915021)
                  ·
                    refine ⟨1086588051874076149468133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897568138330869731915021 1086588051874076149468133)
                    ·
                      rfl

theorem cell22_3174184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3174184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174184 prefixEnd_3174184 := by exact prefixLift 3174184
  have htrace : WordTrace (prefixWord ++ tailWord_3174184) baseStart_3174184 baseEnd_3174184 := by
    simpa [prefixWord, tailWord_3174184, baseEnd_3174184] using wordTrace_append hprefix tailTrace_3174184
  have hstable : (prefixWord ++ tailWord_3174184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174184).length < 2 ^ (prefixWord ++ tailWord_3174184).sum := by decide
  have hdescent : baseEnd_3174184 < baseStart_3174184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174257 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3174257 : Nat := 118140960795 + 3174257 * 2 ^ 59
def prefixEnd_3174257 : Nat := 4983230072969 + 3 ^ 40 * 3174257 * 2
def baseEnd_3174257 : Nat := 1086613041265928292392909

theorem tailTrace_3174257 : CollatzResearch.WordTrace tailWord_3174257 prefixEnd_3174257 1086613041265928292392909 := by
  unfold tailWord_3174257
  simp only [CollatzResearch.WordTrace]
  refine ⟨115774664061216483780337025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77183109374144322520224683 115774664061216483780337025)
  ·
    refine ⟨86830998045912362835252769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115774664061216483780337025 86830998045912362835252769)
    ·
      refine ⟨65123248534434272126439577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86830998045912362835252769 65123248534434272126439577)
      ·
        refine ⟨48842436400825704094829683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65123248534434272126439577 48842436400825704094829683)
        ·
          refine ⟨73263654601238556142244525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48842436400825704094829683 73263654601238556142244525)
          ·
            refine ⟨27473870475464458553341697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73263654601238556142244525 27473870475464458553341697)
            ·
              refine ⟨20605402856598343915006273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27473870475464458553341697 20605402856598343915006273)
              ·
                refine ⟨15454052142448757936254705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20605402856598343915006273 15454052142448757936254705)
                ·
                  refine ⟨11590539106836568452191029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15454052142448757936254705 11590539106836568452191029)
                  ·
                    refine ⟨1086613041265928292392909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11590539106836568452191029 1086613041265928292392909)
                    ·
                      rfl

theorem cell22_3174257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3174257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174257 prefixEnd_3174257 := by exact prefixLift 3174257
  have htrace : WordTrace (prefixWord ++ tailWord_3174257) baseStart_3174257 baseEnd_3174257 := by
    simpa [prefixWord, tailWord_3174257, baseEnd_3174257] using wordTrace_append hprefix tailTrace_3174257
  have hstable : (prefixWord ++ tailWord_3174257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174257).length < 2 ^ (prefixWord ++ tailWord_3174257).sum := by decide
  have hdescent : baseEnd_3174257 < baseStart_3174257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174272 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_3174272 : Nat := 118140960795 + 3174272 * 2 ^ 59
def prefixEnd_3174272 : Nat := 4983230072969 + 3 ^ 40 * 3174272 * 2
def baseEnd_3174272 : Nat := 1086618176072473253267863

theorem tailTrace_3174272 : CollatzResearch.WordTrace tailWord_3174272 prefixEnd_3174272 1086618176072473253267863 := by
  unfold tailWord_3174272
  simp only [CollatzResearch.WordTrace]
  refine ⟨57887605578081070671066535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77183474104108094228088713 57887605578081070671066535)
  ·
    refine ⟨86831408367121606006599803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57887605578081070671066535 86831408367121606006599803)
    ·
      refine ⟨130247112550682409009899705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86831408367121606006599803 130247112550682409009899705)
      ·
        refine ⟨97685334413011806757424779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130247112550682409009899705 97685334413011806757424779)
        ·
          refine ⟨146528001619517710136137169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97685334413011806757424779 146528001619517710136137169)
          ·
            refine ⟨109896001214638282602102877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146528001619517710136137169 109896001214638282602102877)
            ·
              refine ⟨41211000455489355975788579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109896001214638282602102877 41211000455489355975788579)
              ·
                refine ⟨61816500683234033963682869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41211000455489355975788579 61816500683234033963682869)
                ·
                  refine ⟨5795296939053190684095269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61816500683234033963682869 5795296939053190684095269)
                  ·
                    refine ⟨1086618176072473253267863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5795296939053190684095269 1086618176072473253267863)
                    ·
                      rfl

theorem cell22_3174272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_3174272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174272 prefixEnd_3174272 := by exact prefixLift 3174272
  have htrace : WordTrace (prefixWord ++ tailWord_3174272) baseStart_3174272 baseEnd_3174272 := by
    simpa [prefixWord, tailWord_3174272, baseEnd_3174272] using wordTrace_append hprefix tailTrace_3174272
  have hstable : (prefixWord ++ tailWord_3174272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174272).length < 2 ^ (prefixWord ++ tailWord_3174272).sum := by decide
  have hdescent : baseEnd_3174272 < baseStart_3174272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174319 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 4, 3]
def baseStart_3174319 : Nat := 118140960795 + 3174319 * 2 ^ 59
def prefixEnd_3174319 : Nat := 4983230072969 + 3 ^ 40 * 3174319 * 2
def baseEnd_3174319 : Nat := 1086634265132980797342719

theorem tailTrace_3174319 : CollatzResearch.WordTrace tailWord_3174319 prefixEnd_3174319 1086634265132980797342719 := by
  unfold tailWord_3174319
  simp only [CollatzResearch.WordTrace]
  refine ⟨115776925386991868369094011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77184616924661245579396007 115776925386991868369094011)
  ·
    refine ⟨173665388080487802553641017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115776925386991868369094011 173665388080487802553641017)
    ·
      refine ⟨130249041060365851915230763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173665388080487802553641017 130249041060365851915230763)
      ·
        refine ⟨195373561590548777872846145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130249041060365851915230763 195373561590548777872846145)
        ·
          refine ⟨146530171192911583404634609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195373561590548777872846145 146530171192911583404634609)
          ·
            refine ⟨109897628394683687553475957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146530171192911583404634609 109897628394683687553475957)
            ·
              refine ⟨10302902662001595708138371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109897628394683687553475957 10302902662001595708138371)
              ·
                refine ⟨15454353993002393562207557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10302902662001595708138371 15454353993002393562207557)
                ·
                  refine ⟨2897691373687948792913917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15454353993002393562207557 2897691373687948792913917)
                  ·
                    refine ⟨1086634265132980797342719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897691373687948792913917 1086634265132980797342719)
                    ·
                      rfl

theorem cell22_3174319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_3174319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174319 prefixEnd_3174319 := by exact prefixLift 3174319
  have htrace : WordTrace (prefixWord ++ tailWord_3174319) baseStart_3174319 baseEnd_3174319 := by
    simpa [prefixWord, tailWord_3174319, baseEnd_3174319] using wordTrace_append hprefix tailTrace_3174319
  have hstable : (prefixWord ++ tailWord_3174319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174319).length < 2 ^ (prefixWord ++ tailWord_3174319).sum := by decide
  have hdescent : baseEnd_3174319 < baseStart_3174319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174321 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 4]
def baseStart_3174321 : Nat := 118140960795 + 3174321 * 2 ^ 59
def prefixEnd_3174321 : Nat := 4983230072969 + 3 ^ 40 * 3174321 * 2
def baseEnd_3174321 : Nat := 362211649924617819597571

theorem tailTrace_3174321 : CollatzResearch.WordTrace tailWord_3174321 prefixEnd_3174321 362211649924617819597571 := by
  unfold tailWord_3174321
  simp only [CollatzResearch.WordTrace]
  refine ⟨115776998332984622710666817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77184665555323081807111211 115776998332984622710666817)
  ·
    refine ⟨86832748749738467033000113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115776998332984622710666817 86832748749738467033000113)
    ·
      refine ⟨65124561562303850274750085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86832748749738467033000113 65124561562303850274750085)
      ·
        refine ⟨12210855292931971926515641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65124561562303850274750085 12210855292931971926515641)
        ·
          refine ⟨9158141469698978944886731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12210855292931971926515641 9158141469698978944886731)
          ·
            refine ⟨13737212204548468417330097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158141469698978944886731 13737212204548468417330097)
            ·
              refine ⟨10302909153411351312997573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13737212204548468417330097 10302909153411351312997573)
              ·
                refine ⟨1931795466264628371187045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10302909153411351312997573 1931795466264628371187045)
                ·
                  refine ⟨362211649924617819597571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931795466264628371187045 362211649924617819597571)
                  ·
                    rfl

theorem cell22_3174321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_3174321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174321 prefixEnd_3174321 := by exact prefixLift 3174321
  have htrace : WordTrace (prefixWord ++ tailWord_3174321) baseStart_3174321 baseEnd_3174321 := by
    simpa [prefixWord, tailWord_3174321, baseEnd_3174321] using wordTrace_append hprefix tailTrace_3174321
  have hstable : (prefixWord ++ tailWord_3174321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174321).length < 2 ^ (prefixWord ++ tailWord_3174321).sum := by decide
  have hdescent : baseEnd_3174321 < baseStart_3174321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174334 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3174334 : Nat := 118140960795 + 3174334 * 2 ^ 59
def prefixEnd_3174334 : Nat := 4983230072969 + 3 ^ 40 * 3174334 * 2
def baseEnd_3174334 : Nat := 1086639399939525758217673

theorem tailTrace_3174334 : CollatzResearch.WordTrace tailWord_3174334 prefixEnd_3174334 1086639399939525758217673 := by
  unfold tailWord_3174334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14472184060242190741361257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77184981654625017287260037 14472184060242190741361257)
  ·
    refine ⟨10854138045181643056020943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14472184060242190741361257 10854138045181643056020943)
    ·
      refine ⟨16281207067772464584031415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10854138045181643056020943 16281207067772464584031415)
      ·
        refine ⟨24421810601658696876047123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16281207067772464584031415 24421810601658696876047123)
        ·
          refine ⟨36632715902488045314070685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24421810601658696876047123 36632715902488045314070685)
          ·
            refine ⟨13737268463433016992776507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36632715902488045314070685 13737268463433016992776507)
            ·
              refine ⟨20605902695149525489164761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737268463433016992776507 20605902695149525489164761)
              ·
                refine ⟨15454427021362144116873571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20605902695149525489164761 15454427021362144116873571)
                ·
                  refine ⟨23181640532043216175310357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15454427021362144116873571 23181640532043216175310357)
                  ·
                    refine ⟨1086639399939525758217673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23181640532043216175310357 1086639399939525758217673)
                    ·
                      rfl

theorem cell22_3174334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3174334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174334 prefixEnd_3174334 := by exact prefixLift 3174334
  have htrace : WordTrace (prefixWord ++ tailWord_3174334) baseStart_3174334 baseEnd_3174334 := by
    simpa [prefixWord, tailWord_3174334, baseEnd_3174334] using wordTrace_append hprefix tailTrace_3174334
  have hstable : (prefixWord ++ tailWord_3174334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174334).length < 2 ^ (prefixWord ++ tailWord_3174334).sum := by decide
  have hdescent : baseEnd_3174334 < baseStart_3174334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174347 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_3174347 : Nat := 118140960795 + 3174347 * 2 ^ 59
def prefixEnd_3174347 : Nat := 4983230072969 + 3 ^ 40 * 3174347 * 2
def baseEnd_3174347 : Nat := 1086643850105198057642633

theorem tailTrace_3174347 : CollatzResearch.WordTrace tailWord_3174347 prefixEnd_3174347 1086643850105198057642633 := by
  unfold tailWord_3174347
  simp only [CollatzResearch.WordTrace]
  refine ⟨115777946630890429151113295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77185297753926952767408863 115777946630890429151113295)
  ·
    refine ⟨173666919946335643726669943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115777946630890429151113295 173666919946335643726669943)
    ·
      refine ⟨260500379919503465590004915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173666919946335643726669943 260500379919503465590004915)
      ·
        refine ⟨390750569879255198385007373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260500379919503465590004915 390750569879255198385007373)
        ·
          refine ⟨146531463704720699394377765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390750569879255198385007373 146531463704720699394377765)
          ·
            refine ⟨27474649444635131136445831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146531463704720699394377765 27474649444635131136445831)
            ·
              refine ⟨41211974166952696704668747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27474649444635131136445831 41211974166952696704668747)
              ·
                refine ⟨61817961250429045057003121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41211974166952696704668747 61817961250429045057003121)
                ·
                  refine ⟨46363470937821783792752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61817961250429045057003121 46363470937821783792752341)
                  ·
                    refine ⟨1086643850105198057642633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46363470937821783792752341 1086643850105198057642633)
                    ·
                      rfl

theorem cell22_3174347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_3174347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174347 prefixEnd_3174347 := by exact prefixLift 3174347
  have htrace : WordTrace (prefixWord ++ tailWord_3174347) baseStart_3174347 baseEnd_3174347 := by
    simpa [prefixWord, tailWord_3174347, baseEnd_3174347] using wordTrace_append hprefix tailTrace_3174347
  have hstable : (prefixWord ++ tailWord_3174347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174347).length < 2 ^ (prefixWord ++ tailWord_3174347).sum := by decide
  have hdescent : baseEnd_3174347 < baseStart_3174347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174456 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_3174456 : Nat := 118140960795 + 3174456 * 2 ^ 59
def prefixEnd_3174456 : Nat := 4983230072969 + 3 ^ 40 * 3174456 * 2
def baseEnd_3174456 : Nat := 362227054344252702222433

theorem tailTrace_3174456 : CollatzResearch.WordTrace tailWord_3174456 prefixEnd_3174456 362227054344252702222433 := by
  unfold tailWord_3174456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57890961093747770383415611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77187948124997027177887481 57890961093747770383415611)
  ·
    refine ⟨86836441640621655575123417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57890961093747770383415611 86836441640621655575123417)
    ·
      refine ⟨65127331230466241681342563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86836441640621655575123417 65127331230466241681342563)
      ·
        refine ⟨97690996845699362522013845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65127331230466241681342563 97690996845699362522013845)
        ·
          refine ⟨4579265477142157618219399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97690996845699362522013845 4579265477142157618219399)
          ·
            refine ⟨6868898215713236427329099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579265477142157618219399 6868898215713236427329099)
            ·
              refine ⟨10303347323569854640993649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6868898215713236427329099 10303347323569854640993649)
              ·
                refine ⟨7727510492677390980745237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10303347323569854640993649 7727510492677390980745237)
                ·
                  refine ⟨362227054344252702222433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7727510492677390980745237 362227054344252702222433)
                  ·
                    rfl

theorem cell22_3174456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_3174456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174456 prefixEnd_3174456 := by exact prefixLift 3174456
  have htrace : WordTrace (prefixWord ++ tailWord_3174456) baseStart_3174456 baseEnd_3174456 := by
    simpa [prefixWord, tailWord_3174456, baseEnd_3174456] using wordTrace_append hprefix tailTrace_3174456
  have hstable : (prefixWord ++ tailWord_3174456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174456).length < 2 ^ (prefixWord ++ tailWord_3174456).sum := by decide
  have hdescent : baseEnd_3174456 < baseStart_3174456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174471 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 4, 3]
def baseStart_3174471 : Nat := 118140960795 + 3174471 * 2 ^ 59
def prefixEnd_3174471 : Nat := 4983230072969 + 3 ^ 40 * 3174471 * 2
def baseEnd_3174471 : Nat := 1086686297839303067542253

theorem tailTrace_3174471 : CollatzResearch.WordTrace tailWord_3174471 prefixEnd_3174471 1086686297839303067542253 := by
  unfold tailWord_3174471
  simp only [CollatzResearch.WordTrace]
  refine ⟨115782469282441198328627267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77188312854960798885751511 115782469282441198328627267)
  ·
    refine ⟨173673703923661797492940901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115782469282441198328627267 173673703923661797492940901)
    ·
      refine ⟨32563819485686587029926419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173673703923661797492940901 32563819485686587029926419)
      ·
        refine ⟨48845729228529880544889629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32563819485686587029926419 48845729228529880544889629)
        ·
          refine ⟨18317148460698705204333611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48845729228529880544889629 18317148460698705204333611)
          ·
            refine ⟨27475722691048057806500417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317148460698705204333611 27475722691048057806500417)
            ·
              refine ⟨20606792018286043354875313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27475722691048057806500417 20606792018286043354875313)
              ·
                refine ⟨15455094013714532516156485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20606792018286043354875313 15455094013714532516156485)
                ·
                  refine ⟨2897830127571474846779341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15455094013714532516156485 2897830127571474846779341)
                  ·
                    refine ⟨1086686297839303067542253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897830127571474846779341 1086686297839303067542253)
                    ·
                      rfl

theorem cell22_3174471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_3174471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174471 prefixEnd_3174471 := by exact prefixLift 3174471
  have htrace : WordTrace (prefixWord ++ tailWord_3174471) baseStart_3174471 baseEnd_3174471 := by
    simpa [prefixWord, tailWord_3174471, baseEnd_3174471] using wordTrace_append hprefix tailTrace_3174471
  have hstable : (prefixWord ++ tailWord_3174471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174471).length < 2 ^ (prefixWord ++ tailWord_3174471).sum := by decide
  have hdescent : baseEnd_3174471 < baseStart_3174471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174488 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_3174488 : Nat := 118140960795 + 3174488 * 2 ^ 59
def prefixEnd_3174488 : Nat := 4983230072969 + 3 ^ 40 * 3174488 * 2
def baseEnd_3174488 : Nat := 1086692117286720689867201

theorem tailTrace_3174488 : CollatzResearch.WordTrace tailWord_3174488 prefixEnd_3174488 1086692117286720689867201 := by
  unfold tailWord_3174488
  simp only [CollatzResearch.WordTrace]
  refine ⟨57891544661689805115998059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77188726215586406821330745 57891544661689805115998059)
  ·
    refine ⟨86837316992534707673997089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57891544661689805115998059 86837316992534707673997089)
    ·
      refine ⟨65127987744401030755497817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86837316992534707673997089 65127987744401030755497817)
      ·
        refine ⟨48845990808300773066623363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65127987744401030755497817 48845990808300773066623363)
        ·
          refine ⟨73268986212451159599935045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48845990808300773066623363 73268986212451159599935045)
          ·
            refine ⟨13737934914834592424987821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73268986212451159599935045 13737934914834592424987821)
            ·
              refine ⟨5151725593062972159370433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13737934914834592424987821 5151725593062972159370433)
              ·
                refine ⟨3863794194797229119527825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151725593062972159370433 3863794194797229119527825)
                ·
                  refine ⟨2897845646097921839645869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3863794194797229119527825 2897845646097921839645869)
                  ·
                    refine ⟨1086692117286720689867201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897845646097921839645869 1086692117286720689867201)
                    ·
                      rfl

theorem cell22_3174488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_3174488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174488 prefixEnd_3174488 := by exact prefixLift 3174488
  have htrace : WordTrace (prefixWord ++ tailWord_3174488) baseStart_3174488 baseEnd_3174488 := by
    simpa [prefixWord, tailWord_3174488, baseEnd_3174488] using wordTrace_append hprefix tailTrace_3174488
  have hstable : (prefixWord ++ tailWord_3174488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174488).length < 2 ^ (prefixWord ++ tailWord_3174488).sum := by decide
  have hdescent : baseEnd_3174488 < baseStart_3174488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174518 : List Nat := [5, 1, 1, 2, 1, 2, 4, 6]
def baseStart_3174518 : Nat := 118140960795 + 3174518 * 2 ^ 59
def prefixEnd_3174518 : Nat := 4983230072969 + 3 ^ 40 * 3174518 * 2
def baseEnd_3174518 : Nat := 120744709655534512401901

theorem tailTrace_3174518 : CollatzResearch.WordTrace tailWord_3174518 prefixEnd_3174518 120744709655534512401901 := by
  unfold tailWord_3174518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236511469579432834724263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77189455675513950237058805 7236511469579432834724263)
  ·
    refine ⟨10854767204369149252086395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7236511469579432834724263 10854767204369149252086395)
    ·
      refine ⟨16282150806553723878129593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10854767204369149252086395 16282150806553723878129593)
      ·
        refine ⟨12211613104915292908597195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16282150806553723878129593 12211613104915292908597195)
        ·
          refine ⟨18317419657372939362895793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12211613104915292908597195 18317419657372939362895793)
          ·
            refine ⟨13738064743029704522171845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18317419657372939362895793 13738064743029704522171845)
            ·
              refine ⟨2575887139318069597907221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13738064743029704522171845 2575887139318069597907221)
              ·
                refine ⟨120744709655534512401901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2575887139318069597907221 120744709655534512401901)
                ·
                  rfl

theorem cell22_3174518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_3174518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174518 prefixEnd_3174518 := by exact prefixLift 3174518
  have htrace : WordTrace (prefixWord ++ tailWord_3174518) baseStart_3174518 baseEnd_3174518 := by
    simpa [prefixWord, tailWord_3174518, baseEnd_3174518] using wordTrace_append hprefix tailTrace_3174518
  have hstable : (prefixWord ++ tailWord_3174518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174518).length < 2 ^ (prefixWord ++ tailWord_3174518).sum := by decide
  have hdescent : baseEnd_3174518 < baseStart_3174518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174546 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_3174546 : Nat := 118140960795 + 3174546 * 2 ^ 59
def prefixEnd_3174546 : Nat := 4983230072969 + 3 ^ 40 * 3174546 * 2
def baseEnd_3174546 : Nat := 362237323957342623972341

theorem tailTrace_3174546 : CollatzResearch.WordTrace tailWord_3174546 prefixEnd_3174546 362237323957342623972341 := by
  unfold tailWord_3174546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28946301189292371534401873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77190136504779657425071661 28946301189292371534401873)
  ·
    refine ⟨21709725891969278650801405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28946301189292371534401873 21709725891969278650801405)
    ·
      refine ⟨8141147209488479494050527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21709725891969278650801405 8141147209488479494050527)
      ·
        refine ⟨12211720814232719241075791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8141147209488479494050527 12211720814232719241075791)
        ·
          refine ⟨18317581221349078861613687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12211720814232719241075791 18317581221349078861613687)
          ·
            refine ⟨27476371832023618292420531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317581221349078861613687 27476371832023618292420531)
            ·
              refine ⟨41214557748035427438630797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27476371832023618292420531 41214557748035427438630797)
              ·
                refine ⟨15455459155513285289486549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41214557748035427438630797 15455459155513285289486549)
                ·
                  refine ⟨362237323957342623972341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15455459155513285289486549 362237323957342623972341)
                  ·
                    rfl

theorem cell22_3174546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_3174546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174546 prefixEnd_3174546 := by exact prefixLift 3174546
  have htrace : WordTrace (prefixWord ++ tailWord_3174546) baseStart_3174546 baseEnd_3174546 := by
    simpa [prefixWord, tailWord_3174546, baseEnd_3174546] using wordTrace_append hprefix tailTrace_3174546
  have hstable : (prefixWord ++ tailWord_3174546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174546).length < 2 ^ (prefixWord ++ tailWord_3174546).sum := by decide
  have hdescent : baseEnd_3174546 < baseStart_3174546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174666 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3174666 : Nat := 118140960795 + 3174666 * 2 ^ 59
def prefixEnd_3174666 : Nat := 4983230072969 + 3 ^ 40 * 3174666 * 2
def baseEnd_3174666 : Nat := 1086753050324387558916655

theorem tailTrace_3174666 : CollatzResearch.WordTrace tailWord_3174666 prefixEnd_3174666 1086753050324387558916655 := by
  unfold tailWord_3174666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28947395379183686657993963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77193054344489831087983901 28947395379183686657993963)
  ·
    refine ⟨43421093068775529986990945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28947395379183686657993963 43421093068775529986990945)
    ·
      refine ⟨32565819801581647490243209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43421093068775529986990945 32565819801581647490243209)
      ·
        refine ⟨24424364851186235617682407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32565819801581647490243209 24424364851186235617682407)
        ·
          refine ⟨36636547276779353426523611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24424364851186235617682407 36636547276779353426523611)
          ·
            refine ⟨54954820915169030139785417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36636547276779353426523611 54954820915169030139785417)
            ·
              refine ⟨41216115686376772604839063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54954820915169030139785417 41216115686376772604839063)
              ·
                refine ⟨61824173529565158907258595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41216115686376772604839063 61824173529565158907258595)
                ·
                  refine ⟨92736260294347738360887893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61824173529565158907258595 92736260294347738360887893)
                  ·
                    refine ⟨1086753050324387558916655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92736260294347738360887893 1086753050324387558916655)
                    ·
                      rfl

theorem cell22_3174666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3174666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174666 prefixEnd_3174666 := by exact prefixLift 3174666
  have htrace : WordTrace (prefixWord ++ tailWord_3174666) baseStart_3174666 baseEnd_3174666 := by
    simpa [prefixWord, tailWord_3174666, baseEnd_3174666] using wordTrace_append hprefix tailTrace_3174666
  have hstable : (prefixWord ++ tailWord_3174666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174666).length < 2 ^ (prefixWord ++ tailWord_3174666).sum := by decide
  have hdescent : baseEnd_3174666 < baseStart_3174666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174826 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3174826 : Nat := 118140960795 + 3174826 * 2 ^ 59
def prefixEnd_3174826 : Nat := 4983230072969 + 3 ^ 40 * 3174826 * 2
def baseEnd_3174826 : Nat := 1086807821594200474916165

theorem tailTrace_3174826 : CollatzResearch.WordTrace tailWord_3174826 prefixEnd_3174826 1086807821594200474916165 := by
  unfold tailWord_3174826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28948854299038773489450083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77196944797436729305200221 28948854299038773489450083)
  ·
    refine ⟨43423281448558160234175125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28948854299038773489450083 43423281448558160234175125)
    ·
      refine ⟨2035466317901163760976959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43423281448558160234175125 2035466317901163760976959)
      ·
        refine ⟨3053199476851745641465439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035466317901163760976959 3053199476851745641465439)
        ·
          refine ⟨4579799215277618462198159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053199476851745641465439 4579799215277618462198159)
          ·
            refine ⟨6869698822916427693297239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579799215277618462198159 6869698822916427693297239)
            ·
              refine ⟨10304548234374641539945859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869698822916427693297239 10304548234374641539945859)
              ·
                refine ⟨15456822351561962309918789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10304548234374641539945859 15456822351561962309918789)
                ·
                  refine ⟨2898154190917867933109773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15456822351561962309918789 2898154190917867933109773)
                  ·
                    refine ⟨1086807821594200474916165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898154190917867933109773 1086807821594200474916165)
                    ·
                      rfl

theorem cell22_3174826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3174826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174826 prefixEnd_3174826 := by exact prefixLift 3174826
  have htrace : WordTrace (prefixWord ++ tailWord_3174826) baseStart_3174826 baseEnd_3174826 := by
    simpa [prefixWord, tailWord_3174826, baseEnd_3174826] using wordTrace_append hprefix tailTrace_3174826
  have hstable : (prefixWord ++ tailWord_3174826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174826).length < 2 ^ (prefixWord ++ tailWord_3174826).sum := by decide
  have hdescent : baseEnd_3174826 < baseStart_3174826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174880 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_3174880 : Nat := 118140960795 + 3174880 * 2 ^ 59
def prefixEnd_3174880 : Nat := 4983230072969 + 3 ^ 40 * 3174880 * 2
def baseEnd_3174880 : Nat := 1086826306897762334065999

theorem tailTrace_3174880 : CollatzResearch.WordTrace tailWord_3174880 prefixEnd_3174880 1086826306897762334065999 := by
  unfold tailWord_3174880
  simp only [CollatzResearch.WordTrace]
  refine ⟨57898693368979730590133047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77198257825306307453510729 57898693368979730590133047)
  ·
    refine ⟨86848040053469595885199571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57898693368979730590133047 86848040053469595885199571)
    ·
      refine ⟨130272060080204393827799357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86848040053469595885199571 130272060080204393827799357)
      ·
        refine ⟨48852022530076647685424759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130272060080204393827799357 48852022530076647685424759)
        ·
          refine ⟨73278033795114971528137139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48852022530076647685424759 73278033795114971528137139)
          ·
            refine ⟨109917050692672457292205709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73278033795114971528137139 109917050692672457292205709)
            ·
              refine ⟨41218894009752171484577141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109917050692672457292205709 41218894009752171484577141)
              ·
                refine ⟨3864271313414266076679107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41218894009752171484577141 3864271313414266076679107)
                ·
                  refine ⟨5796406970121399115018661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864271313414266076679107 5796406970121399115018661)
                  ·
                    refine ⟨1086826306897762334065999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796406970121399115018661 1086826306897762334065999)
                    ·
                      rfl

theorem cell22_3174880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_3174880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174880 prefixEnd_3174880 := by exact prefixLift 3174880
  have htrace : WordTrace (prefixWord ++ tailWord_3174880) baseStart_3174880 baseEnd_3174880 := by
    simpa [prefixWord, tailWord_3174880, baseEnd_3174880] using wordTrace_append hprefix tailTrace_3174880
  have hstable : (prefixWord ++ tailWord_3174880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174880).length < 2 ^ (prefixWord ++ tailWord_3174880).sum := by decide
  have hdescent : baseEnd_3174880 < baseStart_3174880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174901 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 5]
def baseStart_3174901 : Nat := 118140960795 + 3174901 * 2 ^ 59
def prefixEnd_3174901 : Nat := 4983230072969 + 3 ^ 40 * 3174901 * 2
def baseEnd_3174901 : Nat := 362277831875641759763645

theorem tailTrace_3174901 : CollatzResearch.WordTrace tailWord_3174901 prefixEnd_3174901 362277831875641759763645 := by
  unfold tailWord_3174901
  simp only [CollatzResearch.WordTrace]
  refine ⟨115798152670883381766780557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77198768447255587844520371 115798152670883381766780557)
  ·
    refine ⟨43424307251581268162542709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115798152670883381766780557 43424307251581268162542709)
    ·
      refine ⟨4071028804835743890238379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43424307251581268162542709 4071028804835743890238379)
      ·
        refine ⟨6106543207253615835357569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071028804835743890238379 6106543207253615835357569)
        ·
          refine ⟨4579907405440211876518177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6106543207253615835357569 4579907405440211876518177)
          ·
            refine ⟨3434930554080158907388633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4579907405440211876518177 3434930554080158907388633)
            ·
              refine ⟨2576197915560119180541475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3434930554080158907388633 2576197915560119180541475)
              ·
                refine ⟨3864296873340178770812213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576197915560119180541475 3864296873340178770812213)
                ·
                  refine ⟨362277831875641759763645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3864296873340178770812213 362277831875641759763645)
                  ·
                    rfl

theorem cell22_3174901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_3174901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174901 prefixEnd_3174901 := by exact prefixLift 3174901
  have htrace : WordTrace (prefixWord ++ tailWord_3174901) baseStart_3174901 baseEnd_3174901 := by
    simpa [prefixWord, tailWord_3174901, baseEnd_3174901] using wordTrace_append hprefix tailTrace_3174901
  have hstable : (prefixWord ++ tailWord_3174901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174901).length < 2 ^ (prefixWord ++ tailWord_3174901).sum := by decide
  have hdescent : baseEnd_3174901 < baseStart_3174901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174914 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3174914 : Nat := 118140960795 + 3174914 * 2 ^ 59
def prefixEnd_3174914 : Nat := 4983230072969 + 3 ^ 40 * 3174914 * 2
def baseEnd_3174914 : Nat := 1086837945792597578715895

theorem tailTrace_3174914 : CollatzResearch.WordTrace tailWord_3174914 prefixEnd_3174914 1086837945792597578715895 := by
  unfold tailWord_3174914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28949656704959071246750949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77199084546557523324669197 28949656704959071246750949)
  ·
    refine ⟨5428060632179825858765803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28949656704959071246750949 5428060632179825858765803)
    ·
      refine ⟨8142090948269738788148705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5428060632179825858765803 8142090948269738788148705)
      ·
        refine ⟨6106568211202304091111529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8142090948269738788148705 6106568211202304091111529)
        ·
          refine ⟨4579926158401728068333647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6106568211202304091111529 4579926158401728068333647)
          ·
            refine ⟨6869889237602592102500471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579926158401728068333647 6869889237602592102500471)
            ·
              refine ⟨10304833856403888153750707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869889237602592102500471 10304833856403888153750707)
              ·
                refine ⟨15457250784605832230626061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10304833856403888153750707 15457250784605832230626061)
                ·
                  refine ⟨5796469044227187086484773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15457250784605832230626061 5796469044227187086484773)
                  ·
                    refine ⟨1086837945792597578715895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796469044227187086484773 1086837945792597578715895)
                    ·
                      rfl

theorem cell22_3174914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3174914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174914 prefixEnd_3174914 := by exact prefixLift 3174914
  have htrace : WordTrace (prefixWord ++ tailWord_3174914) baseStart_3174914 baseEnd_3174914 := by
    simpa [prefixWord, tailWord_3174914, baseEnd_3174914] using wordTrace_append hprefix tailTrace_3174914
  have hstable : (prefixWord ++ tailWord_3174914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174914).length < 2 ^ (prefixWord ++ tailWord_3174914).sum := by decide
  have hdescent : baseEnd_3174914 < baseStart_3174914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174955 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 7, 3]
def baseStart_3174955 : Nat := 118140960795 + 3174955 * 2 ^ 59
def prefixEnd_3174955 : Nat := 4983230072969 + 3 ^ 40 * 3174955 * 2
def baseEnd_3174955 : Nat := 1086851980930487138440769

theorem tailTrace_3174955 : CollatzResearch.WordTrace tailWord_3174955 prefixEnd_3174955 1086851980930487138440769 := by
  unfold tailWord_3174955
  simp only [CollatzResearch.WordTrace]
  refine ⟨115800122212687748989246319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77200081475125165992830879 115800122212687748989246319)
  ·
    refine ⟨173700183319031623483869479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115800122212687748989246319 173700183319031623483869479)
    ·
      refine ⟨260550274978547435225804219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173700183319031623483869479 260550274978547435225804219)
      ·
        refine ⟨390825412467821152838706329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260550274978547435225804219 390825412467821152838706329)
        ·
          refine ⟨293119059350865864629029747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390825412467821152838706329 293119059350865864629029747)
          ·
            refine ⟨439678589026298796943544621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293119059350865864629029747 439678589026298796943544621)
            ·
              refine ⟨164879470884862048853829233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439678589026298796943544621 164879470884862048853829233)
              ·
                refine ⟨123659603163646536640371925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164879470884862048853829233 123659603163646536640371925)
                ·
                  refine ⟨2898271949147965702508717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123659603163646536640371925 2898271949147965702508717)
                  ·
                    refine ⟨1086851980930487138440769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898271949147965702508717 1086851980930487138440769)
                    ·
                      rfl

theorem cell22_3174955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 3].length) (baseStart_3174955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174955 prefixEnd_3174955 := by exact prefixLift 3174955
  have htrace : WordTrace (prefixWord ++ tailWord_3174955) baseStart_3174955 baseEnd_3174955 := by
    simpa [prefixWord, tailWord_3174955, baseEnd_3174955] using wordTrace_append hprefix tailTrace_3174955
  have hstable : (prefixWord ++ tailWord_3174955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174955).length < 2 ^ (prefixWord ++ tailWord_3174955).sum := by decide
  have hdescent : baseEnd_3174955 < baseStart_3174955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174972 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_3174972 : Nat := 118140960795 + 3174972 * 2 ^ 59
def prefixEnd_3174972 : Nat := 4983230072969 + 3 ^ 40 * 3174972 * 2
def baseEnd_3174972 : Nat := 1086857800377904760765717

theorem tailTrace_3174972 : CollatzResearch.WordTrace tailWord_3174972 prefixEnd_3174972 1086857800377904760765717 := by
  unfold tailWord_3174972
  simp only [CollatzResearch.WordTrace]
  refine ⟨57900371126813080446307585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77200494835750773928410113 57900371126813080446307585)
  ·
    refine ⟨43425278345109810334730689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57900371126813080446307585 43425278345109810334730689)
    ·
      refine ⟨32568958758832357751048017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43425278345109810334730689 32568958758832357751048017)
      ·
        refine ⟨24426719069124268313286013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32568958758832357751048017 24426719069124268313286013)
        ·
          refine ⟨9160019650921600617482255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24426719069124268313286013 9160019650921600617482255)
          ·
            refine ⟨13740029476382400926223383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9160019650921600617482255 13740029476382400926223383)
            ·
              refine ⟨20610044214573601389335075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13740029476382400926223383 20610044214573601389335075)
              ·
                refine ⟨30915066321860402084002613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20610044214573601389335075 30915066321860402084002613)
                ·
                  refine ⟨2898287467674412695375245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30915066321860402084002613 2898287467674412695375245)
                  ·
                    refine ⟨1086857800377904760765717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898287467674412695375245 1086857800377904760765717)
                    ·
                      rfl

theorem cell22_3174972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_3174972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3174972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3174972 prefixEnd_3174972 := by exact prefixLift 3174972
  have htrace : WordTrace (prefixWord ++ tailWord_3174972) baseStart_3174972 baseEnd_3174972 := by
    simpa [prefixWord, tailWord_3174972, baseEnd_3174972] using wordTrace_append hprefix tailTrace_3174972
  have hstable : (prefixWord ++ tailWord_3174972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174972).length < 2 ^ (prefixWord ++ tailWord_3174972).sum := by decide
  have hdescent : baseEnd_3174972 < baseStart_3174972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175000 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_3175000 : Nat := 118140960795 + 3175000 * 2 ^ 59
def prefixEnd_3175000 : Nat := 4983230072969 + 3 ^ 40 * 3175000 * 2
def baseEnd_3175000 : Nat := 1086867385350122021065631

theorem tailTrace_3175000 : CollatzResearch.WordTrace tailWord_3175000 prefixEnd_3175000 1086867385350122021065631 := by
  unfold tailWord_3175000
  simp only [CollatzResearch.WordTrace]
  refine ⟨57900881748762360837317227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77201175665016481116422969 57900881748762360837317227)
  ·
    refine ⟨86851322623143541255975841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57900881748762360837317227 86851322623143541255975841)
    ·
      refine ⟨65138491967357655941981881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86851322623143541255975841 65138491967357655941981881)
      ·
        refine ⟨48853868975518241956486411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65138491967357655941981881 48853868975518241956486411)
        ·
          refine ⟨73280803463277362934729617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48853868975518241956486411 73280803463277362934729617)
          ·
            refine ⟨54960602597458022201047213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73280803463277362934729617 54960602597458022201047213)
            ·
              refine ⟨20610225974046758325392705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54960602597458022201047213 20610225974046758325392705)
              ·
                refine ⟨15457669480535068744044529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20610225974046758325392705 15457669480535068744044529)
                ·
                  refine ⟨11593252110401301558033397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15457669480535068744044529 11593252110401301558033397)
                  ·
                    refine ⟨1086867385350122021065631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11593252110401301558033397 1086867385350122021065631)
                    ·
                      rfl

theorem cell22_3175000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_3175000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175000 prefixEnd_3175000 := by exact prefixLift 3175000
  have htrace : WordTrace (prefixWord ++ tailWord_3175000) baseStart_3175000 baseEnd_3175000 := by
    simpa [prefixWord, tailWord_3175000, baseEnd_3175000] using wordTrace_append hprefix tailTrace_3175000
  have hstable : (prefixWord ++ tailWord_3175000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175000).length < 2 ^ (prefixWord ++ tailWord_3175000).sum := by decide
  have hdescent : baseEnd_3175000 < baseStart_3175000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175120 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_3175120 : Nat := 118140960795 + 3175120 * 2 ^ 59
def prefixEnd_3175120 : Nat := 4983230072969 + 3 ^ 40 * 3175120 * 2
def baseEnd_3175120 : Nat := 362302821267493902688421

theorem tailTrace_3175120 : CollatzResearch.WordTrace tailWord_3175120 prefixEnd_3175120 362302821267493902688421 := by
  unfold tailWord_3175120
  simp only [CollatzResearch.WordTrace]
  refine ⟨57903070128544991084501407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77204093504726654779335209 57903070128544991084501407)
  ·
    refine ⟨86854605192817486626752111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57903070128544991084501407 86854605192817486626752111)
    ·
      refine ⟨130281907789226229940128167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86854605192817486626752111 130281907789226229940128167)
      ·
        refine ⟨195422861683839344910192251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130281907789226229940128167 195422861683839344910192251)
        ·
          refine ⟨293134292525759017365288377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195422861683839344910192251 293134292525759017365288377)
          ·
            refine ⟨219850719394319263023966283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293134292525759017365288377 219850719394319263023966283)
            ·
              refine ⟨329776079091478894535949425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219850719394319263023966283 329776079091478894535949425)
              ·
                refine ⟨247332059318609170901962069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329776079091478894535949425 247332059318609170901962069)
                ·
                  refine ⟨362302821267493902688421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 247332059318609170901962069 362302821267493902688421)
                  ·
                    rfl

theorem cell22_3175120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_3175120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175120 prefixEnd_3175120 := by exact prefixLift 3175120
  have htrace : WordTrace (prefixWord ++ tailWord_3175120) baseStart_3175120 baseEnd_3175120 := by
    simpa [prefixWord, tailWord_3175120, baseEnd_3175120] using wordTrace_append hprefix tailTrace_3175120
  have hstable : (prefixWord ++ tailWord_3175120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175120).length < 2 ^ (prefixWord ++ tailWord_3175120).sum := by decide
  have hdescent : baseEnd_3175120 < baseStart_3175120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175158 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_3175158 : Nat := 118140960795 + 3175158 * 2 ^ 59
def prefixEnd_3175158 : Nat := 4983230072969 + 3 ^ 40 * 3175158 * 2
def baseEnd_3175158 : Nat := 1086921471979062275615147

theorem tailTrace_3175158 : CollatzResearch.WordTrace tailWord_3175158 prefixEnd_3175158 1086921471979062275615147 := by
  unfold tailWord_3175158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237970389434519666180383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77205017487301543105924085 7237970389434519666180383)
  ·
    refine ⟨10856955584151779499270575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7237970389434519666180383 10856955584151779499270575)
    ·
      refine ⟨16285433376227669248905863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10856955584151779499270575 16285433376227669248905863)
      ·
        refine ⟨24428150064341503873358795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16285433376227669248905863 24428150064341503873358795)
        ·
          refine ⟨36642225096512255810038193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24428150064341503873358795 36642225096512255810038193)
          ·
            refine ⟨27481668822384191857528645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36642225096512255810038193 27481668822384191857528645)
            ·
              refine ⟨5152812904197035973286621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27481668822384191857528645 5152812904197035973286621)
              ·
                refine ⟨1932304839073888489982483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5152812904197035973286621 1932304839073888489982483)
                ·
                  refine ⟨2898457258610832734973725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932304839073888489982483 2898457258610832734973725)
                  ·
                    refine ⟨1086921471979062275615147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898457258610832734973725 1086921471979062275615147)
                    ·
                      rfl

theorem cell22_3175158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_3175158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175158 prefixEnd_3175158 := by exact prefixLift 3175158
  have htrace : WordTrace (prefixWord ++ tailWord_3175158) baseStart_3175158 baseEnd_3175158 := by
    simpa [prefixWord, tailWord_3175158, baseEnd_3175158] using wordTrace_append hprefix tailTrace_3175158
  have hstable : (prefixWord ++ tailWord_3175158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175158).length < 2 ^ (prefixWord ++ tailWord_3175158).sum := by decide
  have hdescent : baseEnd_3175158 < baseStart_3175158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175212 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_3175212 : Nat := 118140960795 + 3175212 * 2 ^ 59
def prefixEnd_3175212 : Nat := 4983230072969 + 3 ^ 40 * 3175212 * 2
def baseEnd_3175212 : Nat := 1086939957282624134764981

theorem tailTrace_3175212 : CollatzResearch.WordTrace tailWord_3175212 prefixEnd_3175212 1086939957282624134764981 := by
  unfold tailWord_3175212
  simp only [CollatzResearch.WordTrace]
  refine ⟨57904747886378340940675945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77206330515171121254234593 57904747886378340940675945)
  ·
    refine ⟨43428560914783755705506959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57904747886378340940675945 43428560914783755705506959)
    ·
      refine ⟨65142841372175633558260439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43428560914783755705506959 65142841372175633558260439)
      ·
        refine ⟨97714262058263450337390659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65142841372175633558260439 97714262058263450337390659)
        ·
          refine ⟨146571393087395175506085989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97714262058263450337390659 146571393087395175506085989)
          ·
            refine ⟨27482136203886595407391123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146571393087395175506085989 27482136203886595407391123)
            ·
              refine ⟨41223204305829893111086685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27482136203886595407391123 41223204305829893111086685)
              ·
                refine ⟨15458701614686209916657507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41223204305829893111086685 15458701614686209916657507)
                ·
                  refine ⟨23188052422029314874986261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15458701614686209916657507 23188052422029314874986261)
                  ·
                    refine ⟨1086939957282624134764981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23188052422029314874986261 1086939957282624134764981)
                    ·
                      rfl

theorem cell22_3175212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_3175212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175212 prefixEnd_3175212 := by exact prefixLift 3175212
  have htrace : WordTrace (prefixWord ++ tailWord_3175212) baseStart_3175212 baseEnd_3175212 := by
    simpa [prefixWord, tailWord_3175212, baseEnd_3175212] using wordTrace_append hprefix tailTrace_3175212
  have hstable : (prefixWord ++ tailWord_3175212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175212).length < 2 ^ (prefixWord ++ tailWord_3175212).sum := by decide
  have hdescent : baseEnd_3175212 < baseStart_3175212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175233 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 6]
def baseStart_3175233 : Nat := 118140960795 + 3175233 * 2 ^ 59
def prefixEnd_3175233 : Nat := 4983230072969 + 3 ^ 40 * 3175233 * 2
def baseEnd_3175233 : Nat := 362315715337262359996639

theorem tailTrace_3175233 : CollatzResearch.WordTrace tailWord_3175233 prefixEnd_3175233 362315715337262359996639 := by
  unfold tailWord_3175233
  simp only [CollatzResearch.WordTrace]
  refine ⟨115810261705680602467866353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77206841137120401645244235 115810261705680602467866353)
  ·
    refine ⟨86857696279260451850899765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115810261705680602467866353 86857696279260451850899765)
    ·
      refine ⟨8142909026180667361021853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86857696279260451850899765 8142909026180667361021853)
      ·
        refine ⟨3053590884817750260383195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8142909026180667361021853 3053590884817750260383195)
        ·
          refine ⟨4580386327226625390574793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053590884817750260383195 4580386327226625390574793)
          ·
            refine ⟨3435289745419969042931095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4580386327226625390574793 3435289745419969042931095)
            ·
              refine ⟨5152934618129953564396643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435289745419969042931095 5152934618129953564396643)
              ·
                refine ⟨7729401927194930346594965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152934618129953564396643 7729401927194930346594965)
                ·
                  refine ⟨362315715337262359996639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7729401927194930346594965 362315715337262359996639)
                  ·
                    rfl

theorem cell22_3175233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_3175233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175233 prefixEnd_3175233 := by exact prefixLift 3175233
  have htrace : WordTrace (prefixWord ++ tailWord_3175233) baseStart_3175233 baseEnd_3175233 := by
    simpa [prefixWord, tailWord_3175233, baseEnd_3175233] using wordTrace_append hprefix tailTrace_3175233
  have hstable : (prefixWord ++ tailWord_3175233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175233).length < 2 ^ (prefixWord ++ tailWord_3175233).sum := by decide
  have hdescent : baseEnd_3175233 < baseStart_3175233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175242 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3175242 : Nat := 118140960795 + 3175242 * 2 ^ 59
def prefixEnd_3175242 : Nat := 4983230072969 + 3 ^ 40 * 3175242 * 2
def baseEnd_3175242 : Nat := 1086950226895714056514889

theorem tailTrace_3175242 : CollatzResearch.WordTrace tailWord_3175242 prefixEnd_3175242 1086950226895714056514889 := by
  unfold tailWord_3175242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28952647490661999251235995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77207059975098664669962653 28952647490661999251235995)
  ·
    refine ⟨43428971235992998876853993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28952647490661999251235995 43428971235992998876853993)
    ·
      refine ⟨32571728426994749157640495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43428971235992998876853993 32571728426994749157640495)
      ·
        refine ⟨48857592640492123736460743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32571728426994749157640495 48857592640492123736460743)
        ·
          refine ⟨73286388960738185604691115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48857592640492123736460743 73286388960738185604691115)
          ·
            refine ⟨109929583441107278407036673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73286388960738185604691115 109929583441107278407036673)
            ·
              refine ⟨82447187580830458805277505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109929583441107278407036673 82447187580830458805277505)
              ·
                refine ⟨61835390685622844103958129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82447187580830458805277505 61835390685622844103958129)
                ·
                  refine ⟨46376543014217133077968597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61835390685622844103958129 46376543014217133077968597)
                  ·
                    refine ⟨1086950226895714056514889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46376543014217133077968597 1086950226895714056514889)
                    ·
                      rfl

theorem cell22_3175242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3175242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175242 prefixEnd_3175242 := by exact prefixLift 3175242
  have htrace : WordTrace (prefixWord ++ tailWord_3175242) baseStart_3175242 baseEnd_3175242 := by
    simpa [prefixWord, tailWord_3175242, baseEnd_3175242] using wordTrace_append hprefix tailTrace_3175242
  have hstable : (prefixWord ++ tailWord_3175242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175242).length < 2 ^ (prefixWord ++ tailWord_3175242).sum := by decide
  have hdescent : baseEnd_3175242 < baseStart_3175242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175244 : List Nat := [2, 2, 1, 3, 3, 2, 2, 7]
def baseStart_3175244 : Nat := 118140960795 + 3175244 * 2 ^ 59
def prefixEnd_3175244 : Nat := 4983230072969 + 3 ^ 40 * 3175244 * 2
def baseEnd_3175244 : Nat := 120772323504065190884987

theorem tailTrace_3175244 : CollatzResearch.WordTrace tailWord_3175244 prefixEnd_3175244 120772323504065190884987 := by
  unfold tailWord_3175244
  simp only [CollatzResearch.WordTrace]
  refine ⟨57905331454320375673258393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77207108605760500897677857 57905331454320375673258393)
  ·
    refine ⟨43428998590740281754943795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57905331454320375673258393 43428998590740281754943795)
    ·
      refine ⟨65143497886110422632415693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43428998590740281754943795 65143497886110422632415693)
      ·
        refine ⟨24428811707291408487155885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65143497886110422632415693 24428811707291408487155885)
        ·
          refine ⟨9160804390234278182683457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24428811707291408487155885 9160804390234278182683457)
          ·
            refine ⟨6870603292675708637012593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9160804390234278182683457 6870603292675708637012593)
            ·
              refine ⟨5152952469506781477759445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6870603292675708637012593 5152952469506781477759445)
              ·
                refine ⟨120772323504065190884987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5152952469506781477759445 120772323504065190884987)
                ·
                  rfl

theorem cell22_3175244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_3175244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175244 prefixEnd_3175244 := by exact prefixLift 3175244
  have htrace : WordTrace (prefixWord ++ tailWord_3175244) baseStart_3175244 baseEnd_3175244 := by
    simpa [prefixWord, tailWord_3175244, baseEnd_3175244] using wordTrace_append hprefix tailTrace_3175244
  have hstable : (prefixWord ++ tailWord_3175244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175244).length < 2 ^ (prefixWord ++ tailWord_3175244).sum := by decide
  have hdescent : baseEnd_3175244 < baseStart_3175244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175287 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3175287 : Nat := 118140960795 + 3175287 * 2 ^ 59
def prefixEnd_3175287 : Nat := 4983230072969 + 3 ^ 40 * 3175287 * 2
def baseEnd_3175287 : Nat := 1086965631315348939139751

theorem tailTrace_3175287 : CollatzResearch.WordTrace tailWord_3175287 prefixEnd_3175287 1086965631315348939139751 := by
  unfold tailWord_3175287
  simp only [CollatzResearch.WordTrace]
  refine ⟨115812231247484969690332115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77208154164989979793554743 115812231247484969690332115)
  ·
    refine ⟨173718346871227454535498173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115812231247484969690332115 173718346871227454535498173)
    ·
      refine ⟨65144380076710295450811815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173718346871227454535498173 65144380076710295450811815)
      ·
        refine ⟨97716570115065443176217723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65144380076710295450811815 97716570115065443176217723)
        ·
          refine ⟨146574855172598164764326585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97716570115065443176217723 146574855172598164764326585)
          ·
            refine ⟨109931141379448623573244939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146574855172598164764326585 109931141379448623573244939)
            ·
              refine ⟨164896712069172935359867409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109931141379448623573244939 164896712069172935359867409)
              ·
                refine ⟨123672534051879701519900557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164896712069172935359867409 123672534051879701519900557)
                ·
                  refine ⟨46377200269454888069962709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123672534051879701519900557 46377200269454888069962709)
                  ·
                    refine ⟨1086965631315348939139751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46377200269454888069962709 1086965631315348939139751)
                    ·
                      rfl

theorem cell22_3175287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3175287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175287 prefixEnd_3175287 := by exact prefixLift 3175287
  have htrace : WordTrace (prefixWord ++ tailWord_3175287) baseStart_3175287 baseEnd_3175287 := by
    simpa [prefixWord, tailWord_3175287, baseEnd_3175287] using wordTrace_append hprefix tailTrace_3175287
  have hstable : (prefixWord ++ tailWord_3175287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175287).length < 2 ^ (prefixWord ++ tailWord_3175287).sum := by decide
  have hdescent : baseEnd_3175287 < baseStart_3175287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175289 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 5]
def baseStart_3175289 : Nat := 118140960795 + 3175289 * 2 ^ 59
def prefixEnd_3175289 : Nat := 4983230072969 + 3 ^ 40 * 3175289 * 2
def baseEnd_3175289 : Nat := 362322105318740533529915

theorem tailTrace_3175289 : CollatzResearch.WordTrace tailWord_3175289 prefixEnd_3175289 362322105318740533529915 := by
  unfold tailWord_3175289
  simp only [CollatzResearch.WordTrace]
  refine ⟨115812304193477724031904921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77208202795651816021269947 115812304193477724031904921)
  ·
    refine ⟨86859228145108293023928691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115812304193477724031904921 86859228145108293023928691)
    ·
      refine ⟨130288842217662439535893037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86859228145108293023928691 130288842217662439535893037)
      ·
        refine ⟨48858315831623414825959889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130288842217662439535893037 48858315831623414825959889)
        ·
          refine ⟨36643736873717561119469917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48858315831623414825959889 36643736873717561119469917)
          ·
            refine ⟨13741401327644085419801219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36643736873717561119469917 13741401327644085419801219)
            ·
              refine ⟨20612101991466128129701829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13741401327644085419801219 20612101991466128129701829)
              ·
                refine ⟨3864769123399899024319093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20612101991466128129701829 3864769123399899024319093)
                ·
                  refine ⟨362322105318740533529915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3864769123399899024319093 362322105318740533529915)
                  ·
                    rfl

theorem cell22_3175289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_3175289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175289 prefixEnd_3175289 := by exact prefixLift 3175289
  have htrace : WordTrace (prefixWord ++ tailWord_3175289) baseStart_3175289 baseEnd_3175289 := by
    simpa [prefixWord, tailWord_3175289, baseEnd_3175289] using wordTrace_append hprefix tailTrace_3175289
  have hstable : (prefixWord ++ tailWord_3175289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175289).length < 2 ^ (prefixWord ++ tailWord_3175289).sum := by decide
  have hdescent : baseEnd_3175289 < baseStart_3175289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175304 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3175304 : Nat := 118140960795 + 3175304 * 2 ^ 59
def prefixEnd_3175304 : Nat := 4983230072969 + 3 ^ 40 * 3175304 * 2
def baseEnd_3175304 : Nat := 1086971450762766561464699

theorem tailTrace_3175304 : CollatzResearch.WordTrace tailWord_3175304 prefixEnd_3175304 1086971450762766561464699 := by
  unfold tailWord_3175304
  simp only [CollatzResearch.WordTrace]
  refine ⟨57906425644211690796850483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77208567525615587729133977 57906425644211690796850483)
  ·
    refine ⟨86859638466317536195275725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57906425644211690796850483 86859638466317536195275725)
    ·
      refine ⟨32572364424869076073228397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86859638466317536195275725 32572364424869076073228397)
      ·
        refine ⟨12214636659325903527460649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32572364424869076073228397 12214636659325903527460649)
        ·
          refine ⟨9160977494494427645595487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12214636659325903527460649 9160977494494427645595487)
          ·
            refine ⟨13741466241741641468393231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9160977494494427645595487 13741466241741641468393231)
            ·
              refine ⟨20612199362612462202589847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13741466241741641468393231 20612199362612462202589847)
              ·
                refine ⟨30918299043918693303884771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20612199362612462202589847 30918299043918693303884771)
                ·
                  refine ⟨46377448565878039955827157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30918299043918693303884771 46377448565878039955827157)
                  ·
                    refine ⟨1086971450762766561464699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46377448565878039955827157 1086971450762766561464699)
                    ·
                      rfl

theorem cell22_3175304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3175304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175304 prefixEnd_3175304 := by exact prefixLift 3175304
  have htrace : WordTrace (prefixWord ++ tailWord_3175304) baseStart_3175304 baseEnd_3175304 := by
    simpa [prefixWord, tailWord_3175304, baseEnd_3175304] using wordTrace_append hprefix tailTrace_3175304
  have hstable : (prefixWord ++ tailWord_3175304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175304).length < 2 ^ (prefixWord ++ tailWord_3175304).sum := by decide
  have hdescent : baseEnd_3175304 < baseStart_3175304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175306 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_3175306 : Nat := 118140960795 + 3175306 * 2 ^ 59
def prefixEnd_3175306 : Nat := 4983230072969 + 3 ^ 40 * 3175306 * 2
def baseEnd_3175306 : Nat := 362324045134546407638231

theorem tailTrace_3175306 : CollatzResearch.WordTrace tailWord_3175306 prefixEnd_3175306 362324045134546407638231 := by
  unfold tailWord_3175306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28953231058604033983818443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77208616156277423956849181 28953231058604033983818443)
  ·
    refine ⟨43429846587906050975727665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28953231058604033983818443 43429846587906050975727665)
    ·
      refine ⟨32572384940929538231795749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43429846587906050975727665 32572384940929538231795749)
      ·
        refine ⟨6107322176424288418461703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32572384940929538231795749 6107322176424288418461703)
        ·
          refine ⟨9160983264636432627692555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107322176424288418461703 9160983264636432627692555)
          ·
            refine ⟨13741474896954648941538833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9160983264636432627692555 13741474896954648941538833)
            ·
              refine ⟨10306106172715986706154125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13741474896954648941538833 10306106172715986706154125)
              ·
                refine ⟨3864789814768495014807797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10306106172715986706154125 3864789814768495014807797)
                ·
                  refine ⟨362324045134546407638231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3864789814768495014807797 362324045134546407638231)
                  ·
                    rfl

theorem cell22_3175306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_3175306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175306 prefixEnd_3175306 := by exact prefixLift 3175306
  have htrace : WordTrace (prefixWord ++ tailWord_3175306) baseStart_3175306 baseEnd_3175306 := by
    simpa [prefixWord, tailWord_3175306, baseEnd_3175306] using wordTrace_append hprefix tailTrace_3175306
  have hstable : (prefixWord ++ tailWord_3175306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175306).length < 2 ^ (prefixWord ++ tailWord_3175306).sum := by decide
  have hdescent : baseEnd_3175306 < baseStart_3175306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175319 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 3, 4]
def baseStart_3175319 : Nat := 118140960795 + 3175319 * 2 ^ 59
def prefixEnd_3175319 : Nat := 4983230072969 + 3 ^ 40 * 3175319 * 2
def baseEnd_3175319 : Nat := 1086976585569311522339653

theorem tailTrace_3175319 : CollatzResearch.WordTrace tailWord_3175319 prefixEnd_3175319 1086976585569311522339653 := by
  unfold tailWord_3175319
  simp only [CollatzResearch.WordTrace]
  refine ⟨115813398383369039155497011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77208932255579359436998007 115813398383369039155497011)
  ·
    refine ⟨173720097575053558733245517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115813398383369039155497011 173720097575053558733245517)
    ·
      refine ⟨65145036590645084524967069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173720097575053558733245517 65145036590645084524967069)
      ·
        refine ⟨24429388721491906696862651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65145036590645084524967069 24429388721491906696862651)
        ·
          refine ⟨36644083082237860045293977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24429388721491906696862651 36644083082237860045293977)
          ·
            refine ⟨27483062311678395033970483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36644083082237860045293977 27483062311678395033970483)
            ·
              refine ⟨41224593467517592550955725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27483062311678395033970483 41224593467517592550955725)
              ·
                refine ⟨15459222550319097206608397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41224593467517592550955725 15459222550319097206608397)
                ·
                  refine ⟨5797208456369661452478149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15459222550319097206608397 5797208456369661452478149)
                  ·
                    refine ⟨1086976585569311522339653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797208456369661452478149 1086976585569311522339653)
                    ·
                      rfl

theorem cell22_3175319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_3175319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175319 prefixEnd_3175319 := by exact prefixLift 3175319
  have htrace : WordTrace (prefixWord ++ tailWord_3175319) baseStart_3175319 baseEnd_3175319 := by
    simpa [prefixWord, tailWord_3175319, baseEnd_3175319] using wordTrace_append hprefix tailTrace_3175319
  have hstable : (prefixWord ++ tailWord_3175319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175319).length < 2 ^ (prefixWord ++ tailWord_3175319).sum := by decide
  have hdescent : baseEnd_3175319 < baseStart_3175319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175351 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 4]
def baseStart_3175351 : Nat := 118140960795 + 3175351 * 2 ^ 59
def prefixEnd_3175351 : Nat := 4983230072969 + 3 ^ 40 * 3175351 * 2
def baseEnd_3175351 : Nat := 362329179941091368513185

theorem tailTrace_3175351 : CollatzResearch.WordTrace tailWord_3175351 prefixEnd_3175351 362329179941091368513185 := by
  unfold tailWord_3175351
  simp only [CollatzResearch.WordTrace]
  refine ⟨115814565519253108620661907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77209710346168739080441271 115814565519253108620661907)
  ·
    refine ⟨173721848278879662930992861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115814565519253108620661907 173721848278879662930992861)
    ·
      refine ⟨65145693104579873599122323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173721848278879662930992861 65145693104579873599122323)
      ·
        refine ⟨97718539656869810398683485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65145693104579873599122323 97718539656869810398683485)
        ·
          refine ⟨36644452371326178899506307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97718539656869810398683485 36644452371326178899506307)
          ·
            refine ⟨54966678556989268349259461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36644452371326178899506307 54966678556989268349259461)
            ·
              refine ⟨10306252229435487815486149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54966678556989268349259461 10306252229435487815486149)
              ·
                refine ⟨1932422293019153965403653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10306252229435487815486149 1932422293019153965403653)
                ·
                  refine ⟨362329179941091368513185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932422293019153965403653 362329179941091368513185)
                  ·
                    rfl

theorem cell22_3175351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 4].length) (baseStart_3175351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175351 prefixEnd_3175351 := by exact prefixLift 3175351
  have htrace : WordTrace (prefixWord ++ tailWord_3175351) baseStart_3175351 baseEnd_3175351 := by
    simpa [prefixWord, tailWord_3175351, baseEnd_3175351] using wordTrace_append hprefix tailTrace_3175351
  have hstable : (prefixWord ++ tailWord_3175351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175351).length < 2 ^ (prefixWord ++ tailWord_3175351).sum := by decide
  have hdescent : baseEnd_3175351 < baseStart_3175351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175458 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3175458 : Nat := 118140960795 + 3175458 * 2 ^ 59
def prefixEnd_3175458 : Nat := 4983230072969 + 3 ^ 40 * 3175458 * 2
def baseEnd_3175458 : Nat := 362341389369987164371409

theorem tailTrace_3175458 : CollatzResearch.WordTrace tailWord_3175458 prefixEnd_3175458 362341389369987164371409 := by
  unfold tailWord_3175458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954617032466366473701757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77212312086576977263204685 28954617032466366473701757)
  ·
    refine ⟨10857981387174887427638159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28954617032466366473701757 10857981387174887427638159)
    ·
      refine ⟨16286972080762331141457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10857981387174887427638159 16286972080762331141457239)
      ·
        refine ⟨24430458121143496712185859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16286972080762331141457239 24430458121143496712185859)
        ·
          refine ⟨36645687181715245068278789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24430458121143496712185859 36645687181715245068278789)
          ·
            refine ⟨6871066346571608450302273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36645687181715245068278789 6871066346571608450302273)
            ·
              refine ⟨5153299759928706337726705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6871066346571608450302273 5153299759928706337726705)
              ·
                refine ⟨3864974819946529753295029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5153299759928706337726705 3864974819946529753295029)
                ·
                  refine ⟨362341389369987164371409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3864974819946529753295029 362341389369987164371409)
                  ·
                    rfl

theorem cell22_3175458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3175458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175458 prefixEnd_3175458 := by exact prefixLift 3175458
  have htrace : WordTrace (prefixWord ++ tailWord_3175458) baseStart_3175458 baseEnd_3175458 := by
    simpa [prefixWord, tailWord_3175458, baseEnd_3175458] using wordTrace_append hprefix tailTrace_3175458
  have hstable : (prefixWord ++ tailWord_3175458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175458).length < 2 ^ (prefixWord ++ tailWord_3175458).sum := by decide
  have hdescent : baseEnd_3175458 < baseStart_3175458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175535 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 2, 3]
def baseStart_3175535 : Nat := 118140960795 + 3175535 * 2 ^ 59
def prefixEnd_3175535 : Nat := 4983230072969 + 3 ^ 40 * 3175535 * 2
def baseEnd_3175535 : Nat := 1087050526783558958938991

theorem tailTrace_3175535 : CollatzResearch.WordTrace tailWord_3175535 prefixEnd_3175535 1087050526783558958938991 := by
  unfold tailWord_3175535
  simp only [CollatzResearch.WordTrace]
  refine ⟨115821276550586508045360059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77214184367057672030240039 115821276550586508045360059)
  ·
    refine ⟨173731914825879762068040089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115821276550586508045360059 173731914825879762068040089)
    ·
      refine ⟨130298936119409821551030067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173731914825879762068040089 130298936119409821551030067)
      ·
        refine ⟨195448404179114732326545101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130298936119409821551030067 195448404179114732326545101)
        ·
          refine ⟨73293151567168024622454413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195448404179114732326545101 73293151567168024622454413)
          ·
            refine ⟨27484931837688009233420405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73293151567168024622454413 27484931837688009233420405)
            ·
              refine ⟨2576712359783250865633163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27484931837688009233420405 2576712359783250865633163)
              ·
                refine ⟨3865068539674876298449745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576712359783250865633163 3865068539674876298449745)
                ·
                  refine ⟨2898801404756157223837309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865068539674876298449745 2898801404756157223837309)
                  ·
                    refine ⟨1087050526783558958938991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898801404756157223837309 1087050526783558958938991)
                    ·
                      rfl

theorem cell22_3175535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_3175535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175535 prefixEnd_3175535 := by exact prefixLift 3175535
  have htrace : WordTrace (prefixWord ++ tailWord_3175535) baseStart_3175535 baseEnd_3175535 := by
    simpa [prefixWord, tailWord_3175535, baseEnd_3175535] using wordTrace_append hprefix tailTrace_3175535
  have hstable : (prefixWord ++ tailWord_3175535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175535).length < 2 ^ (prefixWord ++ tailWord_3175535).sum := by decide
  have hdescent : baseEnd_3175535 < baseStart_3175535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175580 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3175580 : Nat := 118140960795 + 3175580 * 2 ^ 59
def prefixEnd_3175580 : Nat := 4983230072969 + 3 ^ 40 * 3175580 * 2
def baseEnd_3175580 : Nat := 1087065931203193841563853

theorem tailTrace_3175580 : CollatzResearch.WordTrace tailWord_3175580 prefixEnd_3175580 1087065931203193841563853 := by
  unfold tailWord_3175580
  simp only [CollatzResearch.WordTrace]
  refine ⟨57911458917711740365374097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77215278556948987153832129 57911458917711740365374097)
  ·
    refine ⟨43433594188283805274030573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57911458917711740365374097 43433594188283805274030573)
    ·
      refine ⟨16287597820606426977761465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43433594188283805274030573 16287597820606426977761465)
      ·
        refine ⟨12215698365454820233321099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16287597820606426977761465 12215698365454820233321099)
        ·
          refine ⟨18323547548182230349981649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12215698365454820233321099 18323547548182230349981649)
          ·
            refine ⟨13742660661136672762486237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18323547548182230349981649 13742660661136672762486237)
            ·
              refine ⟨5153497747926252285932339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13742660661136672762486237 5153497747926252285932339)
              ·
                refine ⟨7730246621889378428898509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153497747926252285932339 7730246621889378428898509)
                ·
                  refine ⟨2898842483208516910836941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7730246621889378428898509 2898842483208516910836941)
                  ·
                    refine ⟨1087065931203193841563853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898842483208516910836941 1087065931203193841563853)
                    ·
                      rfl

theorem cell22_3175580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3175580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175580 prefixEnd_3175580 := by exact prefixLift 3175580
  have htrace : WordTrace (prefixWord ++ tailWord_3175580) baseStart_3175580 baseEnd_3175580 := by
    simpa [prefixWord, tailWord_3175580, baseEnd_3175580] using wordTrace_append hprefix tailTrace_3175580
  have hstable : (prefixWord ++ tailWord_3175580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175580).length < 2 ^ (prefixWord ++ tailWord_3175580).sum := by decide
  have hdescent : baseEnd_3175580 < baseStart_3175580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175586 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3175586 : Nat := 118140960795 + 3175586 * 2 ^ 59
def prefixEnd_3175586 : Nat := 4983230072969 + 3 ^ 40 * 3175586 * 2
def baseEnd_3175586 : Nat := 1087067985125811825913835

theorem tailTrace_3175586 : CollatzResearch.WordTrace tailWord_3175586 prefixEnd_3175586 1087067985125811825913835 := by
  unfold tailWord_3175586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28955784168350435938866653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77215424448934495836977741 28955784168350435938866653)
  ·
    refine ⟨10858419063131413477074995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28955784168350435938866653 10858419063131413477074995)
    ·
      refine ⟨16287628594697120215612493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10858419063131413477074995 16287628594697120215612493)
      ·
        refine ⟨6107860723011420080854685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16287628594697120215612493 6107860723011420080854685)
        ·
          refine ⟨2290447771129282530320507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6107860723011420080854685 2290447771129282530320507)
          ·
            refine ⟨3435671656693923795480761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290447771129282530320507 3435671656693923795480761)
            ·
              refine ⟨2576753742520442846610571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3435671656693923795480761 2576753742520442846610571)
              ·
                refine ⟨3865130613780664269915857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576753742520442846610571 3865130613780664269915857)
                ·
                  refine ⟨2898847960335498202436893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865130613780664269915857 2898847960335498202436893)
                  ·
                    refine ⟨1087067985125811825913835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898847960335498202436893 1087067985125811825913835)
                    ·
                      rfl

theorem cell22_3175586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3175586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175586 prefixEnd_3175586 := by exact prefixLift 3175586
  have htrace : WordTrace (prefixWord ++ tailWord_3175586) baseStart_3175586 baseEnd_3175586 := by
    simpa [prefixWord, tailWord_3175586, baseEnd_3175586] using wordTrace_append hprefix tailTrace_3175586
  have hstable : (prefixWord ++ tailWord_3175586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175586).length < 2 ^ (prefixWord ++ tailWord_3175586).sum := by decide
  have hdescent : baseEnd_3175586 < baseStart_3175586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175623 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3175623 : Nat := 118140960795 + 3175623 * 2 ^ 59
def prefixEnd_3175623 : Nat := 4983230072969 + 3 ^ 40 * 3175623 * 2
def baseEnd_3175623 : Nat := 1087080650981956062738721

theorem tailTrace_3175623 : CollatzResearch.WordTrace tailWord_3175623 prefixEnd_3175623 1087080650981956062738721 := by
  unfold tailWord_3175623
  simp only [CollatzResearch.WordTrace]
  refine ⟨115824486174267699074563523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77216324116178466049709015 115824486174267699074563523)
  ·
    refine ⟨173736729261401548611845285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115824486174267699074563523 173736729261401548611845285)
    ·
      refine ⟨32575636736512790364720991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173736729261401548611845285 32575636736512790364720991)
      ·
        refine ⟨48863455104769185547081487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32575636736512790364720991 48863455104769185547081487)
        ·
          refine ⟨73295182657153778320622231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48863455104769185547081487 73295182657153778320622231)
          ·
            refine ⟨109942773985730667480933347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73295182657153778320622231 109942773985730667480933347)
            ·
              refine ⟨164914160978596001221400021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109942773985730667480933347 164914160978596001221400021)
              ·
                refine ⟨3865175647935843778626563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 164914160978596001221400021 3865175647935843778626563)
                ·
                  refine ⟨5797763471903765667939845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865175647935843778626563 5797763471903765667939845)
                  ·
                    refine ⟨1087080650981956062738721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797763471903765667939845 1087080650981956062738721)
                    ·
                      rfl

theorem cell22_3175623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3175623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175623 prefixEnd_3175623 := by exact prefixLift 3175623
  have htrace : WordTrace (prefixWord ++ tailWord_3175623) baseStart_3175623 baseEnd_3175623 := by
    simpa [prefixWord, tailWord_3175623, baseEnd_3175623] using wordTrace_append hprefix tailTrace_3175623
  have hstable : (prefixWord ++ tailWord_3175623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175623).length < 2 ^ (prefixWord ++ tailWord_3175623).sum := by decide
  have hdescent : baseEnd_3175623 < baseStart_3175623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175655 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 6]
def baseStart_3175655 : Nat := 118140960795 + 3175655 * 2 ^ 59
def prefixEnd_3175655 : Nat := 4983230072969 + 3 ^ 40 * 3175655 * 2
def baseEnd_3175655 : Nat := 362363868411972881979541

theorem tailTrace_3175655 : CollatzResearch.WordTrace tailWord_3175655 prefixEnd_3175655 362363868411972881979541 := by
  unfold tailWord_3175655
  simp only [CollatzResearch.WordTrace]
  refine ⟨115825653310151768539728419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77217102206767845693152279 115825653310151768539728419)
  ·
    refine ⟨173738479965227652809592629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115825653310151768539728419 173738479965227652809592629)
    ·
      refine ⟨16287982496740092450899309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173738479965227652809592629 16287982496740092450899309)
      ·
        refine ⟨6107993436277534669087241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16287982496740092450899309 6107993436277534669087241)
        ·
          refine ⟨4580995077208151001815431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6107993436277534669087241 4580995077208151001815431)
          ·
            refine ⟨6871492615812226502723147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580995077208151001815431 6871492615812226502723147)
            ·
              refine ⟨10307238923718339754084721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6871492615812226502723147 10307238923718339754084721)
              ·
                refine ⟨7730429192788754815563541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10307238923718339754084721 7730429192788754815563541)
                ·
                  refine ⟨362363868411972881979541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7730429192788754815563541 362363868411972881979541)
                  ·
                    rfl

theorem cell22_3175655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 6].length) (baseStart_3175655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175655 prefixEnd_3175655 := by exact prefixLift 3175655
  have htrace : WordTrace (prefixWord ++ tailWord_3175655) baseStart_3175655 baseEnd_3175655 := by
    simpa [prefixWord, tailWord_3175655, baseEnd_3175655] using wordTrace_append hprefix tailTrace_3175655
  have hstable : (prefixWord ++ tailWord_3175655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175655).length < 2 ^ (prefixWord ++ tailWord_3175655).sum := by decide
  have hdescent : baseEnd_3175655 < baseStart_3175655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175670 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3175670 : Nat := 118140960795 + 3175670 * 2 ^ 59
def prefixEnd_3175670 : Nat := 4983230072969 + 3 ^ 40 * 3175670 * 2
def baseEnd_3175670 : Nat := 1087096740042463606813577

theorem tailTrace_3175670 : CollatzResearch.WordTrace tailWord_3175670 prefixEnd_3175670 1087096740042463606813577 := by
  unfold tailWord_3175670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239137525318589131345279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77217466936731617401016309 7239137525318589131345279)
  ·
    refine ⟨10858706287977883697017919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239137525318589131345279 10858706287977883697017919)
    ·
      refine ⟨16288059431966825545526879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10858706287977883697017919 16288059431966825545526879)
      ·
        refine ⟨24432089147950238318290319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16288059431966825545526879 24432089147950238318290319)
        ·
          refine ⟨36648133721925357477435479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24432089147950238318290319 36648133721925357477435479)
          ·
            refine ⟨54972200582888036216153219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36648133721925357477435479 54972200582888036216153219)
            ·
              refine ⟨82458300874332054324229829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54972200582888036216153219 82458300874332054324229829)
              ·
                refine ⟨15460931413937260185793093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82458300874332054324229829 15460931413937260185793093)
                ·
                  refine ⟨2898924640113236284836205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15460931413937260185793093 2898924640113236284836205)
                  ·
                    refine ⟨1087096740042463606813577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898924640113236284836205 1087096740042463606813577)
                    ·
                      rfl

theorem cell22_3175670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3175670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175670 prefixEnd_3175670 := by exact prefixLift 3175670
  have htrace : WordTrace (prefixWord ++ tailWord_3175670) baseStart_3175670 baseEnd_3175670 := by
    simpa [prefixWord, tailWord_3175670, baseEnd_3175670] using wordTrace_append hprefix tailTrace_3175670
  have hstable : (prefixWord ++ tailWord_3175670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175670).length < 2 ^ (prefixWord ++ tailWord_3175670).sum := by decide
  have hdescent : baseEnd_3175670 < baseStart_3175670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175715 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 3, 3]
def baseStart_3175715 : Nat := 118140960795 + 3175715 * 2 ^ 59
def prefixEnd_3175715 : Nat := 4983230072969 + 3 ^ 40 * 3175715 * 2
def baseEnd_3175715 : Nat := 1087112144462098489438439

theorem tailTrace_3175715 : CollatzResearch.WordTrace tailWord_3175715 prefixEnd_3175715 1087112144462098489438439 := by
  unfold tailWord_3175715
  simp only [CollatzResearch.WordTrace]
  refine ⟨115827841689934398786912599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77218561126622932524608399 115827841689934398786912599)
  ·
    refine ⟨173741762534901598180368899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115827841689934398786912599 173741762534901598180368899)
    ·
      refine ⟨260612643802352397270553349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173741762534901598180368899 260612643802352397270553349)
      ·
        refine ⟨48864870712941074488228753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260612643802352397270553349 48864870712941074488228753)
        ·
          refine ⟨36648653034705805866171565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48864870712941074488228753 36648653034705805866171565)
          ·
            refine ⟨13743244888014677199814337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36648653034705805866171565 13743244888014677199814337)
            ·
              refine ⟨10307433666011007899860753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13743244888014677199814337 10307433666011007899860753)
              ·
                refine ⟨7730575249508255924895565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10307433666011007899860753 7730575249508255924895565)
                ·
                  refine ⟨2898965718565595971835837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7730575249508255924895565 2898965718565595971835837)
                  ·
                    refine ⟨1087112144462098489438439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898965718565595971835837 1087112144462098489438439)
                    ·
                      rfl

theorem cell22_3175715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 3].length) (baseStart_3175715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175715 prefixEnd_3175715 := by exact prefixLift 3175715
  have htrace : WordTrace (prefixWord ++ tailWord_3175715) baseStart_3175715 baseEnd_3175715 := by
    simpa [prefixWord, tailWord_3175715, baseEnd_3175715] using wordTrace_append hprefix tailTrace_3175715
  have hstable : (prefixWord ++ tailWord_3175715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175715).length < 2 ^ (prefixWord ++ tailWord_3175715).sum := by decide
  have hdescent : baseEnd_3175715 < baseStart_3175715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175734 : List Nat := [5, 1, 2, 3, 2, 1, 8]
def baseStart_3175734 : Nat := 118140960795 + 3175734 * 2 ^ 59
def prefixEnd_3175734 : Nat := 4983230072969 + 3 ^ 40 * 3175734 * 2
def baseEnd_3175734 : Nat := 40263653650014399007903

theorem tailTrace_3175734 : CollatzResearch.WordTrace tailWord_3175734 prefixEnd_3175734 40263653650014399007903 := by
  unfold tailWord_3175734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239283417304097814490891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77219023117910376687902837 7239283417304097814490891)
  ·
    refine ⟨10858925125956146721736337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239283417304097814490891 10858925125956146721736337)
    ·
      refine ⟨8144193844467110041302253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10858925125956146721736337 8144193844467110041302253)
      ·
        refine ⟨3054072691675166265488345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8144193844467110041302253 3054072691675166265488345)
        ·
          refine ⟨2290554518756374699116259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054072691675166265488345 2290554518756374699116259)
          ·
            refine ⟨3435831778134562048674389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290554518756374699116259 3435831778134562048674389)
            ·
              refine ⟨40263653650014399007903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3435831778134562048674389 40263653650014399007903)
              ·
                rfl

theorem cell22_3175734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 8].length) (baseStart_3175734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175734 prefixEnd_3175734 := by exact prefixLift 3175734
  have htrace : WordTrace (prefixWord ++ tailWord_3175734) baseStart_3175734 baseEnd_3175734 := by
    simpa [prefixWord, tailWord_3175734, baseEnd_3175734] using wordTrace_append hprefix tailTrace_3175734
  have hstable : (prefixWord ++ tailWord_3175734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175734).length < 2 ^ (prefixWord ++ tailWord_3175734).sum := by decide
  have hdescent : baseEnd_3175734 < baseStart_3175734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175745 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 7]
def baseStart_3175745 : Nat := 118140960795 + 3175745 * 2 ^ 59
def prefixEnd_3175745 : Nat := 4983230072969 + 3 ^ 40 * 3175745 * 2
def baseEnd_3175745 : Nat := 362374138025062803729449

theorem tailTrace_3175745 : CollatzResearch.WordTrace tailWord_3175745 prefixEnd_3175745 362374138025062803729449 := by
  unfold tailWord_3175745
  simp only [CollatzResearch.WordTrace]
  refine ⟨115828935879825713910504689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77219290586550475940336459 115828935879825713910504689)
  ·
    refine ⟨86871701909869285432878517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115828935879825713910504689 86871701909869285432878517)
    ·
      refine ⟨8144222054050245509332361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86871701909869285432878517 8144222054050245509332361)
      ·
        refine ⟨6108166540537684131999271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8144222054050245509332361 6108166540537684131999271)
        ·
          refine ⟨9162249810806526197998907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108166540537684131999271 9162249810806526197998907)
          ·
            refine ⟨13743374716209789296998361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162249810806526197998907 13743374716209789296998361)
            ·
              refine ⟨10307531037157341972748771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13743374716209789296998361 10307531037157341972748771)
              ·
                refine ⟨15461296555736012959123157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307531037157341972748771 15461296555736012959123157)
                ·
                  refine ⟨362374138025062803729449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15461296555736012959123157 362374138025062803729449)
                  ·
                    rfl

theorem cell22_3175745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_3175745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175745 prefixEnd_3175745 := by exact prefixLift 3175745
  have htrace : WordTrace (prefixWord ++ tailWord_3175745) baseStart_3175745 baseEnd_3175745 := by
    simpa [prefixWord, tailWord_3175745, baseEnd_3175745] using wordTrace_append hprefix tailTrace_3175745
  have hstable : (prefixWord ++ tailWord_3175745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175745).length < 2 ^ (prefixWord ++ tailWord_3175745).sum := by decide
  have hdescent : baseEnd_3175745 < baseStart_3175745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175792 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 1, 4]
def baseStart_3175792 : Nat := 118140960795 + 3175792 * 2 ^ 59
def prefixEnd_3175792 : Nat := 4983230072969 + 3 ^ 40 * 3175792 * 2
def baseEnd_3175792 : Nat := 1087138503135695955263203

theorem tailTrace_3175792 : CollatzResearch.WordTrace tailWord_3175792 prefixEnd_3175792 1087138503135695955263203 := by
  unfold tailWord_3175792
  simp only [CollatzResearch.WordTrace]
  refine ⟨57915325055327720468732815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77220433407103627291643753 57915325055327720468732815)
  ·
    refine ⟨86872987582991580703099223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57915325055327720468732815 86872987582991580703099223)
    ·
      refine ⟨130309481374487371054648835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86872987582991580703099223 130309481374487371054648835)
      ·
        refine ⟨195464222061731056581973253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130309481374487371054648835 195464222061731056581973253)
        ·
          refine ⟨36649541636574573109119985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195464222061731056581973253 36649541636574573109119985)
          ·
            refine ⟨27487156227430929831839989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36649541636574573109119985 27487156227430929831839989)
            ·
              refine ⟨2576920896321649671734999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27487156227430929831839989 2576920896321649671734999)
              ·
                refine ⟨3865381344482474507602499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576920896321649671734999 3865381344482474507602499)
                ·
                  refine ⟨5798072016723711761403749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865381344482474507602499 5798072016723711761403749)
                  ·
                    refine ⟨1087138503135695955263203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798072016723711761403749 1087138503135695955263203)
                    ·
                      rfl

theorem cell22_3175792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_3175792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175792 prefixEnd_3175792 := by exact prefixLift 3175792
  have htrace : WordTrace (prefixWord ++ tailWord_3175792) baseStart_3175792 baseEnd_3175792 := by
    simpa [prefixWord, tailWord_3175792, baseEnd_3175792] using wordTrace_append hprefix tailTrace_3175792
  have hstable : (prefixWord ++ tailWord_3175792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175792).length < 2 ^ (prefixWord ++ tailWord_3175792).sum := by decide
  have hdescent : baseEnd_3175792 < baseStart_3175792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175837 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_3175837 : Nat := 118140960795 + 3175837 * 2 ^ 59
def prefixEnd_3175837 : Nat := 4983230072969 + 3 ^ 40 * 3175837 * 2
def baseEnd_3175837 : Nat := 1087153907555330837888065

theorem tailTrace_3175837 : CollatzResearch.WordTrace tailWord_3175837 prefixEnd_3175837 1087153907555330837888065 := by
  unfold tailWord_3175837
  simp only [CollatzResearch.WordTrace]
  refine ⟨115832291395492413622853765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77221527596994942415235843 115832291395492413622853765)
  ·
    refine ⟨21718554636654827554285081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115832291395492413622853765 21718554636654827554285081)
    ·
      refine ⟨16288915977491120665713811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21718554636654827554285081 16288915977491120665713811)
      ·
        refine ⟨24433373966236680998570717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16288915977491120665713811 24433373966236680998570717)
        ·
          refine ⟨9162515237338755374464019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24433373966236680998570717 9162515237338755374464019)
          ·
            refine ⟨13743772856008133061696029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162515237338755374464019 13743772856008133061696029)
            ·
              refine ⟨5153914821003049898136011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13743772856008133061696029 5153914821003049898136011)
              ·
                refine ⟨7730872231504574847204017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153914821003049898136011 7730872231504574847204017)
                ·
                  refine ⟨5798154173628431135403013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7730872231504574847204017 5798154173628431135403013)
                  ·
                    refine ⟨1087153907555330837888065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798154173628431135403013 1087153907555330837888065)
                    ·
                      rfl

theorem cell22_3175837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_3175837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175837 prefixEnd_3175837 := by exact prefixLift 3175837
  have htrace : WordTrace (prefixWord ++ tailWord_3175837) baseStart_3175837 baseEnd_3175837 := by
    simpa [prefixWord, tailWord_3175837, baseEnd_3175837] using wordTrace_append hprefix tailTrace_3175837
  have hstable : (prefixWord ++ tailWord_3175837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175837).length < 2 ^ (prefixWord ++ tailWord_3175837).sum := by decide
  have hdescent : baseEnd_3175837 < baseStart_3175837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175901 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3175901 : Nat := 118140960795 + 3175901 * 2 ^ 59
def prefixEnd_3175901 : Nat := 4983230072969 + 3 ^ 40 * 3175901 * 2
def baseEnd_3175901 : Nat := 1087175816063256004287869

theorem tailTrace_3175901 : CollatzResearch.WordTrace tailWord_3175901 prefixEnd_3175901 1087175816063256004287869 := by
  unfold tailWord_3175901
  simp only [CollatzResearch.WordTrace]
  refine ⟨115834625667260552553183557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77223083778173701702122371 115834625667260552553183557)
  ·
    refine ⟨21718992312611353603721917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115834625667260552553183557 21718992312611353603721917)
    ·
      refine ⟨8144622117229257601395719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21718992312611353603721917 8144622117229257601395719)
      ·
        refine ⟨12216933175843886402093579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8144622117229257601395719 12216933175843886402093579)
        ·
          refine ⟨18325399763765829603140369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12216933175843886402093579 18325399763765829603140369)
          ·
            refine ⟨13744049822824372202355277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18325399763765829603140369 13744049822824372202355277)
            ·
              refine ⟨5154018683559139575883229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13744049822824372202355277 5154018683559139575883229)
              ·
                refine ⟨1932757006334677340956211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5154018683559139575883229 1932757006334677340956211)
                ·
                  refine ⟨2899135509502016011434317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932757006334677340956211 2899135509502016011434317)
                  ·
                    refine ⟨1087175816063256004287869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2899135509502016011434317 1087175816063256004287869)
                    ·
                      rfl

theorem cell22_3175901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3175901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175901 prefixEnd_3175901 := by exact prefixLift 3175901
  have htrace : WordTrace (prefixWord ++ tailWord_3175901) baseStart_3175901 baseEnd_3175901 := by
    simpa [prefixWord, tailWord_3175901, baseEnd_3175901] using wordTrace_append hprefix tailTrace_3175901
  have hstable : (prefixWord ++ tailWord_3175901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175901).length < 2 ^ (prefixWord ++ tailWord_3175901).sum := by decide
  have hdescent : baseEnd_3175901 < baseStart_3175901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175957 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3175957 : Nat := 118140960795 + 3175957 * 2 ^ 59
def prefixEnd_3175957 : Nat := 4983230072969 + 3 ^ 40 * 3175957 * 2
def baseEnd_3175957 : Nat := 1087194986007690524887697

theorem tailTrace_3175957 : CollatzResearch.WordTrace tailWord_3175957 prefixEnd_3175957 1087194986007690524887697 := by
  unfold tailWord_3175957
  simp only [CollatzResearch.WordTrace]
  refine ⟨115836668155057674117222125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77224445436705116078148083 115836668155057674117222125)
  ·
    refine ⟨43438750558146627793958297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115836668155057674117222125 43438750558146627793958297)
    ·
      refine ⟨32579062918609970845468723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43438750558146627793958297 32579062918609970845468723)
      ·
        refine ⟨48868594377914956268203085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32579062918609970845468723 48868594377914956268203085)
        ·
          refine ⟨18325722891718108600576157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48868594377914956268203085 18325722891718108600576157)
          ·
            refine ⟨6872146084394290725216059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18325722891718108600576157 6872146084394290725216059)
            ·
              refine ⟨10308219126591436087824089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6872146084394290725216059 10308219126591436087824089)
              ·
                refine ⟨7731164344943577065868067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10308219126591436087824089 7731164344943577065868067)
                ·
                  refine ⟨11596746517415365598802101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7731164344943577065868067 11596746517415365598802101)
                  ·
                    refine ⟨1087194986007690524887697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11596746517415365598802101 1087194986007690524887697)
                    ·
                      rfl

theorem cell22_3175957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3175957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175957 prefixEnd_3175957 := by exact prefixLift 3175957
  have htrace : WordTrace (prefixWord ++ tailWord_3175957) baseStart_3175957 baseEnd_3175957 := by
    simpa [prefixWord, tailWord_3175957, baseEnd_3175957] using wordTrace_append hprefix tailTrace_3175957
  have hstable : (prefixWord ++ tailWord_3175957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175957).length < 2 ^ (prefixWord ++ tailWord_3175957).sum := by decide
  have hdescent : baseEnd_3175957 < baseStart_3175957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175976 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 4]
def baseStart_3175976 : Nat := 118140960795 + 3175976 * 2 ^ 59
def prefixEnd_3175976 : Nat := 4983230072969 + 3 ^ 40 * 3175976 * 2
def baseEnd_3175976 : Nat := 362400496698660269554213

theorem tailTrace_3175976 : CollatzResearch.WordTrace tailWord_3175976 prefixEnd_3175976 362400496698660269554213 := by
  unfold tailWord_3175976
  simp only [CollatzResearch.WordTrace]
  refine ⟨57918680570994420181081891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77224907427992560241442521 57918680570994420181081891)
  ·
    refine ⟨86878020856491630271622837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57918680570994420181081891 86878020856491630271622837)
    ·
      refine ⟨8144814455296090337964641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86878020856491630271622837 8144814455296090337964641)
      ·
        refine ⟨6108610841472067753473481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8144814455296090337964641 6108610841472067753473481)
        ·
          refine ⟨4581458131104050815105111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6108610841472067753473481 4581458131104050815105111)
          ·
            refine ⟨6872187196656076222657667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581458131104050815105111 6872187196656076222657667)
            ·
              refine ⟨10308280794984114333986501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6872187196656076222657667 10308280794984114333986501)
              ·
                refine ⟨1932802649059521437622469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10308280794984114333986501 1932802649059521437622469)
                ·
                  refine ⟨362400496698660269554213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932802649059521437622469 362400496698660269554213)
                  ·
                    rfl

theorem cell22_3175976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_3175976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175976 prefixEnd_3175976 := by exact prefixLift 3175976
  have htrace : WordTrace (prefixWord ++ tailWord_3175976) baseStart_3175976 baseEnd_3175976 := by
    simpa [prefixWord, tailWord_3175976, baseEnd_3175976] using wordTrace_append hprefix tailTrace_3175976
  have hstable : (prefixWord ++ tailWord_3175976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175976).length < 2 ^ (prefixWord ++ tailWord_3175976).sum := by decide
  have hdescent : baseEnd_3175976 < baseStart_3175976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175985 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3175985 : Nat := 118140960795 + 3175985 * 2 ^ 59
def prefixEnd_3175985 : Nat := 4983230072969 + 3 ^ 40 * 3175985 * 2
def baseEnd_3175985 : Nat := 1087204570979907785187611

theorem tailTrace_3175985 : CollatzResearch.WordTrace tailWord_3175985 prefixEnd_3175985 1087204570979907785187611 := by
  unfold tailWord_3175985
  simp only [CollatzResearch.WordTrace]
  refine ⟨115837689398956234899241409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77225126265970823266160939 115837689398956234899241409)
  ·
    refine ⟨86878267049217176174431057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115837689398956234899241409 86878267049217176174431057)
    ·
      refine ⟨65158700286912882130823293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86878267049217176174431057 65158700286912882130823293)
      ·
        refine ⟨24434512607592330799058735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65158700286912882130823293 24434512607592330799058735)
        ·
          refine ⟨36651768911388496198588103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24434512607592330799058735 36651768911388496198588103)
          ·
            refine ⟨54977653367082744297882155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36651768911388496198588103 54977653367082744297882155)
            ·
              refine ⟨82466480050624116446823233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54977653367082744297882155 82466480050624116446823233)
              ·
                refine ⟨61849860037968087335117425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82466480050624116446823233 61849860037968087335117425)
                ·
                  refine ⟨46387395028476065501338069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61849860037968087335117425 46387395028476065501338069)
                  ·
                    refine ⟨1087204570979907785187611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46387395028476065501338069 1087204570979907785187611)
                    ·
                      rfl

theorem cell22_3175985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3175985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175985 prefixEnd_3175985 := by exact prefixLift 3175985
  have htrace : WordTrace (prefixWord ++ tailWord_3175985) baseStart_3175985 baseEnd_3175985 := by
    simpa [prefixWord, tailWord_3175985, baseEnd_3175985] using wordTrace_append hprefix tailTrace_3175985
  have hstable : (prefixWord ++ tailWord_3175985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175985).length < 2 ^ (prefixWord ++ tailWord_3175985).sum := by decide
  have hdescent : baseEnd_3175985 < baseStart_3175985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175987 : List Nat := [1, 1, 1, 2, 4, 5, 1, 7]
def baseStart_3175987 : Nat := 118140960795 + 3175987 * 2 ^ 59
def prefixEnd_3175987 : Nat := 4983230072969 + 3 ^ 40 * 3175987 * 2
def baseEnd_3175987 : Nat := 120800583957864494070845

theorem tailTrace_3175987 : CollatzResearch.WordTrace tailWord_3175987 prefixEnd_3175987 120800583957864494070845 := by
  unfold tailWord_3175987
  simp only [CollatzResearch.WordTrace]
  refine ⟨115837762344948989240814215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77225174896632659493876143 115837762344948989240814215)
  ·
    refine ⟨173756643517423483861221323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115837762344948989240814215 173756643517423483861221323)
    ·
      refine ⟨260634965276135225791831985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173756643517423483861221323 260634965276135225791831985)
      ·
        refine ⟨195476223957101419343873989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260634965276135225791831985 195476223957101419343873989)
        ·
          refine ⟨36651791991956516126976373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195476223957101419343873989 36651791991956516126976373)
          ·
            refine ⟨3436105499245923386904035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36651791991956516126976373 3436105499245923386904035)
            ·
              refine ⟨5154158248868885080356053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436105499245923386904035 5154158248868885080356053)
              ·
                refine ⟨120800583957864494070845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5154158248868885080356053 120800583957864494070845)
                ·
                  rfl

theorem cell22_3175987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 7].length) (baseStart_3175987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3175987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3175987 prefixEnd_3175987 := by exact prefixLift 3175987
  have htrace : WordTrace (prefixWord ++ tailWord_3175987) baseStart_3175987 baseEnd_3175987 := by
    simpa [prefixWord, tailWord_3175987, baseEnd_3175987] using wordTrace_append hprefix tailTrace_3175987
  have hstable : (prefixWord ++ tailWord_3175987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175987).length < 2 ^ (prefixWord ++ tailWord_3175987).sum := by decide
  have hdescent : baseEnd_3175987 < baseStart_3175987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176000 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_3176000 : Nat := 118140960795 + 3176000 * 2 ^ 59
def prefixEnd_3176000 : Nat := 4983230072969 + 3 ^ 40 * 3176000 * 2
def baseEnd_3176000 : Nat := 1087209705786452746062565

theorem tailTrace_3176000 : CollatzResearch.WordTrace tailWord_3176000 prefixEnd_3176000 1087209705786452746062565 := by
  unfold tailWord_3176000
  simp only [CollatzResearch.WordTrace]
  refine ⟨57919118246950946230518727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77225490995934594974024969 57919118246950946230518727)
  ·
    refine ⟨86878677370426419345778091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57919118246950946230518727 86878677370426419345778091)
    ·
      refine ⟨130318016055639629018667137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86878677370426419345778091 130318016055639629018667137)
      ·
        refine ⟨97738512041729721764000353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130318016055639629018667137 97738512041729721764000353)
        ·
          refine ⟨73303884031297291323000265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97738512041729721764000353 73303884031297291323000265)
          ·
            refine ⟨54977913023472968492250199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73303884031297291323000265 54977913023472968492250199)
            ·
              refine ⟨82466869535209452738375299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54977913023472968492250199 82466869535209452738375299)
              ·
                refine ⟨123700304302814179107562949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82466869535209452738375299 123700304302814179107562949)
                ·
                  refine ⟨23193807056777658582668053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123700304302814179107562949 23193807056777658582668053)
                  ·
                    refine ⟨1087209705786452746062565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23193807056777658582668053 1087209705786452746062565)
                    ·
                      rfl

theorem cell22_3176000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_3176000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176000 prefixEnd_3176000 := by exact prefixLift 3176000
  have htrace : WordTrace (prefixWord ++ tailWord_3176000) baseStart_3176000 baseEnd_3176000 := by
    simpa [prefixWord, tailWord_3176000, baseEnd_3176000] using wordTrace_append hprefix tailTrace_3176000
  have hstable : (prefixWord ++ tailWord_3176000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176000).length < 2 ^ (prefixWord ++ tailWord_3176000).sum := by decide
  have hdescent : baseEnd_3176000 < baseStart_3176000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176006 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3176006 : Nat := 118140960795 + 3176006 * 2 ^ 59
def prefixEnd_3176006 : Nat := 4983230072969 + 3 ^ 40 * 3176006 * 2
def baseEnd_3176006 : Nat := 1087211759709070730412547

theorem tailTrace_3176006 : CollatzResearch.WordTrace tailWord_3176006 prefixEnd_3176006 1087211759709070730412547 := by
  unfold tailWord_3176006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3619951729121254858929871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77225636887920103657170581 3619951729121254858929871)
  ·
    refine ⟨5429927593681882288394807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3619951729121254858929871 5429927593681882288394807)
    ·
      refine ⟨8144891390522823432592211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5429927593681882288394807 8144891390522823432592211)
      ·
        refine ⟨12217337085784235148888317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8144891390522823432592211 12217337085784235148888317)
        ·
          refine ⟨4581501407169088180833119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12217337085784235148888317 4581501407169088180833119)
          ·
            refine ⟨6872252110753632271249679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581501407169088180833119 6872252110753632271249679)
            ·
              refine ⟨10308378166130448406874519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6872252110753632271249679 10308378166130448406874519)
              ·
                refine ⟨15462567249195672610311779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10308378166130448406874519 15462567249195672610311779)
                ·
                  refine ⟨23193850873793508915467669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15462567249195672610311779 23193850873793508915467669)
                  ·
                    refine ⟨1087211759709070730412547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23193850873793508915467669 1087211759709070730412547)
                    ·
                      rfl

theorem cell22_3176006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3176006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176006 prefixEnd_3176006 := by exact prefixLift 3176006
  have htrace : WordTrace (prefixWord ++ tailWord_3176006) baseStart_3176006 baseEnd_3176006 := by
    simpa [prefixWord, tailWord_3176006, baseEnd_3176006] using wordTrace_append hprefix tailTrace_3176006
  have hstable : (prefixWord ++ tailWord_3176006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176006).length < 2 ^ (prefixWord ++ tailWord_3176006).sum := by decide
  have hdescent : baseEnd_3176006 < baseStart_3176006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176015 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 7]
def baseStart_3176015 : Nat := 118140960795 + 3176015 * 2 ^ 59
def prefixEnd_3176015 : Nat := 4983230072969 + 3 ^ 40 * 3176015 * 2
def baseEnd_3176015 : Nat := 362404946864332568979173

theorem tailTrace_3176015 : CollatzResearch.WordTrace tailWord_3176015 prefixEnd_3176015 362404946864332568979173 := by
  unfold tailWord_3176015
  simp only [CollatzResearch.WordTrace]
  refine ⟨115838783588847550022833499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77225855725898366681888999 115838783588847550022833499)
  ·
    refine ⟨173758175383271325034250249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115838783588847550022833499 173758175383271325034250249)
    ·
      refine ⟨130318631537453493775687687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173758175383271325034250249 130318631537453493775687687)
      ·
        refine ⟨195477947306180240663531531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130318631537453493775687687 195477947306180240663531531)
        ·
          refine ⟨293216920959270360995297297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195477947306180240663531531 293216920959270360995297297)
          ·
            refine ⟨219912690719452770746472973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293216920959270360995297297 219912690719452770746472973)
            ·
              refine ⟨82467259019794789029927365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219912690719452770746472973 82467259019794789029927365)
              ·
                refine ⟨15462611066211522943111381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82467259019794789029927365 15462611066211522943111381)
                ·
                  refine ⟨362404946864332568979173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15462611066211522943111381 362404946864332568979173)
                  ·
                    rfl

theorem cell22_3176015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_3176015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176015 prefixEnd_3176015 := by exact prefixLift 3176015
  have htrace : WordTrace (prefixWord ++ tailWord_3176015) baseStart_3176015 baseEnd_3176015 := by
    simpa [prefixWord, tailWord_3176015, baseEnd_3176015] using wordTrace_append hprefix tailTrace_3176015
  have hstable : (prefixWord ++ tailWord_3176015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176015).length < 2 ^ (prefixWord ++ tailWord_3176015).sum := by decide
  have hdescent : baseEnd_3176015 < baseStart_3176015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176036 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_3176036 : Nat := 118140960795 + 3176036 * 2 ^ 59
def prefixEnd_3176036 : Nat := 4983230072969 + 3 ^ 40 * 3176036 * 2
def baseEnd_3176036 : Nat := 1087222029322160652162455

theorem tailTrace_3176036 : CollatzResearch.WordTrace tailWord_3176036 prefixEnd_3176036 1087222029322160652162455 := by
  unfold tailWord_3176036
  simp only [CollatzResearch.WordTrace]
  refine ⟨57919774760885735304673981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77226366347847647072898641 57919774760885735304673981)
  ·
    refine ⟨21719915535332150739252743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57919774760885735304673981 21719915535332150739252743)
    ·
      refine ⟨32579873302998226108879115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21719915535332150739252743 32579873302998226108879115)
      ·
        refine ⟨48869809954497339163318673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32579873302998226108879115 48869809954497339163318673)
        ·
          refine ⟨36652357465873004372489005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48869809954497339163318673 36652357465873004372489005)
          ·
            refine ⟨13744634049702376639683377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36652357465873004372489005 13744634049702376639683377)
            ·
              refine ⟨10308475537276782479762533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13744634049702376639683377 10308475537276782479762533)
              ·
                refine ⟨1932839163239396714955475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10308475537276782479762533 1932839163239396714955475)
                ·
                  refine ⟨2899258744859095072433213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932839163239396714955475 2899258744859095072433213)
                  ·
                    refine ⟨1087222029322160652162455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2899258744859095072433213 1087222029322160652162455)
                    ·
                      rfl

theorem cell22_3176036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_3176036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176036 prefixEnd_3176036 := by exact prefixLift 3176036
  have htrace : WordTrace (prefixWord ++ tailWord_3176036) baseStart_3176036 baseEnd_3176036 := by
    simpa [prefixWord, tailWord_3176036, baseEnd_3176036] using wordTrace_append hprefix tailTrace_3176036
  have hstable : (prefixWord ++ tailWord_3176036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176036).length < 2 ^ (prefixWord ++ tailWord_3176036).sum := by decide
  have hdescent : baseEnd_3176036 < baseStart_3176036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176109 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3176109 : Nat := 118140960795 + 3176109 * 2 ^ 59
def prefixEnd_3176109 : Nat := 4983230072969 + 3 ^ 40 * 3176109 * 2
def baseEnd_3176109 : Nat := 1087247018714012795087231

theorem tailTrace_3176109 : CollatzResearch.WordTrace tailWord_3176109 prefixEnd_3176109 1087247018714012795087231 := by
  unfold tailWord_3176109
  simp only [CollatzResearch.WordTrace]
  refine ⟨115842212050507004076755381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77228141367004669384503587 115842212050507004076755381)
  ·
    refine ⟨10860207379735031632195817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115842212050507004076755381 10860207379735031632195817)
    ·
      refine ⟨8145155534801273724146863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10860207379735031632195817 8145155534801273724146863)
      ·
        refine ⟨12217733302201910586220295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145155534801273724146863 12217733302201910586220295)
        ·
          refine ⟨18326599953302865879330443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12217733302201910586220295 18326599953302865879330443)
          ·
            refine ⟨27489899929954298818995665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18326599953302865879330443 27489899929954298818995665)
            ·
              refine ⟨20617424947465724114246749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27489899929954298818995665 20617424947465724114246749)
              ·
                refine ⟨7731534355299646542842531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20617424947465724114246749 7731534355299646542842531)
                ·
                  refine ⟨11597301532949469814263797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7731534355299646542842531 11597301532949469814263797)
                  ·
                    refine ⟨1087247018714012795087231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11597301532949469814263797 1087247018714012795087231)
                    ·
                      rfl

theorem cell22_3176109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3176109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176109 prefixEnd_3176109 := by exact prefixLift 3176109
  have htrace : WordTrace (prefixWord ++ tailWord_3176109) baseStart_3176109 baseEnd_3176109 := by
    simpa [prefixWord, tailWord_3176109, baseEnd_3176109] using wordTrace_append hprefix tailTrace_3176109
  have hstable : (prefixWord ++ tailWord_3176109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176109).length < 2 ^ (prefixWord ++ tailWord_3176109).sum := by decide
  have hdescent : baseEnd_3176109 < baseStart_3176109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176122 : List Nat := [3, 1, 1, 1, 2, 4, 2, 8]
def baseStart_3176122 : Nat := 118140960795 + 3176122 * 2 ^ 59
def prefixEnd_3176122 : Nat := 4983230072969 + 3 ^ 40 * 3176122 * 2
def baseEnd_3176122 : Nat := 120805718764409454945799

theorem tailTrace_3176122 : CollatzResearch.WordTrace tailWord_3176122 prefixEnd_3176122 120805718764409454945799 := by
  unfold tailWord_3176122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28960671549864976824244655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77228457466306604864652413 28960671549864976824244655)
  ·
    refine ⟨43441007324797465236366983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28960671549864976824244655 43441007324797465236366983)
    ·
      refine ⟨65161510987196197854550475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43441007324797465236366983 65161510987196197854550475)
      ·
        refine ⟨97742266480794296781825713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65161510987196197854550475 97742266480794296781825713)
        ·
          refine ⟨73306699860595722586369285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97742266480794296781825713 73306699860595722586369285)
          ·
            refine ⟨13745006223861697984944241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73306699860595722586369285 13745006223861697984944241)
            ·
              refine ⟨10308754667896273488708181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13745006223861697984944241 10308754667896273488708181)
              ·
                refine ⟨120805718764409454945799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10308754667896273488708181 120805718764409454945799)
                ·
                  rfl

theorem cell22_3176122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_3176122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176122 prefixEnd_3176122 := by exact prefixLift 3176122
  have htrace : WordTrace (prefixWord ++ tailWord_3176122) baseStart_3176122 baseEnd_3176122 := by
    simpa [prefixWord, tailWord_3176122, baseEnd_3176122] using wordTrace_append hprefix tailTrace_3176122
  have hstable : (prefixWord ++ tailWord_3176122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176122).length < 2 ^ (prefixWord ++ tailWord_3176122).sum := by decide
  have hdescent : baseEnd_3176122 < baseStart_3176122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176124 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_3176124 : Nat := 118140960795 + 3176124 * 2 ^ 59
def prefixEnd_3176124 : Nat := 4983230072969 + 3 ^ 40 * 3176124 * 2
def baseEnd_3176124 : Nat := 1087252153520557755962185

theorem tailTrace_3176124 : CollatzResearch.WordTrace tailWord_3176124 prefixEnd_3176124 1087252153520557755962185 := by
  unfold tailWord_3176124
  simp only [CollatzResearch.WordTrace]
  refine ⟨57921379572726330819275713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77228506096968441092367617 57921379572726330819275713)
  ·
    refine ⟨43441034679544748114456785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57921379572726330819275713 43441034679544748114456785)
    ·
      refine ⟨32580776009658561085842589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43441034679544748114456785 32580776009658561085842589)
      ·
        refine ⟨12217791003621960407190971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32580776009658561085842589 12217791003621960407190971)
        ·
          refine ⟨18326686505432940610786457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12217791003621960407190971 18326686505432940610786457)
          ·
            refine ⟨13745014879074705458089843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18326686505432940610786457 13745014879074705458089843)
            ·
              refine ⟨20617522318612058187134765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13745014879074705458089843 20617522318612058187134765)
              ·
                refine ⟨7731570869479521820175537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20617522318612058187134765 7731570869479521820175537)
                ·
                  refine ⟨5798678152109641365131653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7731570869479521820175537 5798678152109641365131653)
                  ·
                    refine ⟨1087252153520557755962185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798678152109641365131653 1087252153520557755962185)
                    ·
                      rfl

theorem cell22_3176124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_3176124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176124 prefixEnd_3176124 := by exact prefixLift 3176124
  have htrace : WordTrace (prefixWord ++ tailWord_3176124) baseStart_3176124 baseEnd_3176124 := by
    simpa [prefixWord, tailWord_3176124, baseEnd_3176124] using wordTrace_append hprefix tailTrace_3176124
  have hstable : (prefixWord ++ tailWord_3176124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176124).length < 2 ^ (prefixWord ++ tailWord_3176124).sum := by decide
  have hdescent : baseEnd_3176124 < baseStart_3176124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176152 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_3176152 : Nat := 118140960795 + 3176152 * 2 ^ 59
def prefixEnd_3176152 : Nat := 4983230072969 + 3 ^ 40 * 3176152 * 2
def baseEnd_3176152 : Nat := 1087261738492775016262099

theorem tailTrace_3176152 : CollatzResearch.WordTrace tailWord_3176152 prefixEnd_3176152 1087261738492775016262099 := by
  unfold tailWord_3176152
  simp only [CollatzResearch.WordTrace]
  refine ⟨57921890194675611210285355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77229186926234148280380473 57921890194675611210285355)
  ·
    refine ⟨86882835292013416815428033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57921890194675611210285355 86882835292013416815428033)
    ·
      refine ⟨65162126469010062611571025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86882835292013416815428033 65162126469010062611571025)
      ·
        refine ⟨48871594851757546958678269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65162126469010062611571025 48871594851757546958678269)
        ·
          refine ⟨18326848069409080109504351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48871594851757546958678269 18326848069409080109504351)
          ·
            refine ⟨27490272104113620164256527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18326848069409080109504351 27490272104113620164256527)
            ·
              refine ⟨41235408156170430246384791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27490272104113620164256527 41235408156170430246384791)
              ·
                refine ⟨61853112234255645369577187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41235408156170430246384791 61853112234255645369577187)
                ·
                  refine ⟨92779668351383468054365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61853112234255645369577187 92779668351383468054365781)
                  ·
                    refine ⟨1087261738492775016262099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92779668351383468054365781 1087261738492775016262099)
                    ·
                      rfl

theorem cell22_3176152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_3176152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176152 prefixEnd_3176152 := by exact prefixLift 3176152
  have htrace : WordTrace (prefixWord ++ tailWord_3176152) baseStart_3176152 baseEnd_3176152 := by
    simpa [prefixWord, tailWord_3176152, baseEnd_3176152] using wordTrace_append hprefix tailTrace_3176152
  have hstable : (prefixWord ++ tailWord_3176152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176152).length < 2 ^ (prefixWord ++ tailWord_3176152).sum := by decide
  have hdescent : baseEnd_3176152 < baseStart_3176152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176188 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_3176188 : Nat := 118140960795 + 3176188 * 2 ^ 59
def prefixEnd_3176188 : Nat := 4983230072969 + 3 ^ 40 * 3176188 * 2
def baseEnd_3176188 : Nat := 1087274062028482922361989

theorem tailTrace_3176188 : CollatzResearch.WordTrace tailWord_3176188 prefixEnd_3176188 1087274062028482922361989 := by
  unfold tailWord_3176188
  simp only [CollatzResearch.WordTrace]
  refine ⟨57922546708610400284440609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77230062278147200379254145 57922546708610400284440609)
  ·
    refine ⟨43441910031457800213330457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57922546708610400284440609 43441910031457800213330457)
    ·
      refine ⟨32581432523593350159997843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43441910031457800213330457 32581432523593350159997843)
      ·
        refine ⟨48872148785390025239996765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32581432523593350159997843 48872148785390025239996765)
        ·
          refine ⟨18327055794521259464998787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48872148785390025239996765 18327055794521259464998787)
          ·
            refine ⟨27490583691781889197498181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18327055794521259464998787 27490583691781889197498181)
            ·
              refine ⟨5154484442209104224530909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27490583691781889197498181 5154484442209104224530909)
              ·
                refine ⟨1932931665828414084199091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5154484442209104224530909 1932931665828414084199091)
                ·
                  refine ⟨2899397498742621126298637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932931665828414084199091 2899397498742621126298637)
                  ·
                    refine ⟨1087274062028482922361989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2899397498742621126298637 1087274062028482922361989)
                    ·
                      rfl

theorem cell22_3176188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_3176188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176188 prefixEnd_3176188 := by exact prefixLift 3176188
  have htrace : WordTrace (prefixWord ++ tailWord_3176188) baseStart_3176188 baseEnd_3176188 := by
    simpa [prefixWord, tailWord_3176188, baseEnd_3176188] using wordTrace_append hprefix tailTrace_3176188
  have hstable : (prefixWord ++ tailWord_3176188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176188).length < 2 ^ (prefixWord ++ tailWord_3176188).sum := by decide
  have hdescent : baseEnd_3176188 < baseStart_3176188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176229 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 6]
def baseStart_3176229 : Nat := 118140960795 + 3176229 * 2 ^ 59
def prefixEnd_3176229 : Nat := 4983230072969 + 3 ^ 40 * 3176229 * 2
def baseEnd_3176229 : Nat := 362429365722124160695621

theorem tailTrace_3176229 : CollatzResearch.WordTrace tailWord_3176229 prefixEnd_3176229 362429365722124160695621 := by
  unfold tailWord_3176229
  simp only [CollatzResearch.WordTrace]
  refine ⟨115846588810072264571123741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77231059206714843047415827 115846588810072264571123741)
  ·
    refine ⟨43442470803777099214171403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115846588810072264571123741 43442470803777099214171403)
    ·
      refine ⟨65163706205665648821257105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43442470803777099214171403 65163706205665648821257105)
      ·
        refine ⟨48872779654249236615942829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65163706205665648821257105 48872779654249236615942829)
        ·
          refine ⟨18327292370343463730978561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48872779654249236615942829 18327292370343463730978561)
          ·
            refine ⟨13745469277757597798233921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18327292370343463730978561 13745469277757597798233921)
            ·
              refine ⟨10309101958318198348675441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13745469277757597798233921 10309101958318198348675441)
              ·
                refine ⟨7731826468738648761506581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10309101958318198348675441 7731826468738648761506581)
                ·
                  refine ⟨362429365722124160695621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7731826468738648761506581 362429365722124160695621)
                  ·
                    rfl

theorem cell22_3176229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_3176229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176229 prefixEnd_3176229 := by exact prefixLift 3176229
  have htrace : WordTrace (prefixWord ++ tailWord_3176229) baseStart_3176229 baseEnd_3176229 := by
    simpa [prefixWord, tailWord_3176229, baseEnd_3176229] using wordTrace_append hprefix tailTrace_3176229
  have hstable : (prefixWord ++ tailWord_3176229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176229).length < 2 ^ (prefixWord ++ tailWord_3176229).sum := by decide
  have hdescent : baseEnd_3176229 < baseStart_3176229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176259 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 4, 4]
def baseStart_3176259 : Nat := 118140960795 + 3176259 * 2 ^ 59
def prefixEnd_3176259 : Nat := 4983230072969 + 3 ^ 40 * 3176259 * 2
def baseEnd_3176259 : Nat := 1087298366779462403836771

theorem tailTrace_3176259 : CollatzResearch.WordTrace tailWord_3176259 prefixEnd_3176259 1087298366779462403836771 := by
  unfold tailWord_3176259
  simp only [CollatzResearch.WordTrace]
  refine ⟨115847682999963579694715831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77231788666642386463143887 115847682999963579694715831)
  ·
    refine ⟨173771524499945369542073747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115847682999963579694715831 173771524499945369542073747)
    ·
      refine ⟨260657286749918054313110621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173771524499945369542073747 260657286749918054313110621)
      ·
        refine ⟨97746482531219270367416483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260657286749918054313110621 97746482531219270367416483)
        ·
          refine ⟨146619723796828905551124725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97746482531219270367416483 146619723796828905551124725)
          ·
            refine ⟨13745599105952709895417943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146619723796828905551124725 13745599105952709895417943)
            ·
              refine ⟨20618398658929064843126915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13745599105952709895417943 20618398658929064843126915)
              ·
                refine ⟨30927597988393597264690373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20618398658929064843126915 30927597988393597264690373)
                ·
                  refine ⟨5798924622823799487129445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30927597988393597264690373 5798924622823799487129445)
                  ·
                    refine ⟨1087298366779462403836771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798924622823799487129445 1087298366779462403836771)
                    ·
                      rfl

theorem cell22_3176259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_3176259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176259 prefixEnd_3176259 := by exact prefixLift 3176259
  have htrace : WordTrace (prefixWord ++ tailWord_3176259) baseStart_3176259 baseEnd_3176259 := by
    simpa [prefixWord, tailWord_3176259, baseEnd_3176259] using wordTrace_append hprefix tailTrace_3176259
  have hstable : (prefixWord ++ tailWord_3176259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176259).length < 2 ^ (prefixWord ++ tailWord_3176259).sum := by decide
  have hdescent : baseEnd_3176259 < baseStart_3176259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176261 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_3176261 : Nat := 118140960795 + 3176261 * 2 ^ 59
def prefixEnd_3176261 : Nat := 4983230072969 + 3 ^ 40 * 3176261 * 2
def baseEnd_3176261 : Nat := 1087299051420335065286765

theorem tailTrace_3176261 : CollatzResearch.WordTrace tailWord_3176261 prefixEnd_3176261 1087299051420335065286765 := by
  unfold tailWord_3176261
  simp only [CollatzResearch.WordTrace]
  refine ⟨115847755945956334036288637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77231837297304222690859091 115847755945956334036288637)
  ·
    refine ⟨43442908479733625263608239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115847755945956334036288637 43442908479733625263608239)
    ·
      refine ⟨65164362719600437895412359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43442908479733625263608239 65164362719600437895412359)
      ·
        refine ⟨97746544079400656843118539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65164362719600437895412359 97746544079400656843118539)
        ·
          refine ⟨146619816119100985264677809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97746544079400656843118539 146619816119100985264677809)
          ·
            refine ⟨109964862089325738948508357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146619816119100985264677809 109964862089325738948508357)
            ·
              refine ⟨20618411641748576052845317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109964862089325738948508357 20618411641748576052845317)
              ·
                refine ⟨3865952182827858009908497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20618411641748576052845317 3865952182827858009908497)
                ·
                  refine ⟨2899464137120893507431373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865952182827858009908497 2899464137120893507431373)
                  ·
                    refine ⟨1087299051420335065286765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2899464137120893507431373 1087299051420335065286765)
                    ·
                      rfl

theorem cell22_3176261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_3176261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176261 prefixEnd_3176261 := by exact prefixLift 3176261
  have htrace : WordTrace (prefixWord ++ tailWord_3176261) baseStart_3176261 baseEnd_3176261 := by
    simpa [prefixWord, tailWord_3176261, baseEnd_3176261] using wordTrace_append hprefix tailTrace_3176261
  have hstable : (prefixWord ++ tailWord_3176261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176261).length < 2 ^ (prefixWord ++ tailWord_3176261).sum := by decide
  have hdescent : baseEnd_3176261 < baseStart_3176261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176274 : List Nat := [3, 2, 2, 1, 1, 3, 1, 9]
def baseStart_3176274 : Nat := 118140960795 + 3176274 * 2 ^ 59
def prefixEnd_3176274 : Nat := 4983230072969 + 3 ^ 40 * 3176274 * 2
def baseEnd_3176274 : Nat := 120811500176223040523525

theorem tailTrace_3176274 : CollatzResearch.WordTrace tailWord_3176274 prefixEnd_3176274 120811500176223040523525 := by
  unfold tailWord_3176274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28962057523727309314127969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77232153396606158171007917 28962057523727309314127969)
  ·
    refine ⟨21721543142795481985595977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28962057523727309314127969 21721543142795481985595977)
    ·
      refine ⟨16291157357096611489196983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21721543142795481985595977 16291157357096611489196983)
      ·
        refine ⟨24436736035644917233795475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16291157357096611489196983 24436736035644917233795475)
        ·
          refine ⟨36655104053467375850693213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24436736035644917233795475 36655104053467375850693213)
          ·
            refine ⟨13745664020050265944009955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36655104053467375850693213 13745664020050265944009955)
            ·
              refine ⟨20618496030075398916014933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13745664020050265944009955 20618496030075398916014933)
              ·
                refine ⟨120811500176223040523525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20618496030075398916014933 120811500176223040523525)
                ·
                  rfl

theorem cell22_3176274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_3176274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176274 prefixEnd_3176274 := by exact prefixLift 3176274
  have htrace : WordTrace (prefixWord ++ tailWord_3176274) baseStart_3176274 baseEnd_3176274 := by
    simpa [prefixWord, tailWord_3176274, baseEnd_3176274] using wordTrace_append hprefix tailTrace_3176274
  have hstable : (prefixWord ++ tailWord_3176274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176274).length < 2 ^ (prefixWord ++ tailWord_3176274).sum := by decide
  have hdescent : baseEnd_3176274 < baseStart_3176274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176342 : List Nat := [5, 3, 1, 1, 2, 1, 3, 6]
def baseStart_3176342 : Nat := 118140960795 + 3176342 * 2 ^ 59
def prefixEnd_3176342 : Nat := 4983230072969 + 3 ^ 40 * 3176342 * 2
def baseEnd_3176342 : Nat := 120814086597297539334613

theorem tailTrace_3176342 : CollatzResearch.WordTrace tailWord_3176342 prefixEnd_3176342 120814086597297539334613 := by
  unfold tailWord_3176342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240669391166430304374205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77233806839108589913324853 7240669391166430304374205)
  ·
    refine ⟨2715251021687411364140327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7240669391166430304374205 2715251021687411364140327)
    ·
      refine ⟨4072876532531117046210491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715251021687411364140327 4072876532531117046210491)
      ·
        refine ⟨6109314798796675569315737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072876532531117046210491 6109314798796675569315737)
        ·
          refine ⟨4581986099097506676986803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6109314798796675569315737 4581986099097506676986803)
          ·
            refine ⟨6872979148646260015480205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581986099097506676986803 6872979148646260015480205)
            ·
              refine ⟨2577367180742347505805077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6872979148646260015480205 2577367180742347505805077)
              ·
                refine ⟨120814086597297539334613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2577367180742347505805077 120814086597297539334613)
                ·
                  rfl

theorem cell22_3176342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_3176342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176342 prefixEnd_3176342 := by exact prefixLift 3176342
  have htrace : WordTrace (prefixWord ++ tailWord_3176342) baseStart_3176342 baseEnd_3176342 := by
    simpa [prefixWord, tailWord_3176342, baseEnd_3176342] using wordTrace_append hprefix tailTrace_3176342
  have hstable : (prefixWord ++ tailWord_3176342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176342).length < 2 ^ (prefixWord ++ tailWord_3176342).sum := by decide
  have hdescent : baseEnd_3176342 < baseStart_3176342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176379 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_3176379 : Nat := 118140960795 + 3176379 * 2 ^ 59
def prefixEnd_3176379 : Nat := 4983230072969 + 3 ^ 40 * 3176379 * 2
def baseEnd_3176379 : Nat := 1087339445231822090836403

theorem tailTrace_3176379 : CollatzResearch.WordTrace tailWord_3176379 prefixEnd_3176379 1087339445231822090836403 := by
  unfold tailWord_3176379
  simp only [CollatzResearch.WordTrace]
  refine ⟨115852059759528840189084191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77234706506352560126056127 115852059759528840189084191)
  ·
    refine ⟨173778089639293260283626287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115852059759528840189084191 173778089639293260283626287)
    ·
      refine ⟨260667134458939890425439431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173778089639293260283626287 260667134458939890425439431)
      ·
        refine ⟨391000701688409835638159147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260667134458939890425439431 391000701688409835638159147)
        ·
          refine ⟨586501052532614753457238721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391000701688409835638159147 586501052532614753457238721)
          ·
            refine ⟨439875789399461065092929041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586501052532614753457238721 439875789399461065092929041)
            ·
              refine ⟨329906842049595798819696781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439875789399461065092929041 329906842049595798819696781)
              ·
                refine ⟨123715065768598424557386293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329906842049595798819696781 123715065768598424557386293)
                ·
                  refine ⟨11598287415806102302254965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123715065768598424557386293 11598287415806102302254965)
                  ·
                    refine ⟨1087339445231822090836403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11598287415806102302254965 1087339445231822090836403)
                    ·
                      rfl

theorem cell22_3176379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_3176379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176379 prefixEnd_3176379 := by exact prefixLift 3176379
  have htrace : WordTrace (prefixWord ++ tailWord_3176379) baseStart_3176379 baseEnd_3176379 := by
    simpa [prefixWord, tailWord_3176379, baseEnd_3176379] using wordTrace_append hprefix tailTrace_3176379
  have hstable : (prefixWord ++ tailWord_3176379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176379).length < 2 ^ (prefixWord ++ tailWord_3176379).sum := by decide
  have hdescent : baseEnd_3176379 < baseStart_3176379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176381 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 6]
def baseStart_3176381 : Nat := 118140960795 + 3176381 * 2 ^ 59
def prefixEnd_3176381 : Nat := 4983230072969 + 3 ^ 40 * 3176381 * 2
def baseEnd_3176381 : Nat := 362446709957564917428799

theorem tailTrace_3176381 : CollatzResearch.WordTrace tailWord_3176381 prefixEnd_3176381 362446709957564917428799 := by
  unfold tailWord_3176381
  simp only [CollatzResearch.WordTrace]
  refine ⟨115852132705521594530656997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77234755137014396353771331 115852132705521594530656997)
  ·
    refine ⟨21722274882285298974498187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115852132705521594530656997 21722274882285298974498187)
    ·
      refine ⟨32583412323427948461747281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21722274882285298974498187 32583412323427948461747281)
      ·
        refine ⟨24437559242570961346310461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32583412323427948461747281 24437559242570961346310461)
        ·
          refine ⟨9164084715964110504866423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24437559242570961346310461 9164084715964110504866423)
          ·
            refine ⟨13746127073946165757299635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164084715964110504866423 13746127073946165757299635)
            ·
              refine ⟨20619190610919248635949453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13746127073946165757299635 20619190610919248635949453)
              ·
                refine ⟨7732196479094718238481045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20619190610919248635949453 7732196479094718238481045)
                ·
                  refine ⟨362446709957564917428799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7732196479094718238481045 362446709957564917428799)
                  ·
                    rfl

theorem cell22_3176381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_3176381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176381 prefixEnd_3176381 := by exact prefixLift 3176381
  have htrace : WordTrace (prefixWord ++ tailWord_3176381) baseStart_3176381 baseEnd_3176381 := by
    simpa [prefixWord, tailWord_3176381, baseEnd_3176381] using wordTrace_append hprefix tailTrace_3176381
  have hstable : (prefixWord ++ tailWord_3176381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176381).length < 2 ^ (prefixWord ++ tailWord_3176381).sum := by decide
  have hdescent : baseEnd_3176381 < baseStart_3176381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176415 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 4]
def baseStart_3176415 : Nat := 118140960795 + 3176415 * 2 ^ 59
def prefixEnd_3176415 : Nat := 4983230072969 + 3 ^ 40 * 3176415 * 2
def baseEnd_3176415 : Nat := 362450589589176665645431

theorem tailTrace_3176415 : CollatzResearch.WordTrace tailWord_3176415 prefixEnd_3176415 362450589589176665645431 := by
  unfold tailWord_3176415
  simp only [CollatzResearch.WordTrace]
  refine ⟨115853372787398418337394699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77235581858265612224929799 115853372787398418337394699)
  ·
    refine ⟨173780059181097627506092049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115853372787398418337394699 173780059181097627506092049)
    ·
      refine ⟨130335044385823220629569037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173780059181097627506092049 130335044385823220629569037)
      ·
        refine ⟨48875641644683707736088389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130335044385823220629569037 48875641644683707736088389)
        ·
          refine ⟨9164182808378195200516573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48875641644683707736088389 9164182808378195200516573)
          ·
            refine ⟨3436568553141823200193715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9164182808378195200516573 3436568553141823200193715)
            ·
              refine ⟨5154852829712734800290573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436568553141823200193715 5154852829712734800290573)
              ·
                refine ⟨1933069811142275550108965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5154852829712734800290573 1933069811142275550108965)
                ·
                  refine ⟨362450589589176665645431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933069811142275550108965 362450589589176665645431)
                  ·
                    rfl

theorem cell22_3176415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 4].length) (baseStart_3176415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176415 prefixEnd_3176415 := by exact prefixLift 3176415
  have htrace : WordTrace (prefixWord ++ tailWord_3176415) baseStart_3176415 baseEnd_3176415 := by
    simpa [prefixWord, tailWord_3176415, baseEnd_3176415] using wordTrace_append hprefix tailTrace_3176415
  have hstable : (prefixWord ++ tailWord_3176415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176415).length < 2 ^ (prefixWord ++ tailWord_3176415).sum := by decide
  have hdescent : baseEnd_3176415 < baseStart_3176415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
